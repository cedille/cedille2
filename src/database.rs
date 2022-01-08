
use std::rc::Rc;
use std::io::prelude::*;
use std::fs::{self, File};
use std::time::SystemTime;
use std::path::{Path, PathBuf};
use std::collections::{HashSet, HashMap};

use anyhow::{Context, Result, anyhow};
use colored::*;
use thiserror::Error;

use crate::common::{Id, Mode, Symbol};
use crate::kernel::value::{Environment, LazyValue};
use crate::lang::parser;
use crate::lang::syntax;
use crate::lang::elaborator;

#[derive(Debug, Error)]
pub enum DatabaseError {
    #[error("Non unicode path {path:?}")]
    NonUnicodePath { path: PathBuf },
}

#[derive(Debug)]
struct DeclValues {
    type_value: LazyValue,
    def_value: LazyValue
}

#[derive(Debug)]
struct ModuleData {
    text: String,
    values: HashMap<Symbol, DeclValues>,
    last_modified: SystemTime,
}

#[derive(Debug)]
struct ModuleImports {
    imports: HashMap<Symbol, Option<Symbol>>
}

#[derive(Debug)]
pub struct Database {
    modules: HashMap<Symbol, ModuleData>,
    imports: HashMap<Symbol, ModuleImports>,
    defs: HashSet<Id>,
}

impl Database {
    pub fn new() -> Database {
        Database { 
            modules: HashMap::new(),
            imports: HashMap::new(),
            defs: HashSet::new(),
        }
    }

    pub fn clear(&mut self) {
        self.modules.clear();
        self.defs.clear();
    }

    fn loaded(&self, module: Symbol) -> bool {
        if let Some(data) = self.modules.get(&module) {
            let current_modified = Path::new(module.as_ref())
                .metadata()
                .and_then(|m| m.modified())
                .unwrap_or_else(|_| SystemTime::now());
            current_modified <= data.last_modified
        } else { false }
    }

    fn load_imports<P: AsRef<Path>>(&mut self
        , prefix: P
        , imports: impl Iterator<Item=P>
        , visited: HashSet<Symbol>)
        -> Result<Vec<Symbol>>
    {
        let mut result = vec![];
        for path in imports {
            let path = prefix.as_ref().join(path).with_extension("ced");
            let sym = self.load_module_with_visited(path, visited.clone())?;
            result.push(sym);
        }
        Ok(result)
    }

    fn load_module_with_visited<P: AsRef<Path>>(&mut self
        , path: P
        , mut visited: HashSet<Symbol>)
        -> Result<Symbol>
    {
        let path = path.as_ref();
        let ext = path.extension().unwrap_or_default();
        if ext.to_string_lossy() != "ced" { return Ok(Symbol::from("")); }

        let canonical_path = path.canonicalize()
            .with_context(|| format!("Failed to canonicalize path {}", path.display()))?;
        let key = canonical_path.to_str()
            .ok_or(DatabaseError::NonUnicodePath { path:path.to_path_buf() })?;
        let sym = Symbol::from(key);

        if visited.contains(&sym) {
            return Err(anyhow!(format!("Cycle in dependencies of module {}", key)));
        }
        visited.insert(sym);

        if self.loaded(sym) {
            println!("{} {}{}", "skipping file".dimmed(), key, "...".dimmed());
        } else {
            println!("{} {}{}", "loading file".dimmed(), key, "...".dimmed());
            /***
             * Parse the file to the dynamically typed AST
             ***/
            let metadata = path.metadata()
                .with_context(|| format!("Failed to extract metadata of path {}", path.display()))?;
            let last_modified = metadata.modified().unwrap_or_else(|_| SystemTime::now());
            let mut file = File::open(path)
                .with_context(|| format!("Failed to open file with path {}", path.display()))?;
            let mut buffer = Vec::new();
            file.read_to_end(&mut buffer)?;
            let text = String::from_utf8(buffer)?;
            let tree = parser::parse(&text)?;
            /***
             * Recurse through the files imports and load them first
             ***/
            let import_paths = parser::extract_imports(tree.clone()).into_iter()
                .map(|(start, end)| Path::new(&text[start..end]));
            let import_names = self.load_imports(path.parent().unwrap(), import_paths, visited)?;
            let mut imports = HashMap::new();
            for name in import_names.into_iter() {
                imports.insert(name, None);
            }
            self.imports.insert(sym, ModuleImports { imports });
            /***
             * Construct the statically typed AST
             ***/
            let tree = parser::module(tree);
            /***
             * Elaborate and type check the statically typed AST
             ***/
            let core_module = elaborator::elaborate(&text, self, &tree, sym)?;
            /***
             * Extract the modules exports
             ***/
            let mut values = HashMap::new();
            for decl in core_module.decls.iter() {
                let type_value = LazyValue::new(Environment::new(), decl.ty.clone());
                let def_value = LazyValue::new(Environment::new(), decl.body.clone());
                let decl_data = DeclValues { type_value, def_value };
                values.insert(decl.name, decl_data);
            }
            /***
             * Finish loading the module
             ***/
            let data = ModuleData {
                text,
                values,
                last_modified,
            };
            self.modules.insert(sym, data);
        }
        Ok(sym)
    }

    pub fn load_module<P: AsRef<Path>>(&mut self, path: P) -> Result<()> {
        self.load_module_with_visited(path, HashSet::new()).map(|_| ())
    }

    pub fn load_dir(&mut self, path: &Path) -> Result<()> {
        let mut found_error = false;
        for entry in fs::read_dir(path)? {
            let entry = entry?;
            let path = entry.path();
            if path.is_file() {
                if let Err(error) = self.load_module(path) {
                    found_error = true;
                    println!("{}", error);
                }
            } else {
                self.load_dir(&path)?;
            }
        }
        if !found_error { Ok(()) }
        else { Err(anyhow!("Error loading directory.")) }
    }

    fn trace_qualified_id(&self, module: Symbol, id: &Id) -> Option<Symbol> {
        let mut module = Some(module);
        let get_next_module = |module, namespace_component| {
            if let Some(module) = module {
                if let Some(pairs) = self.imports.get(&module) {
                    let pairs = pairs.imports.iter()
                    .map(|(key, name)| (key, name))
                    .collect::<Vec<_>>();
                    let next_module = pairs.iter().find_map(|(_, name)| match name {
                        | Some(n) => if *n == namespace_component { Some(n) } else { None },
                        | None => None
                    });
                    next_module.copied()
                } else { None }
            } else { None }
        };
        for component in id.namespace.iter() {
            module = get_next_module(module, *component);
        }
        module
    }

    /// Lookup the definition of a declaration in its unqualified imports
    /// without chasing the namespace even if one is present
    fn lookup_decl_immediate(&self, module: Symbol, id: &Id) -> Option<&DeclValues> {
        let module_imports = self.imports.get(&module);
        module_imports.map(|data| {
            let mut result = self.modules.get(&module)
                .map(|data| data.values.get(&id.name))
                .flatten();
            for (import_module, import_name) in data.imports.iter() {
                if import_name.is_none() {
                    result = result.or_else(|| self.lookup_decl_immediate(*import_module, id));
                }
            }
            result
        }).flatten()
    }

    fn lookup_decl(&self, module: Symbol, id: &Id) -> Option<&DeclValues> {
        let root_module = self.trace_qualified_id(module, id);
        root_module.map(|module| self.lookup_decl_immediate(module, id))
            .flatten()
    }

    pub fn lookup_def(&self, module: Symbol, id: &Id) -> Option<LazyValue> {
        let decl = self.lookup_decl(module, id);
        decl.map(|decl| decl.def_value.clone())
    }

    pub fn lookup_type(&self, module: Symbol, id: &Id) -> Option<LazyValue> {
        let decl = self.lookup_decl(module, id);
        decl.map(|decl| decl.type_value.clone())
    }
}
