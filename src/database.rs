
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
use crate::kernel::core;
use crate::lang::parser;
use crate::lang::syntax;
use crate::lang::elaborator;

#[derive(Debug, Error)]
pub enum DatabaseError {
    #[error("Non unicode path {path:?}")]
    NonUnicodePath { path: PathBuf },
}

#[derive(Debug)]
struct ImmediateExports {
    namespace_args: Vec<(Mode, syntax::Term)>,
    def: HashSet<syntax::Term>
}

#[derive(Debug)]
struct ImportData {
    name: Option<Symbol>,
    args: Vec<(Mode, syntax::Term)>,
}

#[derive(Debug)]
struct DeclValues {
    type_value: Rc<core::Term>,
    definition_value: Rc<core::Term>
}

#[derive(Debug)]
struct ModuleData {
    text: String,
    imports: HashMap<Symbol, ImportData>,
    exports: HashMap<Option<Symbol>, ImmediateExports>,
    values: HashMap<Symbol, DeclValues>,
    params: Vec<syntax::Parameter>,
    last_modified: SystemTime,
}

#[derive(Debug)]
pub struct Database {
    modules: HashMap<Symbol, ModuleData>,
    defs: HashSet<Id>,
}

impl Database {
    pub fn new() -> Database {
        Database { 
            modules: HashMap::new(),
            defs: HashSet::new(),
        }
    }

    pub fn clear(&mut self) {
        self.modules.clear();
        self.defs.clear();
    }

    fn loaded(&self, module: Symbol) -> bool {
        if let Some(data) = self.modules.get(&module) {
            let imports_loaded = data.imports.iter()
                .all(|(i, _)| self.loaded( *i));
            let current_modified = Path::new(module.as_ref())
                .metadata()
                .and_then(|m| m.modified())
                .unwrap_or_else(|_| SystemTime::now());
            imports_loaded && current_modified <= data.last_modified
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
            let imports = self.load_imports(path.parent().unwrap(), import_paths, visited)?;
            /***
             * Construct the statically typed AST
             ***/
            let mut tree = parser::module(tree);
            /***
             * Elaborate and type check the statically typed AST
             ***/
            let kernel = elaborator::elaborate(self, &tree, sym)?;
            /***
             * Extract the modules exports
             ***/
            /* let exports = HashMap::new(); */
            /***
             * Finish loading the module
             ***/
    /*             let data = ModuleData {
                syntax: tree,
                kernel,
                text,
                imports,
                exports,
                normals: HashMap::new(),
                last_modified,
            };
            self.modules.insert(sym, data); */
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
                if let Some(pairs) = self.modules.get(&module) {
                    let pairs = pairs.imports.iter()
                    .map(|(key, data)| (key, data.name))
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

    fn lookup_module_data(&self, module: Symbol, id: &Id) -> Option<&ModuleData> {
        let module = self.trace_qualified_id(module, id);
        module.map(|s| self.modules.get(&s)).flatten()
    }

    pub fn lookup_def(&self, module: Symbol, id: &Id) -> Option<Rc<core::Term>> {
        let module_data = self.lookup_module_data(module, id);
        module_data.map(|data| data.values.get(&id.name))
            .flatten()
            .map(|values| values.definition_value.clone())
    }

    pub fn lookup_type(&self, module: Symbol, id: &Id) -> Option<Rc<core::Term>> {
        let module_data = self.lookup_module_data(module, id);
        module_data.map(|data| data.values.get(&id.name))
            .flatten()
            .map(|values| values.type_value.clone())
    }

    pub fn lookup_module(&self, module: Symbol, id: &Id) -> Option<Symbol> {
        self.trace_qualified_id(module, id)
    }
}
