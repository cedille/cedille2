
use std::io::prelude::*;
use std::fs::{self, File};
use std::time::SystemTime;
use std::path::{Path, PathBuf};
use std::collections::{HashSet, HashMap};

use anyhow::{Context, Result, anyhow};
use colored::*;
use thiserror::Error;

use crate::common::*;
use crate::kernel::value::{Environment, LazyValue};
use crate::lang::syntax;
use crate::lang::parser;
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
struct ImportData {
    public: bool,
    path: Symbol,
    namespace: Option<Symbol>
}

#[derive(Debug)]
pub struct Database {
    modules: HashMap<Symbol, ModuleData>,
    imports: HashMap<Symbol, Vec<ImportData>>,
    defs: HashSet<Id>,
}

fn path_to_module_symbol<P: AsRef<Path>>(prefix: P, path: P) -> Result<Symbol> {
    let path = prefix.as_ref().join(path);
    let canonical_path = path.canonicalize()
        .with_context(|| format!("Failed to canonicalize path {}", path.display()))?;
    let key = canonical_path.to_str()
        .ok_or(DatabaseError::NonUnicodePath { path })?;
    Ok(Symbol::from(key))
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
        -> Result<()>
    {
        for path in imports {
            let path = prefix.as_ref().join(path).with_extension("ced");
            self.load_module_with_visited(path, visited.clone())?;
        }
        Ok(())
    }

    fn load_module_with_visited<P: AsRef<Path>>(&mut self
        , path: P
        , mut visited: HashSet<Symbol>)
        -> Result<Symbol>
    {
        let path = path.as_ref();
        let ext = path.extension().unwrap_or_default();
        if ext.to_string_lossy() != "ced" { return Ok(Symbol::from("")); }
        let sym = path_to_module_symbol(Path::new(""), path)?;
        let parent_path = Path::new(sym.as_str()).parent().unwrap();

        if visited.contains(&sym) {
            return Err(anyhow!(format!("Cycle in dependencies of module {}", *sym)));
        }
        visited.insert(sym);

        if self.loaded(sym) {
            println!("{} {}{}", "skipping file".dimmed(), *sym, "...".dimmed());
        } else {
            println!("{} {}{}", "loading file".dimmed(), *sym, "...".dimmed());
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
            let ast = parser::module(tree);
            /***
             * Load the import data so symbols can be resolved when elaborating
             ***/
            let import_data = ast.imports.iter()
                .map(|syntax::Import { public, path, namespace, .. }|
            {
                let (start, end) = *path;
                let path = Path::new(&text[start..end]);
                let path = path.with_extension("ced");
                let path = path_to_module_symbol(parent_path, &path)?;
                Ok(ImportData { public: *public, path, namespace: *namespace })
            }).collect::<Result<Vec<_>>>()?;
            let import_paths = import_data.iter()
                .map(|ImportData { path, .. }| Path::new(path.as_str()));
            self.load_imports(path.parent().unwrap(), import_paths, visited)?;
            self.imports.insert(sym, import_data);
            /***
             * Construct the statically typed AST
             ***/
            /***
             * Elaborate and type check the statically typed AST
             ***/
            let core_module = elaborator::elaborate(&text, self, &ast, sym)?;
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

    fn reverse_lookup_namespace(&self, module: Symbol, component: Symbol) -> Option<&ImportData> {
        self.imports.get(&module).map(|data| {
            data.iter().find(|ImportData { namespace, .. }| {
                if let Some(namespace) = namespace { component == *namespace }
                else { false }
            })
        }).flatten()
    }

    fn lookup_decl(&self, original: bool, module: Symbol, namespace: &mut Vec<Symbol>, name: Symbol) -> Option<&DeclValues> {
        let mut result = None;
        if let Some(component) = namespace.get(0) {
            if let Some(import_data) = self.reverse_lookup_namespace(module, *component) {
                namespace.pop();
                if original || import_data.public {
                    result = result
                        .or_else(|| self.lookup_decl(false, import_data.path, namespace, name));
                }
            }
        }
        if let Some(module_data) = self.modules.get(&module) {
            result = result.or_else(|| module_data.values.get(&name));
        }
        if let Some(imports) = self.imports.get(&module) {
            for ImportData { public, path, namespace:qual } in imports.iter() {
                if (original || *public) && qual.is_none() {
                    result = result
                        .or_else(|| self.lookup_decl(false, *path, namespace, name));
                }
            }
        }
        result
    }

    pub fn lookup_def(&self, module: Symbol, id: &Id) -> Option<LazyValue> {
        let mut namespace = id.namespace.clone();
        let decl = self.lookup_decl(true, module, &mut namespace, id.name);
        decl.map(|decl| decl.def_value.clone())
    }

    pub fn lookup_type(&self, module: Symbol, id: &Id) -> Option<LazyValue> {
        let mut namespace = id.namespace.clone();
        let decl = self.lookup_decl(true, module, &mut namespace, id.name);
        decl.map(|decl| decl.type_value.clone())
    }
}
