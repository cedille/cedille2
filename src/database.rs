
use std::rc::Rc;
use std::sync::Arc;
use std::io::prelude::*;
use std::fs::{self, File};
use std::time;
use std::path::{Path, PathBuf};
use std::collections::{HashSet, HashMap};

use colored::Colorize;
use thiserror::Error;
use normpath::PathExt;

use crate::common::*;
use crate::kernel::core;
use crate::kernel::metavar::MetaState;
use crate::kernel::value::{Environment, LazyValue, Value, ValueEx};
use crate::lang::syntax;
use crate::lang::parser;
use crate::lang::elaborator;
use crate::error::CedilleError;

#[derive(Debug, Error)]
pub enum DatabaseError {
    #[error("Non unicode path {path:?}")]
    NonUnicodePath { path: PathBuf },
    #[error("Cycle in {module}")]
    Cycle { module: String },
    #[error("The module {current_module} has conflicting definitions with the import {imported_module} which are: {collisions}")]
    ImportCollision {
        current_module: String,
        imported_module: String,
        collisions: String
    },
    #[error("The name {id} already exists in the module {current_module}")]
    DeclCollision {
        current_module: String,
        id: String
    }
}

#[derive(Debug)]
struct DeclValues {
    type_value: Rc<LazyValue>,
    def_value: Option<Rc<LazyValue>>
}

#[derive(Debug)]
struct ImportData {
    public: bool,
    path: Symbol,
    namespace: Option<Symbol>
}

#[derive(Debug)]
struct ModuleData {
    text: Arc<String>,
    values: HashMap<Symbol, DeclValues>,
    metas: HashMap<Symbol, MetaState>,
    active_metas: HashSet<Symbol>,
    next_meta: usize,
    imports: Vec<ImportData>,
    exports: HashSet<Id>,
    scope: HashSet<Id>,
    last_modified: time::SystemTime,
    contains_error: bool
}

impl ModuleData {
    fn flag_error(&mut self) {
        self.contains_error = true;
    }
}


#[derive(Debug)]
pub struct Database {
    modules: HashMap<Symbol, ModuleData>,
    queued: Vec<Symbol>
}

pub fn path_to_module_symbol<P: AsRef<Path>>(prefix: P, path: P) -> Result<Symbol, CedilleError> {
    let path = if cfg!(target_os = "windows") {
        let windows_fix= path.as_ref()
            .to_str()
            .ok_or(DatabaseError::NonUnicodePath { path: path.as_ref().into() })?
            .replace('/', "\\");
        PathBuf::from(windows_fix)
    } else { path.as_ref().into() };
    let mut result: PathBuf = prefix.as_ref().into();
    result.push(path);
    let canonical_path = result.normalize()?;
    let key = canonical_path.as_path().to_str()
        .ok_or(DatabaseError::NonUnicodePath { path: result })?;
    Ok(Symbol::from(key))
}

impl Database {
    pub fn new() -> Database {
        Database { 
            modules: HashMap::new(),
            queued: Vec::new()
        }
    }

    pub fn insert_decl(&mut self, module: Symbol, opaque: bool, decl: core::Decl) -> Result<(), CedilleError> {
        self.freeze_active_metas(module);
        if decl.name == Symbol::from("_") { return Ok(()) }
        let module_data = self.modules.get_mut(&module).unwrap();
        let id = Id::from(decl.name);
        if module_data.scope.contains(&id) || module_data.exports.contains(&id) {
            Err(DatabaseError::DeclCollision {
                current_module: module.to_string(),
                id: id.to_string()
            }.into())
        } else {
            module_data.scope.insert(id.clone());
            module_data.exports.insert(id);
            let type_value = Rc::new(LazyValue::new(module, Environment::new(), decl.ty.clone()));
            let def_value = if opaque { None } 
                else { Some(Rc::new(LazyValue::new(module, Environment::new(), decl.body.clone()))) };
            let decl_values = DeclValues { type_value, def_value };
            module_data.values.insert(decl.name, decl_values);
            Ok(())
        }
    }

    fn loaded(&self, module: Symbol) -> bool {
        if let Some(data) = self.modules.get(&module) {
            if data.contains_error { false }
            else {
                let mut imports_loaded = true;
                for ImportData { path, .. } in data.imports.iter() {
                    imports_loaded = imports_loaded && self.loaded(*path);
                }

                let current_modified = Path::new(module.as_ref())
                    .metadata()
                    .and_then(|m| m.modified())
                    .unwrap_or_else(|_| time::SystemTime::now());
                
                imports_loaded && current_modified <= data.last_modified
            }
        } else { false }
    }

    pub fn load_import(&mut self, module: Symbol, import: &syntax::Import) -> Result<(), CedilleError> {
        let path = {
            let module_data = self.modules.get(&module).unwrap();
            let (start, end) = import.path;
            let parent_path = Path::new(&**module).parent().unwrap();
            let path = Path::new(&module_data.text[start..end]).with_extension("ced");
            path_to_module_symbol(parent_path, &path)?
        };

        self.load_module(path)?;
        let import_module_data = self.modules.remove(&path).unwrap();
        
        let result = {
            let module_data = self.modules.get_mut(&module).unwrap();
            let import_data = ImportData { public: import.public, path, namespace: import.namespace };
            module_data.imports.push(import_data);

            let exports = if let Some(namespace) = import.namespace {
                import_module_data.exports.iter().map(|id| id.add_qualifier(namespace)).collect()
            } else {
                import_module_data.exports.clone()
            };

            let intersection = module_data.scope
                .intersection(&exports)
                .map(|id| id.to_string())
                .collect::<Vec<_>>();
            if !intersection.is_empty() {
                let collisions = intersection.join(", ");
                Err(DatabaseError::ImportCollision {
                    current_module: module.to_string(),
                    imported_module: path.to_string(),
                    collisions
                })
            } else {
                for id in exports.iter() {
                    module_data.scope.insert(id.clone());
                    if import.public { module_data.exports.insert(id.clone()); }
                }
                Ok(())
            }
        };

        self.modules.insert(path, import_module_data);
        result.map_err(|e| e.into())
    }

    pub fn load_module_from_path<P: AsRef<Path>>(&mut self, path: P) -> Result<Symbol, CedilleError> {
        let path = path.as_ref();
        let ext = path.extension().unwrap_or_default();
        if ext.to_string_lossy() != "ced" { return Ok(Symbol::from("")); }
        let sym = path_to_module_symbol(Path::new(""), path)?;
        self.load_module(sym)?;
        Ok(sym)
    }

    fn load_module(&mut self, sym: Symbol) -> Result<(), CedilleError> {
        if self.queued.contains(&sym) {
            Err(DatabaseError::Cycle { module: (*sym).clone() }.into())
        } else if self.loaded(sym) {
            log::info!("Skipped {}", *sym);
            Ok(())
        } else {
            let now = time::Instant::now();
            self.queued.push(sym);
            let result = self.load_module_inner(sym);
            self.queued.pop();
            log::info!("\nLoaded {}\nin {}ms", *sym, now.elapsed().as_millis());
            if result.is_err() {
                if let Some(module) = self.modules.get_mut(&sym) { module.flag_error() }
            }
            result
        }
    }

    fn load_module_inner(&mut self, sym: Symbol) -> Result<(), CedilleError> {
        let path = Path::new(&*sym);
        let metadata = path.metadata()?;
        let last_modified = metadata.modified().unwrap_or_else(|_| time::SystemTime::now());
        
        let mut file = File::open(path)?;
        let mut buffer = Vec::new();
        file.read_to_end(&mut buffer)?;
        let text = String::from_utf8(buffer)?;

        self.modules.insert(sym, ModuleData { 
            text: Arc::new(text),
            values: HashMap::new(),
            metas: HashMap::new(),
            active_metas: HashSet::new(),
            next_meta: 0,
            imports: Vec::new(),
            exports: HashSet::new(),
            scope: HashSet::new(),
            last_modified,
            contains_error: false
        });

        let tree = parser::parse(self.text_ref(sym))?;
        let ast = parser::module(tree);
        elaborator::elaborate(self, sym, &ast)?;
        Ok(())
    }

    pub fn load_dir(&mut self, path: &Path) -> Result<(), CedilleError> {
        for entry in fs::read_dir(path)? {
            let entry = entry?;
            let path = entry.path();
            if path.is_file() {
                self.load_module_from_path(path)?;
            } else {
                self.load_dir(&path)?;
            }
        }
        Ok(())
    }

    fn reverse_lookup_namespace(&self, module: Symbol, component: Symbol) -> Option<&ImportData> {
        self.modules.get(&module).and_then(|data| {
            data.imports.iter().find(|ImportData { namespace, .. }| {
                if let Some(namespace) = namespace { component == *namespace }
                else { false }
            })
        })
    }

    fn lookup_decl(&self, original: bool, module: Symbol, namespace: &mut Vec<Symbol>, name: Symbol) -> Option<&DeclValues> {
        let mut result = None;
        if_chain! {
            if let Some(component) = namespace.get(0);
            if let Some(import_data) = self.reverse_lookup_namespace(module, *component);
            if original || import_data.public;
            then {
                namespace.remove(0);
                result = self.lookup_decl(false, import_data.path, namespace, name);
            }
        }
        if_chain! {
            if result.is_none();
            if namespace.is_empty();
            if let Some(module_data) = self.modules.get(&module);
            then { result = module_data.values.get(&name); }
        }
        if_chain! {
            if result.is_none();
            if let Some(module_data) = self.modules.get(&module);
            then {
                for ImportData { public, path, namespace:qual } in module_data.imports.iter() {
                    if (original || *public) && qual.is_none() {
                        result = result.or_else(|| self.lookup_decl(false, *path, namespace, name));
                    }
                }
            }
        }
        result
    }

    pub fn lookup_def(&self, module: Symbol, id: &Id) -> Option<Rc<LazyValue>> {
        let mut namespace = id.namespace.clone();
        let decl = self.lookup_decl(true, module, &mut namespace, id.name);
        decl.and_then(|decl| decl.def_value.clone())
    }

    pub fn lookup_type(&self, module: Symbol, id: &Id) -> Option<Rc<LazyValue>> {
        let mut namespace = id.namespace.clone();
        let decl = self.lookup_decl(true, module, &mut namespace, id.name);
        decl.map(|decl| decl.type_value.clone())
    }

    pub fn text(&self, module: Symbol) -> Arc<String> {
        self.modules.get(&module).unwrap().text.clone()
    }

    pub fn text_ref(&self, module: Symbol) -> &str {
        self.modules.get(&module).unwrap().text.as_ref()
    }

    pub fn fresh_meta(&mut self, module: Symbol) -> Symbol {
        let mut module_data = self.modules.get_mut(&module).unwrap();
        let next = module_data.next_meta;
        module_data.next_meta += 1;
        let name = format!("meta/{}", next);
        let name = Symbol::from(name.as_str());
        module_data.metas.insert(name, MetaState::Unsolved);
        module_data.active_metas.insert(name);
        name
    }

    pub fn lookup_meta(&self, module: Symbol, name: Symbol) -> MetaState {
        let module_data = self.modules.get(&module).unwrap();
        module_data.metas.get(&name).cloned()
            .expect("Impossible, any created meta must exist.")
    }

    pub fn insert_meta(&mut self, module: Symbol, name: Symbol, value: Rc<Value>) -> Result<(), ()> {
        let module_data = self.modules.get_mut(&module).unwrap();
        match module_data.metas.get_mut(&name) {
            None | Some(MetaState::Frozen) | Some(MetaState::Solved(_)) => panic!("TODO FIX"),
            | Some(meta @ MetaState::Unsolved) => {
                *meta = MetaState::Solved(value.clone());
            }
        }
        log::info!("\n{}\n{}\n{}", name, "solved to".green(), value.quote(self, 0.into()));
        Ok(())
    }

    pub fn get_metas(&self, module: Symbol) -> Option<&HashMap<Symbol, MetaState>> {
        self.modules.get(&module).map(|m| &m.metas)
    }

    fn freeze_active_metas(&mut self, module: Symbol) {
        let module_data = self.modules.get_mut(&module).unwrap();
        for active in module_data.active_metas.drain() {
            let meta = module_data.metas.entry(active)
                .or_insert(MetaState::Frozen);
            if let MetaState::Unsolved = meta {
                log::info!("{} is {}", active, "frozen".bright_blue());
                *meta = MetaState::Frozen
            }
        }
    }
}
