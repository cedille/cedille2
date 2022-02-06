
use std::rc::Rc;
use std::io::prelude::*;
use std::fs::{self, File};
use std::time;
use std::path::{Path, PathBuf};
use std::collections::{HashSet, HashMap};

use colored::Colorize;
use anyhow::{Context, Result, anyhow};
use thiserror::Error;
use normpath::PathExt;

use crate::common::*;
use crate::kernel::core;
use crate::kernel::metavar::MetaState;
use crate::kernel::value::{Environment, LazyValue, Value, ValueEx};
use crate::lang::syntax;
use crate::lang::parser;
use crate::lang::elaborator::{self, ElabError};

#[derive(Debug, Error)]
pub enum DatabaseError {
    #[error("Non unicode path {path:?}")]
    NonUnicodePath { path: PathBuf },
}

#[derive(Debug)]
struct DeclValues {
    type_value: Rc<LazyValue>,
    def_value: Rc<LazyValue>
}

#[derive(Debug)]
struct ImportData {
    public: bool,
    path: Symbol,
    namespace: Option<Symbol>
}

#[derive(Debug)]
struct ModuleData {
    text: String,
    values: HashMap<Symbol, DeclValues>,
    metas: HashMap<Symbol, MetaState>,
    active_metas: HashSet<Symbol>,
    next_meta: usize,
    imports: Vec<ImportData>,
    exports: HashSet<Id>,
    scope: HashSet<Id>,
    last_modified: time::SystemTime,
}

#[derive(Debug)]
pub struct Database {
    modules: HashMap<Symbol, ModuleData>,
    queued: Vec<Symbol>
}

pub fn path_to_module_symbol<P: AsRef<Path>>(prefix: P, path: P) -> Result<Symbol> {
    let path = if cfg!(target_os = "windows") {
        let windows_fix= path.as_ref()
            .to_str()
            .ok_or(DatabaseError::NonUnicodePath { path: path.as_ref().into() })?
            .replace("/", "\\");
        PathBuf::from(windows_fix)
    } else { path.as_ref().into() };
    let mut result: PathBuf = prefix.as_ref().into();
    result.push(path);
    let canonical_path = result.normalize()
        .with_context(|| format!("Failed to normalize path {}", result.display()))?;
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

    pub fn insert_decl(&mut self, module: Symbol, decl: core::Decl) -> Result<(), ElabError> {
        self.freeze_active_metas(module);
        if decl.name == Symbol::from("_") { return Ok(()) }
        let module_data = self.modules.get_mut(&module).unwrap();
        let id = Id::from(decl.name);
        if module_data.scope.contains(&id) || module_data.exports.contains(&id) {
            Err(ElabError::DefinitionCollision)
        } else {
            module_data.scope.insert(id.clone());
            module_data.exports.insert(id);
            let type_value = Rc::new(LazyValue::new(module, Environment::new(), decl.ty.clone()));
            let def_value = Rc::new(LazyValue::new(module, Environment::new(), decl.body.clone()));
            let decl_values = DeclValues { type_value, def_value };
            module_data.values.insert(decl.name, decl_values);
            Ok(())
        }
    }

    fn loaded(&self, module: Symbol) -> bool {
        if let Some(data) = self.modules.get(&module) {
            let mut imports_loaded = true;
            for ImportData { path, .. } in data.imports.iter() {
                imports_loaded = imports_loaded && self.loaded(*path);
            }

            let current_modified = Path::new(module.as_ref())
                .metadata()
                .and_then(|m| m.modified())
                .unwrap_or_else(|_| time::SystemTime::now());
            
            imports_loaded && current_modified <= data.last_modified
        } else { false }
    }

    pub fn load_import(&mut self, module: Symbol, import: &syntax::Import) -> Result<()> {
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

            if module_data.scope.intersection(&import_module_data.exports).count() != 0 {
                Err(anyhow::Error::new(ElabError::DefinitionCollision))
            } else {
                for id in import_module_data.exports.iter() {
                    let mut id = id.clone();
                    if let Some(qual) = import.namespace { id.namespace.insert(0, qual); }
                    module_data.scope.insert(id.clone());
                    if import.public { module_data.exports.insert(id); }
                }
                Ok(())
            }
        };

        self.modules.insert(path, import_module_data);
        result
    }

    pub fn load_module_from_path<P: AsRef<Path>>(&mut self, path: P) -> Result<Symbol> {
        let path = path.as_ref();
        let ext = path.extension().unwrap_or_default();
        if ext.to_string_lossy() != "ced" { return Ok(Symbol::from("")); }
        let sym = path_to_module_symbol(Path::new(""), path)?;
        self.load_module(sym)?;
        Ok(sym)
    }

    fn load_module(&mut self, sym: Symbol) -> Result<()> {
        if self.queued.contains(&sym) {
            Err(anyhow!(format!("Cycle in dependencies of module {}", *sym)))
        } else if self.loaded(sym) {
            log::info!("Skipped {}", *sym);
            Ok(())
        } else {
            let now = time::Instant::now();
            self.queued.push(sym);
            let result = self.load_module_inner(sym);
            self.queued.pop();
            log::info!("\nLoaded {}\nin {}ms", *sym, now.elapsed().as_millis());
            result
        }
    }

    fn load_module_inner(&mut self, sym: Symbol) -> Result<()> {
        let path = Path::new(&*sym);
        let metadata = path.metadata()
            .with_context(|| format!("Failed to extract metadata of path {}", path.display()))?;
        let last_modified = metadata.modified().unwrap_or_else(|_| time::SystemTime::now());
        
        let mut file = File::open(path)
            .with_context(|| format!("Failed to open file with path {}", path.display()))?;
        let mut buffer = Vec::new();
        file.read_to_end(&mut buffer)?;
        let text = String::from_utf8(buffer)?;

        self.modules.insert(sym, ModuleData { 
            text,
            values: HashMap::new(),
            metas: HashMap::new(),
            active_metas: HashSet::new(),
            next_meta: 0,
            imports: Vec::new(),
            exports: HashSet::new(),
            scope: HashSet::new(),
            last_modified
        });

        let tree = parser::parse(self.text(sym))?;
        let ast = parser::module(tree);
        elaborator::elaborate(self, sym, &ast)?;
        Ok(())
    }

    pub fn load_dir(&mut self, path: &Path) -> Result<()> {
        let mut found_error = false;
        for entry in fs::read_dir(path)? {
            let entry = entry?;
            let path = entry.path();
            if path.is_file() {
                if let Err(error) = self.load_module_from_path(path) {
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
        self.modules.get(&module).map(|data| {
            data.imports.iter().find(|ImportData { namespace, .. }| {
                if let Some(namespace) = namespace { component == *namespace }
                else { false }
            })
        }).flatten()
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
        decl.map(|decl| decl.def_value.clone())
    }

    pub fn lookup_type(&self, module: Symbol, id: &Id) -> Option<Rc<LazyValue>> {
        let mut namespace = id.namespace.clone();
        let decl = self.lookup_decl(true, module, &mut namespace, id.name);
        decl.map(|decl| decl.type_value.clone())
    }

    pub fn text(&self, module: Symbol) -> &str {
        &self.modules.get(&module).unwrap().text
    }

    pub fn fresh_meta(&mut self, module: Symbol) -> Symbol {
        let mut module_data = self.modules.get_mut(&module).unwrap();
        let next = module_data.next_meta;
        module_data.next_meta += 1;
        let name = format!("meta/{}", next);
        let name = Symbol::from(name.as_str());
        module_data.metas.insert(name, MetaState::Unsolved);
        name
    }

    pub fn lookup_meta(&self, module: Symbol, name: Symbol) -> MetaState {
        let module_data = self.modules.get(&module).unwrap();
        module_data.metas.get(&name).map(|x| x.clone())
            .expect("Impossible, any created meta must exist.")
    }

    pub fn insert_meta(&mut self, module: Symbol, name: Symbol, value: Rc<Value>) -> Result<()> {
        let module_data = self.modules.get_mut(&module).unwrap();
        match module_data.metas.get_mut(&name) {
            None | Some(MetaState::Frozen) | Some(MetaState::Solved(_)) =>
                return Err(anyhow!("TODO: meta insertion error, replace this with an error variant")),
            | Some(meta @ MetaState::Unsolved) => {
                *meta = MetaState::Solved(value.clone());
            }
        }
        log::info!("\n{}\n{}\n{}", name, "solved to".green(), value.quote(self, 0.into()));
        Ok(())
    }

    fn freeze_active_metas(&mut self, module: Symbol) {
        let module_data = self.modules.get_mut(&module).unwrap();
        for active in module_data.active_metas.drain() {
            let meta = module_data.metas.entry(active)
                .or_insert(MetaState::Frozen);
            match meta {
                MetaState::Unsolved => *meta = MetaState::Frozen,
                _ => { }
            }
        }
    }
}
