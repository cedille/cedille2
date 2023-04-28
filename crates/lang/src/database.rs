
use std::any::type_name;
use std::rc::Rc;
use std::sync::Arc;
use std::io::prelude::*;
use std::fs::{self, File};
use std::time;
use std::path::{Path, PathBuf};
use std::collections::{HashSet, HashMap};

use colored::Colorize;
use miette::SourceSpan;
use thiserror::Error;
use normpath::PathExt;
use if_chain::if_chain;

use cedille2_core::utility::*;
use cedille2_core::term;
use cedille2_core::metavar::MetaState;
use cedille2_core::value::{Environment, LazyValue, Value, ValueEx, SpineEntry, Spine};
use cedille2_core::database::{Database, ModuleData, ImportData};
use crate::syntax;
use crate::parser;
use crate::elaborator::{self, Context, ElabError};
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

pub trait DatabaseExt {
    fn resolve_import_symbol(&self, module: Symbol, import: (usize, usize)) -> Result<Symbol, CedilleError>;
    fn load_import(&mut self, module: Symbol, import: &syntax::Import, args: Vec<(Mode, Rc<Value>)>) -> Result<(), CedilleError>;
    fn load_module(&mut self, sym: Symbol) -> Result<(), CedilleError>;
    fn load_module_from_path<P: AsRef<Path>>(&mut self, path: P) -> Result<Symbol, CedilleError>;
    fn load_dir(&mut self, path: &Path) -> Result<(), CedilleError>;
}

impl DatabaseExt for Database {
    fn resolve_import_symbol(&self, module: Symbol, import: (usize, usize)) -> Result<Symbol, CedilleError> {
        let module_data = self.modules.get(&module).unwrap();
        let (start, end) = import;
        let parent_path = Path::new(&**module).parent().unwrap();
        let path = Path::new(&module_data.text[start..end]).with_extension("ced");
        path_to_module_symbol(parent_path, &path)
    }

    fn load_import(&mut self, module: Symbol, import: &syntax::Import, args: Vec<(Mode, Rc<Value>)>) -> Result<(), CedilleError> {
        let path = self.resolve_import_symbol(module, import.path)?;

        self.load_module(path)?;
        let import_module_data = self.modules.remove(&path).unwrap();
        
        let result = {
            let module_data = self.modules.get_mut(&module).unwrap();
            let import_data = ImportData { public: import.public, path, namespace: import.namespace, args };
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

    fn load_module(&mut self, sym: Symbol) -> Result<(), CedilleError> {
        if self.queued.contains(&sym) {
            Err(DatabaseError::Cycle { module: (*sym).clone() }.into())
        } else if self.loaded(sym) {
            log::info!("Skipped {}", *sym);
            Ok(())
        } else {
            let now = time::Instant::now();
            self.queued.push(sym);
            let result = load_module_inner(self, sym);
            self.queued.pop();
            log::info!("\nLoaded {}\nin {}ms", *sym, now.elapsed().as_millis());
            if result.is_err() {
                if let Some(module) = self.modules.get_mut(&sym) { module.flag_error() }
            }
            result
        }
    }

    fn load_module_from_path<P: AsRef<Path>>(&mut self, path: P) -> Result<Symbol, CedilleError> {
        let path = path.as_ref();
        let ext = path.extension().unwrap_or_default();
        if ext.to_string_lossy() != "ced" { return Ok(Symbol::from("")); }
        let sym = path_to_module_symbol(Path::new(""), path)?;
        self.load_module(sym)?;
        Ok(sym)
    }

    fn load_dir(&mut self, path: &Path) -> Result<(), CedilleError> {
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
}


fn load_module_inner(db : &mut Database, sym: Symbol) -> Result<(), CedilleError> {
    let path = Path::new(&*sym);
    let metadata = path.metadata()?;
    let last_modified = metadata.modified().unwrap_or_else(|_| time::SystemTime::now());
    
    let mut file = File::open(path)?;
    let mut buffer = Vec::new();
    file.read_to_end(&mut buffer)?;
    let text = String::from_utf8(buffer)?;

    db.modules.insert(sym, ModuleData { 
        text: Arc::new(text),
        values: HashMap::new(),
        metas: HashMap::new(),
        active_metas: HashSet::new(),
        next_meta: 0,
        imports: Vec::new(),
        exports: HashSet::new(),
        params: Vec::new(),
        scope: HashSet::new(),
        last_modified,
        contains_error: false
    });

    let tree = parser::parse(db.text_ref(sym))?;
    let ast = parser::module(tree);
    elaborator::elaborate(db, sym, &ast)?;
    Ok(())
}