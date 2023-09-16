
use std::any::type_name;
use std::rc::Rc;
use std::sync::Arc;
use std::io::prelude::*;
use std::fs::{self, File};
use std::time;
use std::path::{Path, PathBuf};
use std::collections::{HashSet, HashMap};

use colored::Colorize;
use thiserror::Error;
use if_chain::if_chain;

use crate::utility::*;
use crate::term;
use crate::metavar::MetaState;
use crate::value::{Environment, LazyValue, Value, ValueEx, SpineEntry, Spine};

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

#[derive(Debug, Clone)]
pub struct DeclValues {
    pub type_value: Rc<LazyValue>,
    pub def_value: Option<Rc<LazyValue>>
}

impl DeclValues {
    fn apply(self, db: &Database, args: &[(Mode, Rc<Value>)]) -> DeclValues {
        let DeclValues { mut type_value, mut def_value } = self;
        for (mode, arg) in args {
            let arg = LazyValue::computed(arg.clone());
            let entry = SpineEntry::new(*mode, arg);
            type_value = type_value.apply(db, entry.clone());
            def_value = def_value.map(|x| x.apply(db, entry));
        }
        DeclValues { type_value, def_value }
    }
}

#[derive(Debug)]
pub struct ImportData {
    pub public: bool,
    pub path: Symbol,
    pub namespace: Option<Symbol>,
    pub args: Vec<(Mode, Rc<Value>)>
}

#[derive(Debug)]
pub struct ModuleData {
    pub text: Arc<String>,
    pub values: HashMap<Symbol, DeclValues>,
    pub metas: HashMap<Symbol, MetaState>,
    pub active_metas: HashSet<Symbol>,
    pub next_meta: usize,
    // holes: HashMap<Symbol, H>,
    // next_hole: usize,
    pub imports: Vec<ImportData>,
    pub exports: HashSet<Id>,
    pub params: Vec<term::Parameter>,
    pub scope: HashSet<Id>,
    pub last_modified: time::SystemTime,
    pub contains_error: bool
}

impl ModuleData {
    pub fn flag_error(&mut self) {
        self.contains_error = true;
    }
}


#[derive(Debug)]
pub struct Database {
    pub modules: HashMap<Symbol, ModuleData>,
    pub queued: Vec<Symbol>
}

impl Database {
    pub fn new() -> Database {
        Database { 
            modules: HashMap::new(),
            queued: Vec::new()
        }
    }

    pub fn insert_decl(&mut self, module: Symbol, opaque: bool, decl: term::Decl) -> Result<(), ()> {
        self.freeze_active_metas(module);
        if decl.name == Symbol::from("_") { return Ok(()) }
        let module_data = self.modules.get_mut(&module).unwrap();
        let id = Id::from(decl.name);
        if module_data.scope.contains(&id) || module_data.exports.contains(&id) {
            Err(())
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

    pub fn loaded(&self, module: Symbol) -> bool {
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

    fn reverse_lookup_namespace(&self, module: Symbol, component: Symbol) -> Option<&ImportData> {
        self.modules.get(&module).and_then(|data| {
            data.imports.iter().find(|ImportData { namespace, .. }| {
                if let Some(namespace) = namespace { component == *namespace }
                else { false }
            })
        })
    }

    fn lookup_decl(&self, original: bool, module: Symbol, namespace: &mut Vec<Symbol>, name: Symbol) -> Option<DeclValues> {
        let mut result = None;
        // We have a namespace, so we should find the declaration in an imported module
        if_chain! {
            if let Some(component) = namespace.get(0);
            if let Some(import_data) = self.reverse_lookup_namespace(module, *component);
            if original || import_data.public;
            then {
                namespace.remove(0);
                result = self.lookup_decl(false, import_data.path, namespace, name);
                result = result.map(|x| x.apply(self, &import_data.args));
            }
        }
        // There is no namespace, so check the current module first
        if_chain! {
            if result.is_none();
            if namespace.is_empty();
            if let Some(module_data) = self.modules.get(&module);
            then {
                result = module_data.values.get(&name).cloned();
                // If we are pulling the definition from the same module, then we know that parameters are in context,
                // so we should apply variables with levels corresponding to the implied context
                if original {
                    let params: Vec<_> = module_data.params.iter()
                        .enumerate()
                        .map(|(level, p)| {
                            let sort = p.body.sort().demote();
                            (p.mode, Value::variable(sort, level))
                        }).collect();
                    result = result.map(|x| x.apply(self, &params));
                }
            }
        }
        // There is no namespace, but the definition does not exist in the current module, search the public exports
        // of the current modules imports
        if_chain! {
            if result.is_none();
            if let Some(module_data) = self.modules.get(&module);
            then {
                for ImportData { public, path, namespace:qual, args } in module_data.imports.iter() {
                    if (original || *public) && qual.is_none() {
                        result = result.or_else(|| {
                            let result = self.lookup_decl(false, *path, namespace, name);
                            result.map(|x| x.apply(self, args))
                        });
                    }
                }
            }
        }
        result
    }

    pub fn lookup_def(&self, module: Symbol, id: &Id) -> Option<Rc<LazyValue>> {
        let mut namespace = id.namespace.clone();
        let decl = self.lookup_decl(true, module, &mut namespace, id.name);
        decl.and_then(|decl| decl.def_value)
    }

    pub fn lookup_type(&self, module: Symbol, id: &Id) -> Option<Rc<LazyValue>> {
        let mut namespace = id.namespace.clone();
        let decl = self.lookup_decl(true, module, &mut namespace, id.name);
        decl.map(|decl| decl.type_value)
    }

    pub fn set_params(&mut self, module: Symbol, params: Vec<term::Parameter>) {
        if let Some(module_data) = self.modules.get_mut(&module) {
            module_data.params = params
        }
    }

    pub fn lookup_params(&self, module: Symbol) -> Vec<term::Parameter> {
        self.modules.get(&module)
            .map(|data| &data.params)
            .cloned()
            .unwrap_or_default()
    }

    pub fn text(&self, module: Symbol) -> Arc<String> {
        self.modules.get(&module).unwrap().text.clone()
    }

    pub fn text_ref(&self, module: Symbol) -> &str {
        self.modules.get(&module).unwrap().text.as_ref()
    }

    // pub fn fresh_hole(&mut self, module: Symbol, data: HoleData) -> Symbol {
    //     let mut module_data = self.modules.get_mut(&module).unwrap();
    //     let next = module_data.next_hole;
    //     module_data.next_hole += 1;
    //     let name = format!("hole/{}", next);
    //     let name = Symbol::from(name.as_str());
    //     module_data.holes.insert(name, data);
    //     name
    // }

    // fn lookup_hole(&self, module: Symbol, name: Symbol) -> Option<Rc<Value>> {
    //     let module_data = self.modules.get(&module).unwrap();
    //     module_data.holes.get(&name).map(|data| data.expected_type.clone())
    // }

    // pub fn holes_to_errors(&self, module: Symbol) -> CedilleError {
    //     let mut result = vec![];
    //     let module_data = self.modules.get(&module).unwrap();
    //     for (_, data) in module_data.holes.iter() {
    //         let error = ElabError::Hole {
    //             src: module_data.text.clone(),
    //             span: data.span.clone(),
    //             expected_type: data.expected_type
    //                 .quote(self, data.context.clone().env_lvl())
    //                 .to_string_with_context(data.context.names.clone()),
    //             context: data.context.to_string(self)
    //         };
    //         result.push(error.into());
    //     }
    //     CedilleError::Collection(result)
    // }

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
