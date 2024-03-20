
use std::cell::RefCell;
use std::sync::Arc;
use std::time;
use std::path::{Path, PathBuf};
use std::collections::{HashSet, HashMap};

use imbl::Vector;
use if_chain::if_chain;

use crate::hc::*;
use crate::utility::*;
use crate::term::*;
use crate::metavar::MetaState;
use crate::value::*;
use crate::eval::*;
//use crate::value::{Environment, LazyValue, Value, ValueEx, SpineEntry, Spine};

#[derive(Debug)]
pub enum DatabaseError {
    NonUnicodePath { path: PathBuf },
    Cycle { module: String },
    ImportCollision {
        current_module: String,
        imported_module: String,
        collisions: String
    },
    DeclCollision {
        current_module: String,
        id: String
    }
}

#[derive(Debug, Clone)]
pub struct DeclData {
    pub ann: Term,
    pub inner_ann: Term,
    pub body: Option<Term>
}

impl DeclData {
    fn apply(self, db: &Database, args: &[(Mode, LazyValue)]) -> DeclData {
        self
        // let DeclValues { mut type_value, mut def_value } = self;
        // for (mode, arg) in args {
        //     let action = Action::Apply(*mode, arg.clone());
        //     type_value = type_value.perform(action);
        //     def_value = def_value.map(|x| x.apply(db, entry));
        // }
        // DeclValues { type_value, def_value }
    }
}

#[derive(Debug)]
pub struct ImportData {
    pub public: bool,
    pub path: Symbol,
    pub namespace: Option<Symbol>,
    pub args: Vec<(Mode, LazyValue)>
}

#[derive(Debug)]
pub struct ModuleData {
    pub text: Arc<String>,
    pub decls: HashMap<Symbol, DeclData>,
    pub metas: HashMap<Symbol, MetaState>,
    pub active_metas: HashSet<Symbol>,
    pub next_meta: usize,
    // holes: HashMap<Symbol, H>,
    // next_hole: usize,
    pub imports: Vec<ImportData>,
    pub exports: HashSet<Id>,
    pub params: Vec<Parameter>,
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
    pub term_data: RefCell<HcFactory<TermData>>,
    pub value_data : RefCell<HcFactory<LazyValueData>>,
    pub modules: HashMap<Symbol, ModuleData>,
    pub queued: Vec<Symbol>
}

impl Default for Database {
    fn default() -> Self {
        Self::new()
    }
}

impl Database {
    pub fn new() -> Database {
        Database { 
            term_data: RefCell::new(HcFactory::with_capacity(128)),
            value_data: RefCell::new(HcFactory::with_capacity(128)),
            modules: HashMap::new(),
            queued: Vec::new()
        }
    }

    pub fn make_term(&self, t: TermData) -> Term {
        let mut factory = self.term_data.borrow_mut();
        factory.make(t)
    }

    pub fn make_value(&self, v: LazyValueData) -> LazyValue {
        let mut factory = self.value_data.borrow_mut();
        factory.make(v)
    }

    pub fn insert_decl(&mut self, module: Symbol, opaque: bool, decl: Decl, inner_ann: Term) -> Result<(), ()> {
        self.freeze_active_metas(module);
        if decl.name == Symbol::from("_") { return Ok(()) }
        let type_value = decl.ty.clone();
        let def_value = if opaque { None } else { Some(decl.body.clone()) };
        let module_data = self.modules.get_mut(&module).unwrap();
        let id = Id::new(module, decl.name);
        if module_data.scope.contains(&id) || module_data.exports.contains(&id) {
            Err(())
        } else {
            module_data.scope.insert(id.clone());
            module_data.exports.insert(id);
            let decl_values = DeclData {
                ann: type_value,
                inner_ann,
                body: def_value
            };
            module_data.decls.insert(decl.name, decl_values);
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

    fn lookup_decl(&self, original: bool, module: Symbol, namespace: Vector<Symbol>, name: Symbol) -> (Vec<(Mode, LazyValue)>, Option<DeclData>) {
        let mut params = vec![];
        let mut result = None;
        // We have a namespace, so we should find the declaration in an imported module
        if_chain! {
            if let Some(component) = namespace.get(0);
            if let Some(import_data) = self.reverse_lookup_namespace(module, *component);
            if original || import_data.public;
            then {
                let mut namespace = namespace.clone();
                namespace.pop_front();
                (_, result) = self.lookup_decl(false, import_data.path, namespace, name);
                params = import_data.args.clone();
            }
        }
        // There is no namespace, so check the current module first
        if_chain! {
            if result.is_none();
            if namespace.is_empty();
            if let Some(module_data) = self.modules.get(&module);
            then {
                result = module_data.decls.get(&name).cloned();
                // If we are pulling the definition from the same module, then we know that parameters are in context,
                // so we should apply variables with levels corresponding to the implied context
                if original {
                    params = module_data.params.iter()
                        .enumerate()
                        .map(|(level, p)| {
                            let sort = p.body.sort().demote();
                            (p.mode, LazyValueData::var(self, sort, level.into()))
                        }).collect();
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
                    if (original || *public) && qual.is_none() && result.is_none() {
                        (_, result) = self.lookup_decl(false, *path, namespace.clone(), name);
                        params = args.clone()
                    }
                }
            }
        }
        (params, result)
    }

    pub fn lookup_def(&self, id: &Id) -> Option<Value> {
        let namespace = id.namespace.clone();
        let (mut params, decl) = self.lookup_decl(true, id.module, namespace, id.name);
        decl.and_then(|decl| decl.body).map(|body| {
            let body = eval(self, Env::new(), body);
            let spine = params.drain(..)
                .map(|(m, v)| Action::Apply(m, v))
                .collect::<Spine>();
            body.perform_spine(self, spine)
        })
    }

    pub fn lookup_type(&self, id: &Id) -> Option<Value> {
        let namespace = id.namespace.clone();
        let (params, decl) = self.lookup_decl(true, id.module, namespace, id.name);
        decl.map(|decl| {
            let ann = if params.is_empty() { decl.ann }
                else { decl.inner_ann };
            eval(self, Env::new(), ann)
        })
    }

    pub fn set_params(&mut self, module: Symbol, params: Vec<Parameter>) {
        if let Some(module_data) = self.modules.get_mut(&module) {
            module_data.params = params
        }
    }

    pub fn lookup_params(&self, module: Symbol) -> Vec<Parameter> {
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

    pub fn insert_meta(&mut self, module: Symbol, name: Symbol, value: Value) -> Result<(), ()> {
        let module_data = self.modules.get_mut(&module).unwrap();
        match module_data.metas.get_mut(&name) {
            None | Some(MetaState::Frozen) | Some(MetaState::Solved(_)) => panic!("TODO FIX"),
            | Some(meta @ MetaState::Unsolved) => {
                *meta = MetaState::Solved(value.clone());
            }
        }
        //log::info!("\n{}\n{}\n{}", name, "solved to", value.quote(self, 0.into()));
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
                log::info!("{} is {}", active, "frozen");
                *meta = MetaState::Frozen
            }
        }
    }
}
