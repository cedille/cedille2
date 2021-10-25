
use std::collections::btree_map::OccupiedEntry;
use std::io::prelude::*;
use std::fs::{self, File};
use std::time::SystemTime;
use std::path::{Path, PathBuf};
use std::collections::HashMap;
use std::collections::hash_map::Entry::{Vacant, Occupied};

use petgraph::prelude::*;
use petgraph::algo::{toposort, kosaraju_scc};
use radix_trie::Trie;
use anyhow::{Context, Result, anyhow};
use colored::*;
use thiserror::Error;

use crate::parser;
use crate::syntax;

type Symbol = u16;

#[derive(Debug, Error)]
pub enum DatabaseError {
    #[error("Non unicode path {path:?} ")]
    NonUnicodePath { path: PathBuf },
    #[error("Expected symbol {sym:?} to correspond to a Module")]
    MissingModuleSymbol { sym: Symbol },
    #[error("Expected path {path:?} to be loaded")]
    UnloadedPath { path: PathBuf },
}

#[derive(Debug)]
pub struct ModuleData {
    syntax: syntax::Module,
    text: String,
    path: String,
    imports: Vec<Symbol>,
    exports: Vec<Symbol>,
    last_modified: SystemTime,
}

impl ModuleData {
    fn new(key: &str, mut file: File, last_modified: SystemTime) -> Result<ModuleData> {
        println!("{} {}{}", "loading file".dimmed(), key, "...".dimmed());
        let mut buffer = Vec::new();
        file.read_to_end(&mut buffer)?;
        let text = String::from_utf8(buffer)?;
        let tree = parser::parse(&text)?;
        let tree = parser::module(tree);
        let data = ModuleData {
            syntax: tree,
            text,
            path: key.to_string(),
            imports: Vec::new(),
            exports: Vec::new(),
            last_modified,
        };
        Ok(data)
    }
}

#[derive(Debug)]
pub struct Database {
    pub modules: HashMap<Symbol, ModuleData>,
    module_order: Vec<Symbol>,
    symbols: Trie<String, Symbol>,
    fresh_symbol: Symbol,
}

impl Database {

    pub fn new() -> Database {
        Database { 
            modules: HashMap::new(),
            module_order: Vec::new(),
            symbols: Trie::new(),
            fresh_symbol: 0,
        }
    }

    fn symbol(&mut self, key: &str) -> Symbol {
        match self.symbols.get(key) {
            Some(v) => *v,
            None => {
                let result = self.fresh_symbol;
                self.symbols.insert(key.to_string(), result);
                self.fresh_symbol += 1;
                result
            }
        }
    }

    fn load_imports<P: AsRef<Path>>(&mut self, prefix: P, module: Symbol) -> Result<()> {
        let paths = {
            let module_data = self.modules.get_mut(&module)
                .ok_or(DatabaseError::MissingModuleSymbol { sym:module })?;
            let mut result = vec![];
            for i in module_data.syntax.imports.iter() {
                let (start, end) = i.path;
                let path = module_data.text[start..end].to_string();
                result.push(path);
            }
            result
        };
        for path in paths {
            let path = prefix.as_ref().join(path).with_extension("ced");
            let sym = self.load_module(path)?;
            self.modules.get_mut(&module)
                .ok_or(DatabaseError::MissingModuleSymbol { sym:module })?
                .imports
                .push(sym);
        }
        Ok(())
    }

    pub fn load_module<P: AsRef<Path>>(&mut self, path: P) -> Result<Symbol> {
        let path = path.as_ref();
        let file = File::open(path)
            .with_context(|| format!("Failed to open file with path {}", path.display()))?;
        if let Some(ext) = path.extension() {
            if ext.to_string_lossy() != "ced" { return Ok(0); }

            let metadata = path.metadata()?;
            let last_modified = metadata.modified().unwrap_or_else(|_| SystemTime::now());

            let canonical_path = path.canonicalize()?;
            let key = canonical_path.to_str()
                .ok_or(DatabaseError::NonUnicodePath { path:path.to_path_buf() })?;
            let sym = self.symbol(key);

            match self.modules.entry(sym) {
                Occupied(mut occupied) => {
                    let current_modified = occupied.get().last_modified;
                    if last_modified > current_modified {
                        let data = ModuleData::new(key, file, last_modified)?;
                        let module = occupied.get_mut();
                        *module = data;
                        self.load_imports(path.parent().unwrap(), sym)?;
                    } else {
                        println!("{} {}{}", "skipping file".dimmed(), canonical_path.display(), "...".dimmed());
                    }
                },
                Vacant(vacant) => {
                    let data = ModuleData::new(key, file, last_modified)?;
                    vacant.insert(data);
                    self.load_imports(path.parent().unwrap(), sym)?;
                }
            }
            Ok(sym)
        } else {
            Ok(0)
        }
    }

    pub fn load_dir(&mut self, path: &Path) -> Result<bool> {
        for entry in fs::read_dir(path)? {
            let entry = entry?;
            let path = entry.path();
            if path.is_file() {
                if let Err(error) = self.load_module(path) {
                    println!("{}", error);
                }
            } else {
                self.load_dir(&path)?;
            }
        }
        Ok(true)
    }

    pub fn sort(&mut self) -> Result<()> {
        let mut edges = Vec::new();
        for (source, module) in self.modules.iter() {
            for import in module.imports.iter() {
                let path = &self.modules.get(import)
                    .ok_or(DatabaseError::MissingModuleSymbol { sym:*import })?
                    .path;
                let target = self.symbols.get(path)
                    .ok_or(DatabaseError::UnloadedPath { path:path.into() })?;
                edges.push((*source as u32, *target as u32));
            }
        }
        let graph = Graph::<u32, ()>::from_edges(edges.drain(..));
        match toposort(&graph, None) {
            Ok(mut sorted) => { 
                self.module_order = sorted.drain(..).map(|i| i.index() as u16).collect();
                Ok(())
            },
            Err(cycle) => {
                let node = cycle.node_id();
                let mut scc = kosaraju_scc(&graph);
                let mut cycle_walk = scc.drain(..)
                    .filter(|v| v.contains(&node));
                let mut walk = cycle_walk.next().unwrap();
                let walk: Vec<&String> = walk.drain(..)
                    .map(|n| &self.modules.get(&(n.index() as Symbol)).unwrap().path)
                    .collect();
                let mut message = String::new();
                for node in walk {
                    message.push('\n');
                    message.push_str("    ");
                    message.push_str(node);
                }
                Err(anyhow!("Cycle detected: {}", message))
            }
        }
    }
}
