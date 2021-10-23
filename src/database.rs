
use std::io::prelude::*;
use std::fs::{self, File};
use std::path::{Path, PathBuf};
use std::collections::HashMap;
use std::collections::hash_map::Entry::Vacant;

use petgraph::prelude::*;
use petgraph::algo::toposort;
use petgraph::algo::kosaraju_scc;
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
pub struct Database {
    pub modules: HashMap<Symbol, syntax::Module>,
    module_order: Vec<Symbol>,
    module_paths: HashMap<Symbol, String>,
    module_imports: HashMap<Symbol, Vec<Symbol>>,
    symbols: Trie<String, Symbol>,
    fresh_symbol: Symbol,
}

impl Database {

    pub fn new() -> Database {
        Database { 
            modules: HashMap::new(),
            module_order: Vec::new(),
            module_paths: HashMap::new(),
            module_imports: HashMap::new(),
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
        let paths = self.modules.get(&module)
            .map(|m| {
                let mut result = vec![];
                for i in m.imports.iter() {
                    let (start, end) = i.path;
                    let path = m.text[start..end].to_string();
                    result.push(path);
                }
                result
            })
            .ok_or(DatabaseError::MissingModuleSymbol { sym:module })?;
        for path in paths {
            let path = prefix.as_ref().join(path).with_extension("ced");
            let sym = self.load_module(path)?;
            let imports = self.module_imports.entry(module).or_insert_with(Vec::new);
            imports.push(sym);
        }
        Ok(())
    }

    pub fn load_module<P: AsRef<Path>>(&mut self, path: P) -> Result<Symbol> {
        let path = path.as_ref();
        let mut file = File::open(path)
            .with_context(|| format!("Failed to open file with path {}", path.display()))?;
        if let Some(ext) = path.extension() {
            if ext.to_string_lossy() != "ced" { return Ok(0); }

            let canonical_path = path.canonicalize()?;
            let key = canonical_path.to_str()
                .ok_or(DatabaseError::NonUnicodePath { path:path.to_path_buf() })?;
            let sym = self.symbol(key);
            self.module_paths.insert(sym, key.to_string());

            if let Vacant(vacant) = self.modules.entry(sym) {
                println!("{} {}{}", "loading file".dimmed(), canonical_path.display(), "...".dimmed());
                let mut buffer = Vec::new();
                file.read_to_end(&mut buffer)?;
                let text = String::from_utf8(buffer)?;
                let tree = parser::parse(&text)?;
                let mut tree = parser::module(tree);
                tree.text = text;
                vacant.insert(tree);
                self.load_imports(path.parent().unwrap(), sym)?;
            } else {
                println!("{} {}{}", "skipping file".dimmed(), canonical_path.display(), "...".dimmed());
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
        for source in self.modules.keys() {
            if let Some(imports) = self.module_imports.get(source) {
                for import in imports.iter() {
                    let path = self.module_paths.get(import)
                        .ok_or(DatabaseError::MissingModuleSymbol { sym:*import })?;
                    let target = self.symbols.get(path)
                        .ok_or(DatabaseError::UnloadedPath { path:path.into() })?;
                    edges.push((*source as u32, *target as u32));
                }
            }
        }
        let graph = Graph::<u32, ()>::from_edges(edges.drain(..));
        match toposort(&graph, None) {
            Ok(mut sorted) => { 
                self.module_order = sorted.drain(..).map(|i| i.index() as u16).collect();
            },
            Err(cycle) => {
                let node = cycle.node_id();
                let mut scc = kosaraju_scc(&graph);
                let mut cycle_walk = scc.drain(..)
                    .filter(|v| v.contains(&node));
                if let Some(mut walk) = cycle_walk.next() {
                    let walk: Vec<&String> = walk.drain(..)
                        .map(|n| self.module_paths.get(&(n.index() as Symbol)).unwrap())
                        .collect();
                    let mut message = String::new();
                    for node in walk {
                        message.push('\n');
                        message.push_str("    ");
                        message.push_str(node);
                    }
                    return Err(anyhow!("Cycle detected: {}", message));
                }
            }
        }
        Ok(())
    }
}
