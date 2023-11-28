
use std::io;
use std::fmt;
use std::error::Error;

use miette::{GraphicalReportHandler, GraphicalTheme};
//use rustyline::error::ReadlineError;

use crate::parser;
use crate::elaborator::ElabError;
use crate::database::DatabaseError;

#[derive(Debug)]
pub enum CedilleError {
    // Parser(pest::error::Error<parser::Rule>),
    Elaborator(ElabError),
    Database(DatabaseError),
    External(Box<dyn Error + Send + Sync>),
    Collection(Vec<CedilleError>)
}

impl fmt::Display for CedilleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            // CedilleError::Parser(error) => {
            //     error.fmt(f)
            // }
            CedilleError::Elaborator(e) => {
                let mut out = String::new();
                GraphicalReportHandler::new_themed(GraphicalTheme::unicode())
                    .with_width(80)
                    .render_report(&mut out, e)?;
                out.fmt(f)
            }
            CedilleError::Database(e) => e.fmt(f),
            CedilleError::External(e) => e.fmt(f),
            CedilleError::Collection(list) => {
                for e in list.iter().rev() {
                    e.fmt(f)?;
                    writeln!(f)?;
                }
                Ok(())
            }
        }
    }
}

// impl From<pest::error::Error<parser::Rule>> for CedilleError {
//     fn from (error: pest::error::Error<parser::Rule>) -> Self { CedilleError::Parser(error) }
// }

impl From<ElabError> for CedilleError {
    fn from (error: ElabError) -> Self { CedilleError::Elaborator(error) }
}

impl From<DatabaseError> for CedilleError {
    fn from(error: DatabaseError) -> Self { CedilleError::Database(error) }
}

impl From<io::Error> for CedilleError {
    fn from(error: io::Error) -> Self { CedilleError::External(Box::new(error)) }
}

impl From<std::string::FromUtf8Error> for CedilleError {
    fn from (error: std::string::FromUtf8Error) -> Self { CedilleError::External(Box::new(error)) }
}
