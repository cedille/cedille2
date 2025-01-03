
use std::ops::Range;
use std::sync::{Arc, LazyLock};

use logos::Logos;

use cedille2_core::prelude::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Mode {
    Indent,
    Expr
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Extra {
    mode: Mode,
    is_anchor: bool,
    line: usize,
    indent: usize
}

impl Default for Extra {
    fn default() -> Self {
        Self {
            mode: Mode::Indent,
            is_anchor: true,
            line: 0,
            indent: 0
        }
    }
}

fn newline_callback(lex: &mut logos::Lexer<Token>) -> logos::Skip {
    lex.extras.mode = Mode::Indent;
    lex.extras.is_anchor = true;
    lex.extras.line += 1;
    lex.extras.indent = 0;
    logos::Skip
}

fn space_callback(lex: &mut logos::Lexer<Token>) -> logos::Skip {
    if lex.extras.mode == Mode::Indent {
        lex.extras.indent += lex.slice().len();
    }
    logos::Skip
}

fn data_callback(lex: &mut logos::Lexer<Token>) -> bool {
    lex.extras.mode = Mode::Expr;
    let anchor = lex.extras.is_anchor;
    lex.extras.is_anchor = false;
    anchor
}

#[derive(Logos, Debug, Clone, PartialEq, Eq)]
#[logos(extras = Extra)]
pub enum Token {
    #[token("\n", newline_callback)]
    #[token("\r\n", newline_callback)]
    Newline,
    #[regex("[ ]+", space_callback)]
    Space,
    #[regex(r#"[\p{L}\p{M}\p{S}\p{N}\p{P}--[0-9(){}\[\]\.]]+"#, data_callback)]
    Word(bool),
    #[regex(r#"[(){}\[\]\.]"#, data_callback)]
    #[token(".1", data_callback)]
    #[token(".2", data_callback)]
    Punc(bool),
    #[regex("[1-9][0-9]*", data_callback)]
    #[token("0", data_callback)]
    Numeral(bool)
}

#[derive(Debug)]
struct PeekData<'src> {
    token: Option<Result<Token, ()>>,
    slice: &'src str,
    span: Range<usize>,
    line: usize,
    indent: usize
}

#[derive(Debug)]
pub struct Lexer<'src> {
    lexer: logos::Lexer<'src, Token>,
    peeked: Option<PeekData<'src>>,
    pub src: Arc<String>
}

impl<'src> Lexer<'src> {
    pub fn new(source: Arc<String>, source_ref: &'src str) -> Lexer<'src> {
        let lexer = Token::lexer(source_ref);
        let peeked = None;
        Lexer { lexer, peeked, src: source.clone() }
    }

    pub fn slice(&self) -> &str {
        if let Some(data) = &self.peeked {
            data.slice
        } else {
            self.lexer.slice()
        }
    }

    pub fn next(&mut self) -> Option<Result<Token, ()>> {
        let token = self.peeked
            .as_ref()
            .map(|data| data.token.clone())
            .unwrap_or_else(|| self.lexer.next());
        self.peeked = None;
        token
    }

    pub fn peek(&mut self) -> Option<Result<Token, ()>> {
        if let Some(data) = &self.peeked {
            data.token.clone()
        } else {
            let token = self.lexer.next();
            let slice = self.lexer.slice();
            let span = self.lexer.span();
            let line = self.lexer.extras.line;
            let indent = self.lexer.extras.indent;
            let data = PeekData { token: token.clone(), slice, line, indent, span };
            self.peeked = Some(data);
            token
        }
    }

    pub fn line(&self) -> usize {
        if let Some(data) = &self.peeked {
            data.line
        } else {
            self.lexer.extras.line
        }
    }

    pub fn indent(&self) -> usize {
        if let Some(data) = &self.peeked {
            data.indent
        } else {
            self.lexer.extras.indent
        }
    }

    pub fn span(&self) -> Range<usize> {
        if let Some(data) = &self.peeked {
            data.span.clone()
        } else {
            self.lexer.span()
        }
    }
}

pub static KEYWORD_SYNTAX: LazyLock<Symbol> = LazyLock::new(|| Symbol::from("syntax"));

pub static OPERATOR_ARROW: LazyLock<Symbol> = LazyLock::new(|| Symbol::from("->"));
pub static OPERATOR_INTERSECTION : LazyLock<Symbol> = LazyLock::new(|| Symbol::from("∩"));
pub static OPERATOR_EQUAL: LazyLock<Symbol> = LazyLock::new(|| Symbol::from("="));
pub static OPERATOR_COLON: LazyLock<Symbol> = LazyLock::new(|| Symbol::from(":"));
pub static OPERATOR_LAMBDA: LazyLock<Symbol> = LazyLock::new(|| Symbol::from("λ"));

pub static PUNCTUATION_OPEN_PAREN: LazyLock<Symbol> = LazyLock::new(|| Symbol::from("("));
pub static PUNCTUATION_CLOSE_PAREN: LazyLock<Symbol> = LazyLock::new(|| Symbol::from(")"));
pub static PUNCTUATION_OPEN_BRACKET: LazyLock<Symbol> = LazyLock::new(|| Symbol::from("["));
pub static PUNCTUATION_CLOSE_BRACKET: LazyLock<Symbol> = LazyLock::new(|| Symbol::from("]"));
pub static PUNCTUATION_OPEN_BRACE: LazyLock<Symbol> = LazyLock::new(|| Symbol::from("{"));
pub static PUNCTUATION_CLOSE_BRACE: LazyLock<Symbol> = LazyLock::new(|| Symbol::from("}"));
pub static PUNCTUATION_DOT: LazyLock<Symbol> = LazyLock::new(|| Symbol::from("."));
pub static PUNCTUATION_FIRST_PROJ: LazyLock<Symbol> = LazyLock::new(|| Symbol::from(".1"));
pub static PUNCTUATION_SECOND_PROJ: LazyLock<Symbol> = LazyLock::new(|| Symbol::from(".2"));

#[allow(unused_imports, unused_macros)]
mod tests {
    use super::*;

    macro_rules! test_token {
        ($lexer:expr, $kind:ident, $anchor:expr, $indent:expr, $line:expr, $slice:expr) => {
            let token = $lexer.next().unwrap().unwrap();
            assert_eq!($lexer.indent(), $indent);
            assert_eq!($lexer.line(), $line);
            assert_eq!($lexer.slice(), $slice);
            assert_eq!(token, Token::$kind($anchor));
        }
    }

    macro_rules! peek_token {
        ($lexer:expr, $kind:ident, $anchor:expr, $indent:expr, $line:expr, $slice:expr) => {
            let token = $lexer.peek().unwrap().unwrap();
            assert_eq!($lexer.indent(), $indent);
            assert_eq!($lexer.line(), $line);
            assert_eq!($lexer.slice(), $slice);
            assert_eq!(token, Token::$kind($anchor));
        }
    }

    #[test]
    fn lexer_ex1() {
        let input = r#"
            module test
            syntax _+_ 1 2
            f : (0A : Set) -> a∩b = c.2
        "#;
        let input = Arc::new(input.to_string());
        let mut lexer = Lexer::new(input.clone(), input.as_ref());
        test_token!(lexer, Word, true, 12, 1, "module");
        test_token!(lexer, Word, false, 12, 1, "test");
        test_token!(lexer, Word, true, 12, 2, "syntax");
        test_token!(lexer, Word, false, 12, 2, "_+_");
        test_token!(lexer, Numeral, false, 12, 2, "1");
        test_token!(lexer, Numeral, false, 12, 2, "2");
        peek_token!(lexer, Word, true, 12, 3, "f");
        test_token!(lexer, Word, true, 12, 3, "f");
        test_token!(lexer, Word, false, 12, 3, ":");
        test_token!(lexer, Punc, false, 12, 3, "(");
        test_token!(lexer, Numeral, false, 12, 3, "0");
        test_token!(lexer, Word, false, 12, 3, "A");
        test_token!(lexer, Word, false, 12, 3, ":");
        test_token!(lexer, Word, false, 12, 3, "Set");
        peek_token!(lexer, Punc, false, 12, 3, ")");
        test_token!(lexer, Punc, false, 12, 3, ")");
        test_token!(lexer, Word, false, 12, 3, "->");
        test_token!(lexer, Word, false, 12, 3, "a∩b");
        test_token!(lexer, Word, false, 12, 3, "=");
        test_token!(lexer, Word, false, 12, 3, "c");
        test_token!(lexer, Punc, false, 12, 3, ".2");
        assert_eq!(lexer.next(), None);
    }

    #[test]
    fn lexer_indent() {
        let input = r#"
                    these
                are
            some
                        words bruh
        "#;
        let input = Arc::new(input.to_string());
        let mut lexer = Lexer::new(input.clone(), input.as_ref());
        test_token!(lexer, Word, true, 20, 1, "these");
        test_token!(lexer, Word, true, 16, 2, "are");
        test_token!(lexer, Word, true, 12, 3, "some");
        test_token!(lexer, Word, true, 24, 4, "words");
        test_token!(lexer, Word, false, 24, 4, "bruh");
        assert_eq!(lexer.next(), None);
    }
}
