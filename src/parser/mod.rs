use crate::{
    backends::Backend,
    constants::Span,
    error::{Error, ErrorKind, Result},
    lexer::{Keyword, Token, TokenKind, Tokens},
};

pub use self::types::{ConstDef, FunctionDef, Root, RootKind, UsePath};

pub mod expr;
pub mod structs;
pub mod types;

pub use expr::{Expr, ExprKind, Op2};
pub use structs::{CustomType, StructDef};

//~
//~ # Grammar
//~
//~ ## Notation
//~
//~ We use a notation similar to the Backus-Naur Form (BNF)
//~ to describe the grammar:
//~
//~ <pre>
//~ land := city "|"
//~  ^        ^   ^
//~  |        |  terminal: a token
//~  |        |
//~  |      another non-terminal
//~  |
//~  non-terminal: definition of a piece of code
//~
//~ city := [ sign ] "," { house }
//~         ^            ^
//~         optional     |
//~                     0r or more houses
//~
//~ sign := /a-zA-Z_/
//~         ^
//~         regex-style definition
//~ </pre>
//~

//
// Context
//

/// A context for the parser.
#[derive(Debug, Default)]
pub struct ParserCtx {
    /// A counter used to uniquely identify different nodes in the AST.
    pub node_id: usize,

    /// Used mainly for error reporting,
    /// when we don't have a token to read
    // TODO: replace with `(usize::MAX, usize::MAX)`?
    pub last_token: Option<Token>,

    /// The file we're parsing
    pub filename_id: usize,
}

impl ParserCtx {
    pub fn new(filename_id: usize, node_id: usize) -> Self {
        Self {
            node_id,
            last_token: None,
            filename_id,
        }
    }

    pub fn error(&self, kind: ErrorKind, span: Span) -> Error {
        Error::new("parser", kind, span)
    }

    /// Returns a new unique node id.
    pub fn next_node_id(&mut self) -> usize {
        self.node_id += 1;
        self.node_id
    }

    // TODO: I think I don't need this, I should always be able to use the last token I read if I don't see anything, otherwise maybe just write -1 to say "EOF"
    pub fn last_span(&self) -> Span {
        let span = self
            .last_token
            .as_ref()
            .map(|token| token.span)
            .unwrap_or(Span::new(self.filename_id, 0, 0));
        Span::new(self.filename_id, span.end(), 0)
    }
}

//
// AST
//

#[derive(Debug, Default)]
pub struct AST<B: Backend>(pub Vec<Root<B::Field>>);

impl<B: Backend> AST<B> {
    pub fn parse(
        filename_id: usize,
        mut tokens: Tokens,
        node_id: usize,
    ) -> Result<(AST<B>, usize)> {
        let mut ast = vec![];
        let ctx = &mut ParserCtx::new(filename_id, node_id);

        // use statements must appear first
        let mut function_observed = false;

        while let Some(token) = tokens.bump(ctx) {
            match &token.kind {
                // `use crypto::poseidon;`
                TokenKind::Keyword(Keyword::Use) => {
                    if function_observed {
                        return Err(ctx.error(ErrorKind::UseAfterFn, token.span));
                    }

                    let path = UsePath::parse(ctx, &mut tokens)?;
                    ast.push(Root {
                        kind: RootKind::Use(path),
                        span: token.span,
                    });

                    // end of line
                    let next_token = tokens.bump(ctx);
                    if !matches!(
                        next_token,
                        Some(Token {
                            kind: TokenKind::SemiColon,
                            ..
                        })
                    ) {
                        return Err(ctx.error(ErrorKind::InvalidEndOfLine, token.span));
                    }
                }

                // `const FOO = 42;`
                TokenKind::Keyword(Keyword::Const) => {
                    let cst = ConstDef::parse(ctx, &mut tokens)?;

                    ast.push(Root {
                        kind: RootKind::ConstDef(cst),
                        span: token.span,
                    });
                }

                // `fn main() { }`
                TokenKind::Keyword(Keyword::Fn) => {
                    function_observed = true;

                    let func = FunctionDef::parse(ctx, &mut tokens)?;
                    ast.push(Root {
                        kind: RootKind::FunctionDef(func),
                        span: token.span,
                    });
                }

                // `struct Foo { a: Field, b: Field }`
                TokenKind::Keyword(Keyword::Struct) => {
                    let s = StructDef::parse(ctx, &mut tokens)?;
                    ast.push(Root {
                        kind: RootKind::StructDef(s),
                        span: token.span,
                    });
                }

                // `// some comment`
                TokenKind::Comment(comment) => {
                    ast.push(Root {
                        kind: RootKind::Comment(comment.clone()),
                        span: token.span,
                    });
                }

                // unrecognized
                _ => {
                    return Err(ctx.error(ErrorKind::InvalidToken, token.span));
                }
            }
        }

        Ok((Self(ast), ctx.node_id))
    }
}

//
// Tests
//
/*
#[cfg(test)]
mod tests {
    use crate::parser::types::Stmt;

    use super::*;

    #[test]
    fn fn_signature() {
        let code = r#"main(pub public_input: [Fel; 3], private_input: [Fel; 3]) -> [Fel; 3] { return public_input; }"#;
        let tokens = &mut Token::parse(0, code).unwrap();
        let ctx = &mut ParserCtx::default();
        let parsed = FunctionDef::parse(ctx, tokens).unwrap();
        println!("{:?}", parsed);
    }

    #[test]
    fn statement_assign() {
        let code = r#"let digest = poseidon(private_input);"#;
        let tokens = &mut Token::parse(0, code).unwrap();
        let ctx = &mut ParserCtx::default();
        let parsed = Stmt::parse(ctx, tokens).unwrap();
        println!("{:?}", parsed);
    }

    #[test]
    fn statement_assert() {
        let code = r#"assert(digest == public_input);"#;
        let tokens = &mut Token::parse(0, code).unwrap();
        let ctx = &mut ParserCtx::default();
        let parsed = Stmt::parse(ctx, tokens).unwrap();
        println!("{:?}", parsed);
    }

}
*/

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::types::{Stmt, StmtKind};

    #[test]
    fn test_plus_equal_assignment() {
        let code = "count += value;";
        let tokens = Token::parse(0, code).expect("Failed to parse tokens");
        let mut ctx = ParserCtx::new(0, 0);
        let mut tokens = tokens.clone();

        let stmt = Stmt::parse(&mut ctx, &mut tokens).expect("Failed to parse statement");

        match stmt.kind {
            StmtKind::Expr(ref expr) => {
                match expr.kind {
                    ExprKind::Assignment { ref lhs, ref rhs } => {
                        match lhs.kind {
                            ExprKind::Variable { ref name, .. } => {
                                assert_eq!(name.value, "count");
                            },
                            _ => panic!("Expected variable on the left-hand side"),
                        }

                        match &rhs.kind {
                            ExprKind::BinaryOp { op, ref lhs, ref rhs, .. } => {
                                assert_eq!(*op, Op2::Addition);

                                match lhs.kind {
                                    ExprKind::Variable { ref name, .. } => {
                                        assert_eq!(name.value, "count");
                                    },
                                    _ => panic!("Expected variable on the left-hand side of binary op"),
                                }

                                match rhs.kind {
                                    ExprKind::Variable { ref name, .. } => {
                                        assert_eq!(name.value, "value");
                                    },
                                    _ => panic!("Expected variable on the right-hand side of binary op"),
                                }
                            },
                            _ => panic!("Expected binary operation on the right-hand side"),
                        }
                    },
                    _ => panic!("Expected assignment expression"),
                }
            },
            _ => panic!("Expected expression statement"),
        }
    }
}
