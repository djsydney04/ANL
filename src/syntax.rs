use crate::{
    MAX_DEPTH, MAX_SOURCE_BYTES, MAX_TOKENS,
    diagnostic::{Diagnostic, Span},
    types::{BinaryOp, Type, UnaryOp},
};

#[derive(Clone, Debug, PartialEq, Eq)]
enum TokenKind {
    Ident(String),
    Integer(String),
    Fn,
    Let,
    If,
    Else,
    True,
    False,
    Ty(Type),
    LParen,
    RParen,
    LBrace,
    RBrace,
    Comma,
    Colon,
    PathSep,
    Semi,
    Assign,
    Arrow,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Bang,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
    Eof,
}
#[derive(Clone, Debug)]
struct Token {
    kind: TokenKind,
    span: Span,
}

pub fn identifier(name: &str) -> bool {
    let mut bytes = name.bytes();
    bytes
        .next()
        .is_some_and(|b| b.is_ascii_alphabetic() || b == b'_')
        && bytes.all(|b| b.is_ascii_alphanumeric() || b == b'_')
        && !matches!(
            name,
            "fn" | "let" | "if" | "else" | "true" | "false" | "i64" | "bool" | "unit"
        )
}

fn lex(source: &str, source_id: usize) -> Result<Vec<Token>, Diagnostic> {
    if source.len() > MAX_SOURCE_BYTES {
        return Err(Diagnostic::resource(
            Span {
                source_id,
                ..Span::default()
            },
            "source exceeds 1048576 bytes",
        ));
    }
    let bytes = source.as_bytes();
    let mut i = 0;
    let mut tokens = Vec::new();
    while i < bytes.len() {
        if matches!(bytes[i], b' ' | b'\t' | b'\r' | b'\n') {
            i += 1;
            continue;
        }
        if bytes[i..].starts_with(b"//") {
            while i < bytes.len() && !matches!(bytes[i], b'\r' | b'\n') {
                i += 1;
            }
            continue;
        }
        let start = i;
        let kind = if bytes[i].is_ascii_alphabetic() || bytes[i] == b'_' {
            i += 1;
            while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                i += 1;
            }
            match &source[start..i] {
                "fn" => TokenKind::Fn,
                "let" => TokenKind::Let,
                "if" => TokenKind::If,
                "else" => TokenKind::Else,
                "true" => TokenKind::True,
                "false" => TokenKind::False,
                "i64" => TokenKind::Ty(Type::I64),
                "bool" => TokenKind::Ty(Type::Bool),
                "unit" => TokenKind::Ty(Type::Unit),
                name => TokenKind::Ident(name.to_owned()),
            }
        } else if bytes[i].is_ascii_digit() {
            i += 1;
            while i < bytes.len() && bytes[i].is_ascii_digit() {
                i += 1;
            }
            TokenKind::Integer(source[start..i].to_owned())
        } else {
            let pair = bytes.get(i..i + 2);
            let pair_kind = match pair {
                Some(b"->") => Some(TokenKind::Arrow),
                Some(b"==") => Some(TokenKind::Eq),
                Some(b"!=") => Some(TokenKind::Ne),
                Some(b"<=") => Some(TokenKind::Le),
                Some(b">=") => Some(TokenKind::Ge),
                Some(b"&&") => Some(TokenKind::And),
                Some(b"||") => Some(TokenKind::Or),
                Some(b"::") => Some(TokenKind::PathSep),
                _ => None,
            };
            if let Some(kind) = pair_kind {
                i += 2;
                kind
            } else {
                i += 1;
                match bytes[start] {
                    b'(' => TokenKind::LParen,
                    b')' => TokenKind::RParen,
                    b'{' => TokenKind::LBrace,
                    b'}' => TokenKind::RBrace,
                    b',' => TokenKind::Comma,
                    b':' => TokenKind::Colon,
                    b';' => TokenKind::Semi,
                    b'=' => TokenKind::Assign,
                    b'+' => TokenKind::Plus,
                    b'-' => TokenKind::Minus,
                    b'*' => TokenKind::Star,
                    b'/' => TokenKind::Slash,
                    b'%' => TokenKind::Percent,
                    b'!' => TokenKind::Bang,
                    b'<' => TokenKind::Lt,
                    b'>' => TokenKind::Gt,
                    _ => {
                        let ch = source[start..].chars().next().unwrap();
                        return Err(Diagnostic::new(
                            Span {
                                source_id,
                                start,
                                end: start + ch.len_utf8(),
                            },
                            format!("unexpected character {ch:?}"),
                        ));
                    }
                }
            }
        };
        tokens.push(Token {
            kind,
            span: Span {
                source_id,
                start,
                end: i,
            },
        });
        if tokens.len() > MAX_TOKENS {
            return Err(Diagnostic::resource(
                Span {
                    source_id,
                    start,
                    end: i,
                },
                "token limit exceeded",
            ));
        }
    }
    tokens.push(Token {
        kind: TokenKind::Eof,
        span: Span {
            source_id,
            start: i,
            end: i,
        },
    });
    Ok(tokens)
}

#[derive(Debug)]
pub struct Function {
    pub name: String,
    pub public: bool,
    pub span: Span,
    pub params: Vec<Parameter>,
    pub result: Type,
    pub result_span: Span,
    pub requires: Vec<Clause>,
    pub ensures: Vec<Postcondition>,
    pub body: Expr,
}
#[derive(Debug)]
pub struct Clause {
    pub expr: Expr,
    pub span: Span,
}
#[derive(Debug)]
pub struct Postcondition {
    pub binder: String,
    pub binder_span: Span,
    pub clause: Clause,
}
#[derive(Debug)]
pub struct Module {
    pub name: String,
    pub public: bool,
    pub span: Span,
}
#[derive(Debug)]
pub struct File {
    pub functions: Vec<Function>,
    pub modules: Vec<Module>,
}
#[derive(Debug)]
pub struct Parameter {
    pub name: String,
    pub ty: Type,
    pub span: Span,
}
#[derive(Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
    pub depth: usize,
}
#[derive(Debug)]
pub enum ExprKind {
    Integer(String),
    Boolean(bool),
    Unit,
    Name(String),
    Group(Box<Expr>),
    Block {
        statements: Vec<Statement>,
        tail: Option<Box<Expr>>,
    },
    Unary {
        op: UnaryOp,
        operand: Box<Expr>,
    },
    Binary {
        op: BinaryOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    If {
        condition: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Box<Expr>,
    },
    Call {
        name: String,
        arguments: Vec<Expr>,
    },
}
#[derive(Debug)]
pub enum Statement {
    Let {
        name: String,
        span: Span,
        annotation: Option<(Type, Span)>,
        value: Expr,
    },
    Discard(Expr),
}

pub fn parse(source: &str, source_id: usize) -> Result<File, Diagnostic> {
    Parser {
        tokens: lex(source, source_id)?,
        pos: 0,
        recursion: 0,
    }
    .program()
}
struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    recursion: usize,
}
impl Parser {
    fn current(&self) -> &Token {
        &self.tokens[self.pos]
    }
    fn at(&self, kind: &TokenKind) -> bool {
        self.current().kind == *kind
    }
    fn bump(&mut self) -> Token {
        let token = self.current().clone();
        if !self.at(&TokenKind::Eof) {
            self.pos += 1;
        }
        token
    }
    fn eat(&mut self, kind: &TokenKind) -> bool {
        if self.at(kind) {
            self.bump();
            true
        } else {
            false
        }
    }
    fn expect(&mut self, kind: TokenKind, text: &str) -> Result<Token, Diagnostic> {
        if self.at(&kind) {
            Ok(self.bump())
        } else {
            Err(Diagnostic::new(
                self.current().span,
                format!("expected {text}"),
            ))
        }
    }
    fn name(&mut self) -> Result<(String, Span), Diagnostic> {
        let token = self.bump();
        if let TokenKind::Ident(name) = token.kind {
            Ok((name, token.span))
        } else {
            Err(Diagnostic::new(token.span, "expected identifier"))
        }
    }
    fn ty(&mut self) -> Result<(Type, Span), Diagnostic> {
        let token = self.bump();
        if let TokenKind::Ty(ty) = token.kind {
            Ok((ty, token.span))
        } else {
            Err(Diagnostic::new(
                token.span,
                "expected type i64, bool, or unit",
            ))
        }
    }
    fn enter(&mut self) -> Result<(), Diagnostic> {
        if self.recursion >= MAX_DEPTH {
            return Err(Diagnostic::resource(
                self.current().span,
                "parser nesting limit exceeded",
            ));
        }
        self.recursion += 1;
        Ok(())
    }
    fn node(&self, kind: ExprKind, span: Span, depth: usize) -> Result<Expr, Diagnostic> {
        if depth > MAX_DEPTH {
            return Err(Diagnostic::resource(
                span,
                "expression depth limit exceeded",
            ));
        }
        Ok(Expr { kind, span, depth })
    }
    fn program(mut self) -> Result<File, Diagnostic> {
        let mut functions = Vec::new();
        let mut modules = Vec::new();
        while !self.at(&TokenKind::Eof) {
            let public = if matches!(&self.current().kind, TokenKind::Ident(name) if name == "pub")
            {
                self.bump();
                true
            } else {
                false
            };
            if matches!(&self.current().kind, TokenKind::Ident(name) if name == "mod") {
                let start = self.bump().span;
                let (name, _) = self.name()?;
                let end = self
                    .expect(TokenKind::Semi, "; after module declaration")?
                    .span;
                modules.push(Module {
                    name,
                    public,
                    span: start.join(end),
                });
                continue;
            }
            let start = self.expect(TokenKind::Fn, "fn")?.span;
            let (name, _) = self.name()?;
            self.expect(TokenKind::LParen, "(")?;
            let mut params = Vec::new();
            if !self.at(&TokenKind::RParen) {
                loop {
                    let (name, span) = self.name()?;
                    self.expect(TokenKind::Colon, ":")?;
                    let (ty, _) = self.ty()?;
                    params.push(Parameter { name, ty, span });
                    if !self.eat(&TokenKind::Comma) {
                        break;
                    }
                }
            }
            self.expect(TokenKind::RParen, ")")?;
            self.expect(TokenKind::Arrow, "->")?;
            let (result, result_span) = self.ty()?;
            let mut requires = Vec::new();
            let mut ensures = Vec::new();
            while matches!(&self.current().kind, TokenKind::Ident(name) if name == "requires" || name == "ensures")
            {
                let token = self.bump();
                if matches!(&token.kind, TokenKind::Ident(name) if name == "requires") {
                    if !ensures.is_empty() {
                        return Err(Diagnostic::new(
                            token.span,
                            "requires clauses must precede ensures clauses",
                        ));
                    }
                    let expr = self.expression()?;
                    let end = self
                        .expect(TokenKind::Semi, "; after requires clause")?
                        .span;
                    requires.push(Clause {
                        expr,
                        span: token.span.join(end),
                    });
                } else {
                    self.expect(TokenKind::LParen, "( before result binder")?;
                    let (binder, binder_span) = self.name()?;
                    self.expect(TokenKind::RParen, ") after result binder")?;
                    let expr = self.expression()?;
                    let end = self.expect(TokenKind::Semi, "; after ensures clause")?.span;
                    ensures.push(Postcondition {
                        binder,
                        binder_span,
                        clause: Clause {
                            expr,
                            span: token.span.join(end),
                        },
                    });
                }
            }
            let body = self.block()?;
            functions.push(Function {
                name,
                public,
                span: start.join(body.span),
                params,
                result,
                result_span,
                requires,
                ensures,
                body,
            });
        }
        Ok(File { functions, modules })
    }
    fn block(&mut self) -> Result<Expr, Diagnostic> {
        self.enter()?;
        let result = self.block_inner();
        self.recursion -= 1;
        result
    }
    fn block_inner(&mut self) -> Result<Expr, Diagnostic> {
        let start = self.expect(TokenKind::LBrace, "{")?.span;
        let mut statements = Vec::new();
        let mut tail = None;
        let mut depth = 1;
        while !self.at(&TokenKind::RBrace) {
            if self.eat(&TokenKind::Let) {
                let (name, span) = self.name()?;
                let annotation = if self.eat(&TokenKind::Colon) {
                    Some(self.ty()?)
                } else {
                    None
                };
                self.expect(TokenKind::Assign, "=")?;
                let value = self.expression()?;
                depth = depth.max(value.depth + 1);
                self.expect(TokenKind::Semi, "; after let binding")?;
                statements.push(Statement::Let {
                    name,
                    span,
                    annotation,
                    value,
                });
            } else {
                let value = self.expression()?;
                depth = depth.max(value.depth + 1);
                if self.eat(&TokenKind::Semi) {
                    statements.push(Statement::Discard(value));
                } else {
                    tail = Some(Box::new(value));
                    break;
                }
            }
            if statements.len() >= MAX_DEPTH {
                return Err(Diagnostic::resource(
                    self.current().span,
                    "block binding limit exceeded",
                ));
            }
        }
        let end = self
            .expect(TokenKind::RBrace, "} or ; after expression")?
            .span;
        self.node(ExprKind::Block { statements, tail }, start.join(end), depth)
    }
    fn expression(&mut self) -> Result<Expr, Diagnostic> {
        self.enter()?;
        let result = self.binary(1);
        self.recursion -= 1;
        result
    }
    fn operator(&self) -> Option<(BinaryOp, u8)> {
        Some(match self.current().kind {
            TokenKind::Or => (BinaryOp::Or, 1),
            TokenKind::And => (BinaryOp::And, 2),
            TokenKind::Eq => (BinaryOp::Eq, 3),
            TokenKind::Ne => (BinaryOp::Ne, 3),
            TokenKind::Lt => (BinaryOp::Lt, 4),
            TokenKind::Le => (BinaryOp::Le, 4),
            TokenKind::Gt => (BinaryOp::Gt, 4),
            TokenKind::Ge => (BinaryOp::Ge, 4),
            TokenKind::Plus => (BinaryOp::Add, 5),
            TokenKind::Minus => (BinaryOp::Sub, 5),
            TokenKind::Star => (BinaryOp::Mul, 6),
            TokenKind::Slash => (BinaryOp::Div, 6),
            TokenKind::Percent => (BinaryOp::Rem, 6),
            _ => return None,
        })
    }
    fn binary(&mut self, minimum: u8) -> Result<Expr, Diagnostic> {
        let mut left = self.unary()?;
        while let Some((op, precedence)) = self.operator() {
            if precedence < minimum {
                break;
            }
            self.bump();
            let right = self.binary(precedence + 1)?;
            let span = left.span.join(right.span);
            let depth = left.depth.max(right.depth) + 1;
            left = self.node(
                ExprKind::Binary {
                    op,
                    left: Box::new(left),
                    right: Box::new(right),
                },
                span,
                depth,
            )?;
            if matches!(precedence, 3 | 4) && self.operator().is_some_and(|(_, p)| p == precedence)
            {
                return Err(Diagnostic::new(
                    self.current().span,
                    "repeated comparison or equality requires parentheses",
                ));
            }
        }
        Ok(left)
    }
    fn unary(&mut self) -> Result<Expr, Diagnostic> {
        self.enter()?;
        let result = if self.at(&TokenKind::Minus) || self.at(&TokenKind::Bang) {
            let token = self.bump();
            let op = if token.kind == TokenKind::Minus {
                UnaryOp::Neg
            } else {
                UnaryOp::Not
            };
            let operand = self.unary()?;
            let span = token.span.join(operand.span);
            let depth = operand.depth + 1;
            self.node(
                ExprKind::Unary {
                    op,
                    operand: Box::new(operand),
                },
                span,
                depth,
            )
        } else {
            self.primary()
        };
        self.recursion -= 1;
        result
    }
    fn primary(&mut self) -> Result<Expr, Diagnostic> {
        if self.at(&TokenKind::LBrace) {
            return self.block();
        }
        let token = self.bump();
        let (kind, span, depth) = match token.kind {
            TokenKind::Integer(value) => (ExprKind::Integer(value), token.span, 1),
            TokenKind::True => (ExprKind::Boolean(true), token.span, 1),
            TokenKind::False => (ExprKind::Boolean(false), token.span, 1),
            TokenKind::LParen => {
                if self.eat(&TokenKind::RParen) {
                    (
                        ExprKind::Unit,
                        token.span.join(self.tokens[self.pos - 1].span),
                        1,
                    )
                } else {
                    let inner = self.expression()?;
                    let end = self.expect(TokenKind::RParen, ")")?.span;
                    let depth = inner.depth + 1;
                    (
                        ExprKind::Group(Box::new(inner)),
                        token.span.join(end),
                        depth,
                    )
                }
            }
            TokenKind::Ident(mut name) => {
                let mut name_span = token.span;
                let mut segments = 1;
                while self.eat(&TokenKind::PathSep) {
                    segments += 1;
                    if segments > crate::MAX_MODULE_DEPTH {
                        return Err(Diagnostic::resource(
                            token.span,
                            "module path exceeds 32 segments",
                        ));
                    }
                    let (part, span) = self.name()?;
                    name.push_str("::");
                    name.push_str(&part);
                    name_span = name_span.join(span);
                }
                if self.eat(&TokenKind::LParen) {
                    let mut arguments = Vec::new();
                    let mut depth = 1;
                    if !self.at(&TokenKind::RParen) {
                        loop {
                            let argument = self.expression()?;
                            depth = depth.max(argument.depth + 1);
                            arguments.push(argument);
                            if !self.eat(&TokenKind::Comma) {
                                break;
                            }
                        }
                    }
                    let end = self.expect(TokenKind::RParen, ")")?.span;
                    (
                        ExprKind::Call { name, arguments },
                        token.span.join(end),
                        depth,
                    )
                } else {
                    (ExprKind::Name(name), name_span, 1)
                }
            }
            TokenKind::If => {
                let condition = self.expression()?;
                let then_branch = self.block()?;
                self.expect(TokenKind::Else, "else")?;
                let else_branch = self.block()?;
                let span = token.span.join(else_branch.span);
                let depth = 1 + condition
                    .depth
                    .max(then_branch.depth)
                    .max(else_branch.depth);
                (
                    ExprKind::If {
                        condition: Box::new(condition),
                        then_branch: Box::new(then_branch),
                        else_branch: Box::new(else_branch),
                    },
                    span,
                    depth,
                )
            }
            _ => return Err(Diagnostic::new(token.span, "expected expression")),
        };
        self.node(kind, span, depth)
    }
}
