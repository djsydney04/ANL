use crate::{
    MAX_DEPTH, MAX_SOURCE_BYTES, MAX_TOKENS,
    diagnostic::{Diagnostic, Span},
    types::{BinaryOp, Type, UnaryOp, ViewMode},
    word::{ConvertMode, WordWidth},
};

#[derive(Clone, Debug, PartialEq, Eq)]
enum TokenKind {
    Ident(String),
    Integer(String),
    Word(String, WordWidth),
    Fn,
    Let,
    If,
    Else,
    True,
    False,
    Ty(Type),
    Dot,
    LBracket,
    RBracket,
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
    WrapPlus,
    WrapMinus,
    WrapStar,
    BitAnd,
    BitXor,
    BitOr,
    Tilde,
    Shl,
    Shr,
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
            let digits_end = i;
            if bytes
                .get(i)
                .is_some_and(|b| b.is_ascii_alphabetic() || *b == b'_')
            {
                while bytes
                    .get(i)
                    .is_some_and(|b| b.is_ascii_alphanumeric() || *b == b'_')
                {
                    i += 1;
                }
                let width = WordWidth::from_name(&source[digits_end..i]).ok_or_else(|| {
                    Diagnostic::new(
                        Span {
                            source_id,
                            start,
                            end: i,
                        },
                        "invalid unsigned literal suffix",
                    )
                })?;
                TokenKind::Word(source[start..digits_end].to_owned(), width)
            } else {
                TokenKind::Integer(source[start..i].to_owned())
            }
        } else {
            let pair = bytes.get(i..i + 2);
            let pair_kind = match pair {
                Some(b"+%") => Some(TokenKind::WrapPlus),
                Some(b"-%") => Some(TokenKind::WrapMinus),
                Some(b"*%") => Some(TokenKind::WrapStar),
                Some(b"<<") => Some(TokenKind::Shl),
                Some(b">>") => Some(TokenKind::Shr),
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
                    b'[' => TokenKind::LBracket,
                    b']' => TokenKind::RBracket,
                    b'.' => TokenKind::Dot,
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
                    b'&' => TokenKind::BitAnd,
                    b'|' => TokenKind::BitOr,
                    b'^' => TokenKind::BitXor,
                    b'~' => TokenKind::Tilde,
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
    pub view: Option<ViewParameter>,
    pub name: String,
    pub public: bool,
    pub span: Span,
    pub params: Vec<Parameter>,
    pub result: Type,
    pub result_span: Span,
    pub effects: Option<Vec<(String, Span)>>,
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
pub struct Platform {
    pub profile: crate::boot::Profile,
    pub span: Span,
    pub entries: [String; 3],
}
#[derive(Debug)]
pub struct File {
    pub platform: Option<Platform>,
    pub functions: Vec<Function>,
    pub modules: Vec<Module>,
}
#[derive(Debug)]
pub struct ViewParameter {
    pub name: String,
    pub mode: ViewMode,
    pub span: Span,
}
#[derive(Debug)]
pub enum MemoryExpr {
    Heap {
        name: String,
        length: Box<Expr>,
        initial: Box<Expr>,
        success: Box<Expr>,
        failure: Box<Expr>,
    },
    Length {
        name: String,
    },
    Read {
        name: String,
        index: Box<Expr>,
    },
    Write {
        name: String,
        index: Box<Expr>,
        value: Box<Expr>,
    },
    CallView {
        name: String,
        resource: String,
        mode: ViewMode,
        arguments: Vec<Expr>,
    },
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
    Word(String, WordWidth),
    Convert {
        mode: ConvertMode,
        target: Type,
        operand: Box<Expr>,
    },
    Memory(Box<MemoryExpr>),
    Tuple(Vec<Expr>),
    Project {
        value: Box<Expr>,
        index: usize,
    },
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
        mutable: bool,
        annotation: Option<(Type, Span)>,
        value: Expr,
    },
    Assign {
        name: String,
        span: Span,
        value: Expr,
    },
    While {
        condition: Expr,
        invariants: Vec<Clause>,
        body: Expr,
        span: Span,
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
    fn token_type(kind: &TokenKind) -> Option<Type> {
        match kind {
            TokenKind::Ty(t) => Some(*t),
            TokenKind::Ident(s) => WordWidth::from_name(s).map(Type::Word),
            _ => None,
        }
    }
    fn ty(&mut self) -> Result<(Type, Span), Diagnostic> {
        let token = self.bump();
        if let Some(ty) = Self::token_type(&token.kind) {
            return Ok((ty, token.span));
        }
        if token.kind != TokenKind::LParen {
            return Err(Diagnostic::new(
                token.span,
                "expected scalar or flat tuple type",
            ));
        }
        let mut fields = Vec::new();
        loop {
            if fields.len() == crate::types::MAX_TUPLE_FIELDS {
                return Err(Diagnostic::new(
                    self.current().span,
                    "tuple type exceeds 8 fields",
                ));
            }
            let field = self.bump();
            let Some(ty) = Self::token_type(&field.kind) else {
                return Err(Diagnostic::new(
                    field.span,
                    "tuple fields must be scalar types",
                ));
            };
            fields.push(ty.scalar().expect("scalar type token"));
            if fields.len() == 1 {
                self.expect(TokenKind::Comma, ", in tuple type")?;
            } else if !self.eat(&TokenKind::Comma) {
                break;
            }
            if self.at(&TokenKind::RParen) {
                break;
            }
        }
        let end = self.expect(TokenKind::RParen, ")")?.span;
        Ok((
            Type::Tuple(crate::types::TupleShape::new(&fields).expect("bounded tuple type")),
            token.span.join(end),
        ))
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
    fn view_start(&self) -> Option<ViewMode> {
        match (
            &self.current().kind,
            self.tokens.get(self.pos + 1).map(|t| &t.kind),
        ) {
            (TokenKind::Ident(mode), Some(TokenKind::Ident(_))) => ViewMode::from_name(mode),
            _ => None,
        }
    }
    fn program(mut self) -> Result<File, Diagnostic> {
        let mut platform = None;
        let mut functions = Vec::new();
        let mut modules = Vec::new();
        while !self.at(&TokenKind::Eof) {
            if matches!(&self.current().kind, TokenKind::Ident(name) if name == "platform") {
                if platform.is_some() || !functions.is_empty() || !modules.is_empty() {
                    return Err(Diagnostic::new(
                        self.current().span,
                        "platform must be the first and only root platform declaration",
                    ));
                }
                platform = Some(self.platform()?);
                continue;
            }
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
            let view = if let Some(mode) = self.view_start() {
                self.bump();
                let (name, span) = self.name()?;
                self.expect(TokenKind::Colon, ":")?;
                self.expect(TokenKind::Ty(Type::I64), "i64")?;
                self.expect(TokenKind::LBracket, "[")?;
                self.expect(TokenKind::RBracket, "]")?;
                if !self.at(&TokenKind::RParen) {
                    self.expect(TokenKind::Comma, ",")?;
                    if self.at(&TokenKind::RParen) {
                        return Err(Diagnostic::new(
                            self.current().span,
                            "trailing view comma is not allowed",
                        ));
                    }
                }
                Some(ViewParameter { name, mode, span })
            } else {
                None
            };
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
            let effects = if matches!(&self.current().kind, TokenKind::Ident(name) if name == "effects")
            {
                self.bump();
                self.expect(TokenKind::LParen, "(")?;
                let mut effects = Vec::new();
                if !self.at(&TokenKind::RParen) {
                    loop {
                        effects.push(self.name()?);
                        if !self.eat(&TokenKind::Comma) {
                            break;
                        }
                    }
                }
                self.expect(TokenKind::RParen, ")")?;
                Some(effects)
            } else {
                None
            };
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
                view,
                name,
                public,
                span: start.join(body.span),
                params,
                result,
                result_span,
                effects,
                requires,
                ensures,
                body,
            });
        }
        Ok(File {
            platform,
            functions,
            modules,
        })
    }
    fn keyword(&mut self, expected: &str) -> Result<(), Diagnostic> {
        let (name, span) = self.name()?;
        if name == expected {
            Ok(())
        } else {
            Err(Diagnostic::new(span, format!("expected {expected}")))
        }
    }
    fn static_number(&mut self, word: bool) -> Result<u64, Diagnostic> {
        let token = self.bump();
        let text = match token.kind {
            TokenKind::Integer(text) if !word => text,
            TokenKind::Word(text, WordWidth::U64) if word => text,
            _ => {
                return Err(Diagnostic::new(
                    token.span,
                    if word {
                        "expected u64 literal"
                    } else {
                        "expected canonical natural literal"
                    },
                ));
            }
        };
        let value = text
            .parse::<u64>()
            .map_err(|_| Diagnostic::new(token.span, "static number exceeds uint64"))?;
        if !word && value.to_string() != text {
            return Err(Diagnostic::new(
                token.span,
                "static natural must use canonical decimal spelling",
            ));
        }
        Ok(value)
    }
    fn fixed_number(
        &mut self,
        expected: u64,
        word: bool,
        profile: crate::boot::Profile,
    ) -> Result<(), Diagnostic> {
        let span = self.current().span;
        if self.static_number(word)? != expected {
            return Err(Diagnostic::new(
                span,
                format!("value does not match {} profile", profile.target()),
            ));
        }
        Ok(())
    }
    fn platform(&mut self) -> Result<Platform, Diagnostic> {
        let start = self.bump().span;
        let (name, span) = self.name()?;
        let profile = match name.as_str() {
            "rv64_virt_sbi_v1" => crate::boot::Profile::V1,
            "rv64_virt_sbi_v2" => crate::boot::Profile::V2,
            "rv64_virt_sbi_v3" => crate::boot::Profile::V3,
            _ => {
                return Err(Diagnostic::new(
                    span,
                    "expected rv64_virt_sbi_v1, rv64_virt_sbi_v2 or rv64_virt_sbi_v3",
                ));
            }
        };
        self.expect(TokenKind::LBrace, "{")?;
        let mut seen = std::collections::HashSet::new();
        let mut entries = [String::new(), String::new(), String::new()];
        while !self.at(&TokenKind::RBrace) {
            let (kind, span) = self.name()?;
            let key = match kind.as_str() {
                "image_base" => {
                    self.fixed_number(2149580800, true, profile)?;
                    kind
                }
                "image_limit" => {
                    self.fixed_number(1048576, false, profile)?;
                    kind
                }
                "stack" => {
                    let (name, ns) = self.name()?;
                    let size = match name.as_str() {
                        "boot_stack" => 16384,
                        "terminal_stack" => 4096,
                        _ => return Err(Diagnostic::new(ns, "unknown boot stack")),
                    };
                    self.expect(TokenKind::LBracket, "[")?;
                    self.fixed_number(size, false, profile)?;
                    self.expect(TokenKind::RBracket, "]")?;
                    self.keyword("align")?;
                    self.fixed_number(16, false, profile)?;
                    format!("stack:{name}")
                }
                "device" => {
                    self.keyword("uart0")?;
                    self.keyword("at")?;
                    self.fixed_number(268435456, true, profile)?;
                    self.keyword("size")?;
                    self.fixed_number(256, false, profile)?;
                    self.expect(TokenKind::LBrace, "{")?;
                    let mut permissions = std::collections::HashSet::new();
                    while !self.at(&TokenKind::RBrace) {
                        let (permission, ps) = self.name()?;
                        if !permissions.insert(permission.clone()) {
                            return Err(Diagnostic::new(ps, "duplicate device permission"));
                        }
                        match permission.as_str() {
                            "read8" => self.fixed_number(5, false, profile)?,
                            "write8" => {
                                for n in 0..5 {
                                    if n != 0 {
                                        self.expect(TokenKind::Comma, ",")?;
                                    }
                                    self.fixed_number(n, false, profile)?;
                                }
                            }
                            _ => return Err(Diagnostic::new(ps, "unknown device permission")),
                        }
                        self.expect(TokenKind::Semi, ";")?;
                    }
                    self.expect(TokenKind::RBrace, "}")?;
                    if permissions.len() != 2 {
                        return Err(Diagnostic::new(span, "missing device permission"));
                    }
                    if !seen.insert(kind) {
                        return Err(Diagnostic::new(span, "duplicate platform declaration"));
                    }
                    continue;
                }
                "entry" | "hardware_trap" | "language_trap" => {
                    let i = if kind == "entry" {
                        0
                    } else if kind == "hardware_trap" {
                        1
                    } else {
                        2
                    };
                    entries[i] = self.name()?.0;
                    self.keyword("using")?;
                    self.keyword(if i == 0 {
                        "boot_stack"
                    } else {
                        "terminal_stack"
                    })?;
                    kind
                }
                _ => return Err(Diagnostic::new(span, "unknown platform declaration")),
            };
            if !seen.insert(key) {
                return Err(Diagnostic::new(span, "duplicate platform declaration"));
            }
            self.expect(TokenKind::Semi, ";")?;
        }
        let end = self.expect(TokenKind::RBrace, "}")?.span;
        if seen.len() != 8 {
            return Err(Diagnostic::new(
                start,
                "platform must declare image, both stacks, UART and all three roles",
            ));
        }
        Ok(Platform {
            profile,
            span: start.join(end),
            entries,
        })
    }
    fn block(&mut self) -> Result<Expr, Diagnostic> {
        self.enter()?;
        let result = self.block_inner();
        self.recursion -= 1;
        result
    }
    fn while_statement(&self) -> bool {
        if !matches!(&self.current().kind, TokenKind::Ident(name) if name == "while")
            || self.tokens.get(self.pos + 1).map(|token| &token.kind) != Some(&TokenKind::LParen)
        {
            return false;
        }
        let mut depth = 0;
        for (offset, token) in self.tokens[self.pos + 1..].iter().enumerate() {
            match token.kind {
                TokenKind::LParen => depth += 1,
                TokenKind::RParen => {
                    depth -= 1;
                    if depth == 0 {
                        return matches!(
                            self.tokens
                                .get(self.pos + offset + 2)
                                .map(|token| &token.kind),
                            Some(TokenKind::LBrace)
                        ) || matches!(
                            self.tokens.get(self.pos + offset + 2).map(|token| &token.kind),
                            Some(TokenKind::Ident(name)) if name == "invariant"
                        );
                    }
                }
                TokenKind::Eof => break,
                _ => {}
            }
        }
        false
    }
    fn block_inner(&mut self) -> Result<Expr, Diagnostic> {
        let start = self.expect(TokenKind::LBrace, "{")?.span;
        let mut statements = Vec::new();
        let mut tail = None;
        let mut depth = 1;
        while !self.at(&TokenKind::RBrace) {
            if self.eat(&TokenKind::Let) {
                let mutable = matches!(&self.current().kind, TokenKind::Ident(name) if name == "mut")
                    && matches!(
                        self.tokens.get(self.pos + 1).map(|token| &token.kind),
                        Some(TokenKind::Ident(_))
                    );
                if mutable {
                    self.bump();
                }
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
                    mutable,
                    annotation,
                    value,
                });
            } else if self.while_statement() {
                let start = self.bump().span;
                self.expect(TokenKind::LParen, "( after while")?;
                let condition = self.expression()?;
                self.expect(TokenKind::RParen, ") after while condition")?;
                let mut invariants = Vec::new();
                while matches!(&self.current().kind, TokenKind::Ident(name) if name == "invariant")
                {
                    let clause_start = self.bump().span;
                    let expr = self.expression()?;
                    depth = depth.max(expr.depth + 2);
                    let end = self
                        .expect(TokenKind::Semi, "; after invariant clause")?
                        .span;
                    invariants.push(Clause {
                        expr,
                        span: clause_start.join(end),
                    });
                }
                let body = self.block()?;
                depth = depth.max(condition.depth.max(body.depth) + 2);
                let span = start.join(body.span);
                statements.push(Statement::While {
                    condition,
                    invariants,
                    body,
                    span,
                });
            } else if matches!(&self.current().kind, TokenKind::Ident(_))
                && self.tokens.get(self.pos + 1).map(|token| &token.kind)
                    == Some(&TokenKind::Assign)
            {
                let (name, span) = self.name()?;
                self.bump();
                let value = self.expression()?;
                depth = depth.max(value.depth + 2);
                self.expect(TokenKind::Semi, "; after assignment")?;
                statements.push(Statement::Assign { name, span, value });
            } else {
                let mut value = self.expression()?;
                if self.eat(&TokenKind::Assign) {
                    let ExprKind::Memory(memory) = value.kind else {
                        return Err(Diagnostic::new(
                            value.span,
                            "indexed assignment requires a buffer",
                        ));
                    };
                    let MemoryExpr::Read { name, index } = *memory else {
                        return Err(Diagnostic::new(
                            value.span,
                            "indexed assignment requires a buffer index",
                        ));
                    };
                    let rhs = self.expression()?;
                    let span = value.span.join(rhs.span);
                    let d = 1 + index.depth.max(rhs.depth);
                    value = self.node(
                        ExprKind::Memory(Box::new(MemoryExpr::Write {
                            name,
                            index,
                            value: Box::new(rhs),
                        })),
                        span,
                        d,
                    )?;
                    self.expect(TokenKind::Semi, "; after indexed assignment")?;
                    depth = depth.max(value.depth + 1);
                    statements.push(Statement::Discard(value));
                    if statements.len() >= MAX_DEPTH {
                        return Err(Diagnostic::resource(
                            self.current().span,
                            "block binding limit exceeded",
                        ));
                    }
                    continue;
                }
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
            TokenKind::BitOr => (BinaryOp::BitOr, 5),
            TokenKind::BitXor => (BinaryOp::BitXor, 6),
            TokenKind::BitAnd => (BinaryOp::BitAnd, 7),
            TokenKind::Shl => (BinaryOp::Shl, 8),
            TokenKind::Shr => (BinaryOp::Shr, 8),
            TokenKind::Plus => (BinaryOp::Add, 9),
            TokenKind::Minus => (BinaryOp::Sub, 9),
            TokenKind::WrapPlus => (BinaryOp::WrapAdd, 9),
            TokenKind::WrapMinus => (BinaryOp::WrapSub, 9),
            TokenKind::Star => (BinaryOp::Mul, 10),
            TokenKind::Slash => (BinaryOp::Div, 10),
            TokenKind::Percent => (BinaryOp::Rem, 10),
            TokenKind::WrapStar => (BinaryOp::WrapMul, 10),
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
            if matches!(
                op,
                BinaryOp::Eq
                    | BinaryOp::Ne
                    | BinaryOp::Lt
                    | BinaryOp::Le
                    | BinaryOp::Gt
                    | BinaryOp::Ge
            ) && self.operator().is_some_and(|(_, p)| p == precedence)
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
        let result = if self.at(&TokenKind::Minus)
            || self.at(&TokenKind::Bang)
            || self.at(&TokenKind::Tilde)
        {
            let token = self.bump();
            let op = if token.kind == TokenKind::Minus {
                UnaryOp::Neg
            } else if token.kind == TokenKind::Tilde {
                UnaryOp::BitNot
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
            self.postfix()
        };
        self.recursion -= 1;
        result
    }
    fn postfix(&mut self) -> Result<Expr, Diagnostic> {
        let mut value = self.primary()?;
        loop {
            if self.eat(&TokenKind::LBracket) {
                let ExprKind::Name(name) = value.kind else {
                    return Err(Diagnostic::new(
                        value.span,
                        "buffer base must be a bare identifier",
                    ));
                };
                if name.contains("::") {
                    return Err(Diagnostic::new(
                        value.span,
                        "buffer base must be a bare identifier",
                    ));
                }
                let index = self.expression()?;
                let end = self.expect(TokenKind::RBracket, "]")?.span;
                let depth = index.depth + 1;
                value = self.node(
                    ExprKind::Memory(Box::new(MemoryExpr::Read {
                        name,
                        index: Box::new(index),
                    })),
                    value.span.join(end),
                    depth,
                )?;
                continue;
            }
            if !self.eat(&TokenKind::Dot) {
                break;
            }
            let token = self.bump();
            if matches!(&token.kind, TokenKind::Ident(name) if name == "length") {
                let ExprKind::Name(name) = value.kind else {
                    return Err(Diagnostic::new(
                        value.span,
                        "buffer base must be a bare identifier",
                    ));
                };
                if name.contains("::") {
                    return Err(Diagnostic::new(
                        value.span,
                        "buffer base must be a bare identifier",
                    ));
                }
                value = self.node(
                    ExprKind::Memory(Box::new(MemoryExpr::Length { name })),
                    value.span.join(token.span),
                    1,
                )?;
                continue;
            }
            let TokenKind::Integer(index) = token.kind else {
                return Err(Diagnostic::new(
                    token.span,
                    "projection requires a single digit 0..7",
                ));
            };
            if index.len() != 1 || index.as_bytes()[0] > b'7' {
                return Err(Diagnostic::new(
                    token.span,
                    "projection requires a single digit 0..7",
                ));
            }
            let span = value.span.join(token.span);
            let depth = value.depth + 1;
            value = self.node(
                ExprKind::Project {
                    value: Box::new(value),
                    index: usize::from(index.as_bytes()[0] - b'0'),
                },
                span,
                depth,
            )?;
        }
        Ok(value)
    }
    fn primary(&mut self) -> Result<Expr, Diagnostic> {
        let conversion = match &self.current().kind {
            TokenKind::Ident(s) if s == "cast" => Some(ConvertMode::Checked),
            TokenKind::Ident(s) if s == "truncate" => Some(ConvertMode::Truncate),
            _ => None,
        };
        if let Some(mode) = conversion
            && let Some(target) = self
                .tokens
                .get(self.pos + 1)
                .and_then(|t| Self::token_type(&t.kind))
            && target.integer()
            && (mode == ConvertMode::Checked || matches!(target, Type::Word(_)))
            && self.tokens.get(self.pos + 2).map(|t| &t.kind) == Some(&TokenKind::LParen)
        {
            let start = self.bump().span;
            self.bump();
            self.bump();
            let operand = self.expression()?;
            let end = self.expect(TokenKind::RParen, ")")?.span;
            let depth = operand.depth + 1;
            return self.node(
                ExprKind::Convert {
                    mode,
                    target,
                    operand: Box::new(operand),
                },
                start.join(end),
                depth,
            );
        }

        if self.at(&TokenKind::LBrace) {
            return self.block();
        }
        if matches!(&self.current().kind, TokenKind::Ident(s) if s == "heap")
            && matches!(
                self.tokens.get(self.pos + 1).map(|t| &t.kind),
                Some(TokenKind::Ident(_))
            )
            && self.tokens.get(self.pos + 2).map(|t| &t.kind) == Some(&TokenKind::Colon)
            && self.tokens.get(self.pos + 3).map(|t| &t.kind) == Some(&TokenKind::Ty(Type::I64))
            && self.tokens.get(self.pos + 4).map(|t| &t.kind) == Some(&TokenKind::LBracket)
        {
            let start = self.bump().span;
            let (name, _) = self.name()?;
            self.bump();
            self.bump();
            self.bump();
            let length = self.expression()?;
            self.expect(TokenKind::RBracket, "]")?;
            self.expect(TokenKind::Assign, "=")?;
            let initial = self.expression()?;
            let success = self.block()?;
            self.expect(TokenKind::Else, "else")?;
            let failure = self.block()?;
            let depth = 1 + length
                .depth
                .max(initial.depth)
                .max(success.depth)
                .max(failure.depth);
            let span = start.join(failure.span);
            return self.node(
                ExprKind::Memory(Box::new(MemoryExpr::Heap {
                    name,
                    length: Box::new(length),
                    initial: Box::new(initial),
                    success: Box::new(success),
                    failure: Box::new(failure),
                })),
                span,
                depth,
            );
        }
        let token = self.bump();
        let (kind, span, depth) = match token.kind {
            TokenKind::Integer(value) => (ExprKind::Integer(value), token.span, 1),
            TokenKind::Word(value, width) => (ExprKind::Word(value, width), token.span, 1),
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
                    let mut depth = inner.depth + 1;
                    if self.eat(&TokenKind::Comma) {
                        let mut fields = vec![inner];
                        while !self.at(&TokenKind::RParen) {
                            if fields.len() == crate::types::MAX_TUPLE_FIELDS {
                                return Err(Diagnostic::new(
                                    self.current().span,
                                    "tuple exceeds 8 fields",
                                ));
                            }
                            let field = self.expression()?;
                            depth = depth.max(field.depth + 1);
                            fields.push(field);
                            if !self.eat(&TokenKind::Comma) {
                                break;
                            }
                        }
                        let end = self.expect(TokenKind::RParen, ")")?.span;
                        (ExprKind::Tuple(fields), token.span.join(end), depth)
                    } else {
                        let end = self.expect(TokenKind::RParen, ")")?.span;
                        (
                            ExprKind::Group(Box::new(inner)),
                            token.span.join(end),
                            depth,
                        )
                    }
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
                    let view = if let Some(mode) = self.view_start() {
                        self.bump();
                        let (resource, _) = self.name()?;
                        if !self.at(&TokenKind::RParen) {
                            self.expect(TokenKind::Comma, ",")?;
                            if self.at(&TokenKind::RParen) {
                                return Err(Diagnostic::new(
                                    self.current().span,
                                    "trailing view comma is not allowed",
                                ));
                            }
                        }
                        Some((resource, mode))
                    } else {
                        None
                    };
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
                        if let Some((resource, mode)) = view {
                            ExprKind::Memory(Box::new(MemoryExpr::CallView {
                                name,
                                resource,
                                mode,
                                arguments,
                            }))
                        } else {
                            ExprKind::Call { name, arguments }
                        },
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
