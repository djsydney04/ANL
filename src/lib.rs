//! APL M1 source checker, typed core interchange, and bounded reference evaluator.
//! Formal proof scope is recorded separately under `formal/`.
pub mod core;
pub mod diagnostic;
pub mod eval;
mod resolve;
mod syntax;
pub mod types;

pub const MAX_SOURCE_BYTES: usize = 1_048_576;
pub const MAX_TOKENS: usize = 100_000;
pub const MAX_DEPTH: usize = 128;
pub const MAX_EVAL_DEPTH: usize = 256;
pub const DEFAULT_FUEL: u64 = 100_000;
pub const MAX_FUEL: u64 = 1_000_000_000;

pub fn compile(source: &str) -> Result<types::Program, diagnostic::Diagnostic> {
    resolve::check(syntax::parse(source)?)
}
