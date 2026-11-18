use super::{Failure, formula::StateBudget, hash_file};
use crate::types::Type;
use serde_json::{Value, json};
use std::{
    env, fs,
    path::{Path, PathBuf},
    time::Instant,
};

pub(super) struct Solver {
    pub path: PathBuf,
    pub hash: String,
    pub version: String,
}
pub(super) struct Answer {
    pub status: &'static str,
    pub model: Value,
}
pub(super) struct Attempt {
    pub outcome: Result<Answer, Failure>,
    pub transcript: String,
}
pub(super) struct ModelSymbol {
    pub name: String,
    pub ty: Type,
    pub origin: Value,
    pub head: Option<usize>,
}
#[derive(Clone, Copy)]
enum ModelRequest<'a> {
    Parameters(&'a [Type]),
    Symbols(&'a [ModelSymbol]),
}
impl Solver {
    pub fn discover(requested: &Path, deadline: Instant) -> Result<Self, Failure> {
        let path = if requested.components().count() > 1 || requested.is_absolute() {
            requested.canonicalize().map_err(|e| {
                Failure::Error(format!("cannot locate solver {}: {e}", requested.display()))
            })?
        } else {
            env::split_paths(&env::var_os("PATH").unwrap_or_default())
                .map(|dir| dir.join(requested))
                .find(|path| path.is_file())
                .ok_or_else(|| {
                    Failure::Error(format!(
                        "solver {} was not found on PATH",
                        requested.display()
                    ))
                })?
                .canonicalize()
                .map_err(|e| Failure::Error(e.to_string()))?
        };
        if !fs::metadata(&path)
            .map_err(|e| Failure::Error(e.to_string()))?
            .is_file()
        {
            return Err(Failure::Error("solver is not a regular file".into()));
        }
        let hash = hash_file(&path, deadline)?;
        let version = process::version(&path, deadline)?;
        let fields: Vec<_> = version.split_whitespace().collect();
        if version.lines().count() != 1 || fields.get(..3) != Some(&["Z3", "version", "5.3.3"]) {
            return Err(Failure::Error(format!(
                "solver must report Z3 version 5.3.3, got {version:?}"
            )));
        }
        Ok(Self {
            path,
            hash,
            version,
        })
    }
    pub fn query(
        &self,
        script: &str,
        params: &[Type],
        deadline: Instant,
        max_bytes: usize,
    ) -> Attempt {
        let mut transcript = script.to_owned();
        let outcome = process::query(
            &self.path,
            script,
            ModelRequest::Parameters(params),
            deadline,
            &mut transcript,
            max_bytes,
            None,
        );
        Attempt {
            outcome,
            transcript,
        }
    }
    pub fn query_symbols(
        &self,
        script: &str,
        symbols: &[ModelSymbol],
        deadline: Instant,
        max_bytes: usize,
        budget: &mut StateBudget,
    ) -> Attempt {
        let mut transcript = script.to_owned();
        let outcome = process::query(
            &self.path,
            script,
            ModelRequest::Symbols(symbols),
            deadline,
            &mut transcript,
            max_bytes,
            Some(budget),
        );
        Attempt {
            outcome,
            transcript,
        }
    }
}

#[derive(Debug)]
enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}
fn parse_sexp(text: &str, mut budget: Option<&mut StateBudget>) -> Result<Sexp, Failure> {
    fn parse(
        bytes: &[u8],
        pos: &mut usize,
        depth: usize,
        budget: &mut Option<&mut StateBudget>,
    ) -> Result<Sexp, Failure> {
        if let Some(budget) = budget {
            budget.charge(1)?;
        }
        if depth > 32 {
            return Err(Failure::Error("solver response nesting exceeds 32".into()));
        }
        while bytes.get(*pos).is_some_and(u8::is_ascii_whitespace) {
            *pos += 1;
        }
        if bytes.get(*pos) == Some(&b'(') {
            *pos += 1;
            let mut items = Vec::new();
            loop {
                while bytes.get(*pos).is_some_and(u8::is_ascii_whitespace) {
                    *pos += 1;
                }
                if bytes.get(*pos) == Some(&b')') {
                    *pos += 1;
                    return Ok(Sexp::List(items));
                }
                if *pos == bytes.len() {
                    return Err(Failure::Error("unterminated solver model".into()));
                }
                if let Some(budget) = budget {
                    budget.reserve(&mut items, 1)?;
                }
                items.push(parse(bytes, pos, depth + 1, budget)?);
            }
        }
        let start = *pos;
        while bytes
            .get(*pos)
            .is_some_and(|b| !b.is_ascii_whitespace() && *b != b'(' && *b != b')')
        {
            *pos += 1;
        }
        if start == *pos {
            return Err(Failure::Error("malformed solver response".into()));
        }
        let atom = std::str::from_utf8(&bytes[start..*pos])
            .map_err(|_| Failure::Error("solver output is not UTF-8".into()))?;
        if !atom
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'-' || b == b'_')
        {
            return Err(Failure::Error("invalid solver response atom".into()));
        }
        if let Some(budget) = budget {
            budget.charge(atom.len())?;
        }
        Ok(Sexp::Atom(atom.into()))
    }
    let mut pos = 0;
    let value = parse(text.as_bytes(), &mut pos, 0, &mut budget)?;
    if !text[pos..].trim().is_empty() {
        return Err(Failure::Error("extra solver output after model".into()));
    }
    Ok(value)
}
fn integer(value: &Sexp) -> Option<i64> {
    fn natural(atom: &str) -> Option<i128> {
        if atom.is_empty()
            || !atom.bytes().all(|b| b.is_ascii_digit())
            || (atom.len() > 1 && atom.starts_with('0'))
        {
            return None;
        }
        atom.parse().ok()
    }
    let n = match value {
        Sexp::Atom(atom) => natural(atom)?,
        Sexp::List(items) => match items.as_slice() {
            [Sexp::Atom(op), Sexp::Atom(atom)] if op == "-" => -natural(atom)?,
            _ => return None,
        },
    };
    n.try_into().ok()
}
fn model(text: &str, params: &[Type]) -> Result<Value, Failure> {
    let expected = params.iter().filter(|ty| **ty != Type::Unit).count();
    if expected == 0 {
        if !text.trim().is_empty() {
            return Err(Failure::Error(
                "unexpected solver output for empty model".into(),
            ));
        }
        return Ok(json!({"replayed":false,"assignments":[]}));
    }
    let Sexp::List(entries) = parse_sexp(text, None)? else {
        return Err(Failure::Error("solver model is not a list".into()));
    };
    if entries.len() != expected {
        return Err(Failure::Error(
            "solver model has wrong parameter count".into(),
        ));
    }
    let mut seen = vec![false; params.len()];
    let mut assignments = Vec::new();
    for entry in entries {
        let Sexp::List(pair) = entry else {
            return Err(Failure::Error("malformed solver model entry".into()));
        };
        let [Sexp::Atom(name), value] = pair.as_slice() else {
            return Err(Failure::Error("malformed solver model pair".into()));
        };
        let index: usize = name
            .strip_prefix('p')
            .and_then(|n| n.parse().ok())
            .filter(|&i| i < params.len() && format!("p{i}") == *name)
            .ok_or_else(|| Failure::Error("unknown solver model symbol".into()))?;
        if seen[index] {
            return Err(Failure::Error("duplicate solver model symbol".into()));
        }
        seen[index] = true;
        let value = match params[index] {
            Type::Word(_) => {
                return Err(Failure::Unsupported(
                    "word solver values are unsupported".into(),
                ));
            }
            Type::I64 => json!(
                integer(value)
                    .ok_or_else(|| Failure::Error(
                        "solver integer model is malformed or outside i64".into()
                    ))?
                    .to_string()
            ),
            Type::Bool => match value {
                Sexp::Atom(v) if v == "true" => json!(true),
                Sexp::Atom(v) if v == "false" => json!(false),
                _ => return Err(Failure::Error("invalid solver Boolean model".into())),
            },
            Type::Tuple(_) => {
                return Err(Failure::Unsupported(
                    "flat products are outside scalar verification".into(),
                ));
            }
            Type::Unit => return Err(Failure::Error("unexpected unit solver variable".into())),
        };
        assignments.push(
            json!({"parameter":index,"symbol":name,"type":params[index].as_str(),"value":value}),
        );
    }
    Ok(json!({"replayed":false,"assignments":assignments}))
}

fn mathematical_integer(value: &Sexp, budget: &mut StateBudget) -> Result<String, Failure> {
    let (negative, atom) = match value {
        Sexp::Atom(atom) => (false, atom),
        Sexp::List(items) => match items.as_slice() {
            [Sexp::Atom(op), Sexp::Atom(atom)] if op == "-" => (true, atom),
            _ => {
                return Err(Failure::Error(
                    "malformed mathematical integer model".into(),
                ));
            }
        },
    };
    budget.charge(atom.len())?;
    if atom.is_empty()
        || !atom.bytes().all(|b| b.is_ascii_digit())
        || (atom.len() > 1 && atom.starts_with('0'))
    {
        return Err(Failure::Error(
            "malformed mathematical integer model".into(),
        ));
    }
    budget.charge(atom.len() + 1)?;
    Ok(if negative && atom != "0" {
        format!("-{atom}")
    } else {
        atom.clone()
    })
}

fn within_i64(decimal: &str) -> bool {
    let (digits, limit) = match decimal.strip_prefix('-') {
        Some(digits) => (digits, "9223372036854775808"),
        None => (decimal, "9223372036854775807"),
    };
    digits.len() < limit.len() || (digits.len() == limit.len() && digits <= limit)
}

fn model_symbols(
    text: &str,
    symbols: &[ModelSymbol],
    budget: &mut StateBudget,
) -> Result<Value, Failure> {
    if symbols.is_empty() {
        if !text.trim().is_empty() {
            return Err(Failure::Error(
                "unexpected solver output for empty model".into(),
            ));
        }
        return Ok(json!({"replayed":false,"assignments":[]}));
    }
    let Sexp::List(entries) = parse_sexp(text, Some(budget))? else {
        return Err(Failure::Error("solver model is not a list".into()));
    };
    if entries.len() != symbols.len() {
        return Err(Failure::Error("solver model has wrong symbol count".into()));
    }
    budget.charge(symbols.len())?;
    let mut names = std::collections::HashMap::new();
    names
        .try_reserve(symbols.len())
        .map_err(|_| Failure::Unknown("model allocation failed".into()))?;
    for (index, symbol) in symbols.iter().enumerate() {
        budget.charge(1)?;
        if names.insert(symbol.name.as_str(), index).is_some() {
            return Err(Failure::Error("duplicate model manifest symbol".into()));
        }
    }
    let mut assignments = Vec::new();
    budget.reserve(&mut assignments, symbols.len())?;
    assignments.resize(symbols.len(), Value::Null);
    for entry in entries {
        budget.charge(1)?;
        let Sexp::List(pair) = entry else {
            return Err(Failure::Error("malformed solver model entry".into()));
        };
        let [Sexp::Atom(name), value] = pair.as_slice() else {
            return Err(Failure::Error("malformed solver model pair".into()));
        };
        let index = *names
            .get(name.as_str())
            .ok_or_else(|| Failure::Error("unknown solver model symbol".into()))?;
        if !assignments[index].is_null() {
            return Err(Failure::Error("duplicate solver model symbol".into()));
        }
        let symbol = &symbols[index];
        let value_json = match symbol.ty {
            Type::Word(_) => {
                return Err(Failure::Unsupported(
                    "word solver values are unsupported".into(),
                ));
            }
            Type::I64 if symbol.head.is_some() => {
                Value::String(mathematical_integer(value, budget)?)
            }
            Type::I64 => json!(
                integer(value)
                    .ok_or_else(|| Failure::Error(
                        "solver integer model is malformed or outside i64".into()
                    ))?
                    .to_string()
            ),
            Type::Bool => match value {
                Sexp::Atom(v) if v == "true" => json!(true),
                Sexp::Atom(v) if v == "false" => json!(false),
                _ => return Err(Failure::Error("invalid solver Boolean model".into())),
            },
            Type::Tuple(_) => {
                return Err(Failure::Unsupported(
                    "flat products are outside scalar verification".into(),
                ));
            }
            Type::Unit => return Err(Failure::Error("unexpected unit solver variable".into())),
        };
        budget.charge(12)?;
        let head_range = if symbol.head.is_some() && symbol.ty == Type::I64 {
            Some(within_i64(
                value_json.as_str().expect("mathematical integer"),
            ))
        } else {
            None
        };
        let mut assignment =
            json!({"symbol":name,"type":symbol.ty.as_str(),"origin":symbol.origin});
        assignment["value"] = value_json;
        if symbol.head.is_some() && symbol.ty == Type::I64 {
            assignment["within_machine_range"] = json!(head_range.expect("head range"));
        }
        assignments[index] = assignment;
    }
    let mut model = json!({"replayed":false});
    model["assignments"] = Value::Array(assignments);
    Ok(model)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;
    fn budget() -> StateBudget {
        StateBudget::new(Instant::now() + Duration::from_secs(5))
    }
    fn symbols() -> Vec<ModelSymbol> {
        vec![
            ModelSymbol {
                name: "p0".into(),
                ty: Type::I64,
                origin: json!({"kind":"parameter","index":0}),
                head: None,
            },
            ModelSymbol {
                name: "h3".into(),
                ty: Type::I64,
                origin: json!({"kind":"loop_head"}),
                head: Some(3),
            },
            ModelSymbol {
                name: "h4".into(),
                ty: Type::Bool,
                origin: json!({"kind":"loop_head"}),
                head: Some(4),
            },
        ]
    }
    #[test]
    fn mathematical_head_models_preserve_large_values_and_validate_machine_fit() {
        for (value, expected, fit) in [
            (
                "9223372036854775807".into(),
                "9223372036854775807".into(),
                true,
            ),
            (
                "9223372036854775808".into(),
                "9223372036854775808".into(),
                false,
            ),
            (
                "(- 9223372036854775808)".into(),
                "-9223372036854775808".into(),
                true,
            ),
            (
                "(- 9223372036854775809)".into(),
                "-9223372036854775809".into(),
                false,
            ),
            (
                format!("(- {})", "9".repeat(200)),
                format!("-{}", "9".repeat(200)),
                false,
            ),
            ("(- 0)".into(), "0".into(), true),
        ] {
            let model = model_symbols(
                &format!("((h4 true)(h3 {value})(p0 0))"),
                &symbols(),
                &mut budget(),
            )
            .unwrap();
            assert_eq!(model["assignments"][1]["value"], expected);
            assert_eq!(model["assignments"][1]["within_machine_range"], fit);
            assert_eq!(model["assignments"][0]["symbol"], "p0");
            assert_eq!(model["replayed"], false);
        }
    }
    #[test]
    fn manifest_models_reject_missing_unknown_duplicate_wrong_sort_and_parameter_overflow() {
        for text in [
            "((p0 0)(h3 0))",
            "((p0 0)(h3 0)(h9 true))",
            "((p0 0)(h3 0)(h3 1))",
            "((p0 0)(h3 0)(h4 1))",
            "((p0 0)(h3 true)(h4 true))",
            "((p0 9223372036854775808)(h3 0)(h4 true))",
            "((p0 0)(h3 01)(h4 true))",
            "((p0 0)(h3 (- -1))(h4 true))",
        ] {
            assert!(
                matches!(
                    model_symbols(text, &symbols(), &mut budget()),
                    Err(Failure::Error(_))
                ),
                "{text}"
            );
        }
        assert_eq!(
            model_symbols("", &[], &mut budget()).unwrap(),
            json!({"replayed":false,"assignments":[]})
        );
        assert!(model_symbols("()", &[], &mut budget()).is_err());
    }
}

#[cfg(unix)]
mod process {
    use super::*;
    use nix::{
        fcntl::{FcntlArg, OFlag, fcntl},
        sys::signal::{Signal, killpg},
        unistd::Pid,
    };
    use std::{
        io::{ErrorKind, Read, Write},
        os::{fd::AsFd, unix::process::CommandExt},
        process::{Child, ChildStderr, ChildStdin, ChildStdout, Command, ExitStatus, Stdio},
        thread,
        time::Duration,
    };
    struct Process {
        child: Child,
        input: Option<ChildStdin>,
        output: ChildStdout,
        error: ChildStderr,
        stdout: Vec<u8>,
        stderr: Vec<u8>,
        out_eof: bool,
        err_eof: bool,
        status: Option<ExitStatus>,
    }
    fn nonblocking(fd: &impl AsFd) -> Result<(), Failure> {
        let flags = fcntl(fd, FcntlArg::F_GETFL).map_err(|e| Failure::Error(e.to_string()))?;
        fcntl(
            fd,
            FcntlArg::F_SETFL(OFlag::from_bits_truncate(flags) | OFlag::O_NONBLOCK),
        )
        .map_err(|e| Failure::Error(e.to_string()))?;
        Ok(())
    }
    impl Process {
        fn spawn(path: &Path, args: &[&str]) -> Result<Self, Failure> {
            let mut child = Command::new(path)
                .args(args)
                .process_group(0)
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
                .map_err(|e| Failure::Error(format!("cannot start solver: {e}")))?;
            let input = child.stdin.take().expect("piped stdin");
            let output = child.stdout.take().expect("piped stdout");
            let error = child.stderr.take().expect("piped stderr");
            let process = Self {
                child,
                input: Some(input),
                output,
                error,
                stdout: Vec::new(),
                stderr: Vec::new(),
                out_eof: false,
                err_eof: false,
                status: None,
            };
            nonblocking(process.input.as_ref().expect("stdin exists"))?;
            nonblocking(&process.output)?;
            nonblocking(&process.error)?;
            Ok(process)
        }
        fn pump(&mut self, deadline: Instant) -> Result<(), Failure> {
            if Instant::now() >= deadline {
                return Err(Failure::Unknown("verification deadline exceeded".into()));
            }
            fn drain(
                reader: &mut impl Read,
                buffer: &mut Vec<u8>,
                eof: &mut bool,
                limit: usize,
                deadline: Instant,
            ) -> Result<(), Failure> {
                if *eof {
                    return Ok(());
                }
                let mut bytes = [0; 8192];
                loop {
                    if Instant::now() >= deadline {
                        return Err(Failure::Unknown("verification deadline exceeded".into()));
                    }
                    match reader.read(&mut bytes) {
                        Ok(0) => {
                            *eof = true;
                            break;
                        }
                        Ok(n) => {
                            if buffer.len() + n > limit {
                                return Err(Failure::Error(
                                    "solver output exceeds its byte limit".into(),
                                ));
                            }
                            buffer.extend_from_slice(&bytes[..n]);
                        }
                        Err(e) if e.kind() == ErrorKind::WouldBlock => break,
                        Err(e) if e.kind() == ErrorKind::Interrupted => continue,
                        Err(e) => {
                            return Err(Failure::Error(format!("cannot read solver output: {e}")));
                        }
                    }
                }
                Ok(())
            }
            drain(
                &mut self.output,
                &mut self.stdout,
                &mut self.out_eof,
                1_048_576,
                deadline,
            )?;
            drain(
                &mut self.error,
                &mut self.stderr,
                &mut self.err_eof,
                65_536,
                deadline,
            )?;
            if self.status.is_none() {
                self.status = self
                    .child
                    .try_wait()
                    .map_err(|e| Failure::Error(e.to_string()))?;
            }
            Ok(())
        }
        fn send(&mut self, bytes: &[u8], deadline: Instant) -> Result<(), Failure> {
            let mut sent = 0;
            while sent < bytes.len() {
                self.pump(deadline)?;
                match self
                    .input
                    .as_mut()
                    .ok_or_else(|| Failure::Error("solver input was closed".into()))?
                    .write(&bytes[sent..])
                {
                    Ok(0) => return Err(Failure::Error("solver closed its input".into())),
                    Ok(n) => sent += n,
                    Err(e) if e.kind() == ErrorKind::WouldBlock => {
                        thread::sleep(Duration::from_millis(1))
                    }
                    Err(e) if e.kind() == ErrorKind::Interrupted => {}
                    Err(e) => {
                        return Err(Failure::Error(format!("cannot write solver input: {e}")));
                    }
                }
            }
            Ok(())
        }
        fn finish(&mut self, deadline: Instant) -> Result<(), Failure> {
            self.input.take();
            while self.status.is_none() || !self.out_eof || !self.err_eof {
                self.pump(deadline)?;
                thread::sleep(Duration::from_millis(1));
            }
            if !self.status.expect("status exists").success() {
                return Err(Failure::Error(format!(
                    "solver exited unsuccessfully: {}",
                    self.status.expect("status exists")
                )));
            }
            if !self.stderr.is_empty() {
                return Err(Failure::Error(format!(
                    "solver wrote stderr: {}",
                    String::from_utf8_lossy(&self.stderr)
                )));
            }
            Ok(())
        }
    }
    impl Drop for Process {
        fn drop(&mut self) {
            // A descendant may retain pipes even after the solver exits.
            if self.status.is_none() || !self.out_eof || !self.err_eof {
                let _ = killpg(Pid::from_raw(self.child.id() as i32), Signal::SIGKILL);
            }
            if self.status.is_none() {
                let _ = self.child.kill();
                let _ = self.child.wait();
            }
        }
    }
    pub fn version(path: &Path, deadline: Instant) -> Result<String, Failure> {
        let mut process = Process::spawn(path, &["-version"])?;
        process.finish(deadline)?;
        String::from_utf8(process.stdout.clone())
            .map(|s| s.trim().to_owned())
            .map_err(|_| Failure::Error("solver version is not UTF-8".into()))
    }
    pub fn query(
        path: &Path,
        script: &str,
        request: ModelRequest<'_>,
        deadline: Instant,
        transcript: &mut String,
        max_bytes: usize,
        mut budget: Option<&mut StateBudget>,
    ) -> Result<Answer, Failure> {
        let mut process = Process::spawn(path, &["-in", "-smt2"])?;
        process.send(script.as_bytes(), deadline)?;
        let (status, consumed) = loop {
            process.pump(deadline)?;
            let text = std::str::from_utf8(&process.stdout)
                .map_err(|_| Failure::Error("solver output is not UTF-8".into()))?;
            let trimmed = text.trim_start();
            if let Some(end) = trimmed
                .find(char::is_whitespace)
                .or_else(|| process.out_eof.then_some(trimmed.len()))
            {
                let atom = &trimmed[..end];
                let status = match atom {
                    "sat" => "sat",
                    "unsat" => "unsat",
                    "unknown" => "unknown",
                    _ => return Err(Failure::Error(format!("invalid solver status: {atom:?}"))),
                };
                break (status, text.len() - trimmed.len() + end);
            }
            if process.status.is_some() && process.out_eof {
                return Err(Failure::Error("solver exited without a status".into()));
            }
            thread::sleep(Duration::from_millis(1));
        };
        let symbols: Vec<_> = match request {
            ModelRequest::Parameters(params) => params
                .iter()
                .enumerate()
                .filter(|(_, ty)| **ty != Type::Unit)
                .map(|(i, _)| format!("p{i}"))
                .collect(),
            ModelRequest::Symbols(symbols) => {
                budget
                    .as_deref_mut()
                    .expect("manifest budget")
                    .charge(symbols.len() * 2)?;
                symbols.iter().map(|s| s.name.clone()).collect()
            }
        };
        let mut suffix = String::new();
        if status == "sat" && !symbols.is_empty() {
            suffix.push_str(&format!("(get-value ({}))\n", symbols.join(" ")));
        }
        suffix.push_str("(exit)\n");
        if script.len() + suffix.len() > max_bytes {
            return Err(Failure::Unknown(
                "query protocol exceeds its byte budget".into(),
            ));
        }
        transcript.push_str(&suffix);
        process.send(suffix.as_bytes(), deadline)?;
        process.finish(deadline)?;
        let remainder = std::str::from_utf8(&process.stdout[consumed..])
            .map_err(|_| Failure::Error("solver output is not UTF-8".into()))?;
        let model = if status == "sat" {
            match request {
                ModelRequest::Parameters(params) => model(remainder, params)?,
                ModelRequest::Symbols(symbols) => {
                    model_symbols(remainder, symbols, budget.expect("manifest budget"))?
                }
            }
        } else {
            if !remainder.trim().is_empty() {
                return Err(Failure::Error("unexpected trailing solver output".into()));
            }
            Value::Null
        };
        Ok(Answer { status, model })
    }
}
#[cfg(not(unix))]
mod process {
    use super::*;
    pub fn version(_: &Path, _: Instant) -> Result<String, Failure> {
        Err(Failure::Unsupported(
            "solver process control is supported on Unix hosts".into(),
        ))
    }
    pub fn query(
        _: &Path,
        _: &str,
        _: ModelRequest<'_>,
        _: Instant,
        _: &mut String,
        _: usize,
        _: Option<&mut StateBudget>,
    ) -> Result<Answer, Failure> {
        Err(Failure::Unsupported(
            "solver process control is supported on Unix hosts".into(),
        ))
    }
}
