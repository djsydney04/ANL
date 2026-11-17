use super::{Failure, hash_file};
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
            params,
            deadline,
            &mut transcript,
            max_bytes,
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
fn parse_sexp(text: &str) -> Result<Sexp, Failure> {
    fn parse(bytes: &[u8], pos: &mut usize, depth: usize) -> Result<Sexp, Failure> {
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
                items.push(parse(bytes, pos, depth + 1)?);
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
        Ok(Sexp::Atom(atom.into()))
    }
    let mut pos = 0;
    let value = parse(text.as_bytes(), &mut pos, 0)?;
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
    let Sexp::List(entries) = parse_sexp(text)? else {
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
            Type::Unit => return Err(Failure::Error("unexpected unit solver variable".into())),
        };
        assignments.push(
            json!({"parameter":index,"symbol":name,"type":params[index].as_str(),"value":value}),
        );
    }
    Ok(json!({"replayed":false,"assignments":assignments}))
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
        params: &[Type],
        deadline: Instant,
        transcript: &mut String,
        max_bytes: usize,
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
        let symbols: Vec<_> = params
            .iter()
            .enumerate()
            .filter(|(_, ty)| **ty != Type::Unit)
            .map(|(i, _)| format!("p{i}"))
            .collect();
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
            model(remainder, params)?
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
        _: &[Type],
        _: Instant,
        _: &mut String,
        _: usize,
    ) -> Result<Answer, Failure> {
        Err(Failure::Unsupported(
            "solver process control is supported on Unix hosts".into(),
        ))
    }
}
