//! Opt-in artifact export for local compiler validation.
use crate::{bounded::OutputError, types::Program};
use sha2::{Digest, Sha256};
use std::{fs, path::Path};
fn digest(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

/// Export the actual checked core and the same MIR used to emit the retained C.
pub fn export_bundle(source: &Path, destination: &Path) -> Result<(), OutputError> {
    use std::io::Write as _;
    let program =
        crate::compile_file(source).map_err(|e| e.render(&source.to_string_lossy(), ""))?;
    let entry = program
        .entry()
        .map_err(|e| e.render(&source.to_string_lossy(), ""))?;
    if !program.has_memory() {
        return Err("memory evidence requires a buffer-bearing program".into());
    }
    let core = format!("{}\n", crate::core::export(&program, entry)?);
    let mir = crate::mir::lower(&program, entry).map_err(|e| e.to_string())?;
    let mir_json = crate::mir::wire::export(&mir)?;
    crate::mir::wire::import(&mir_json).map_err(|e| e.to_string())?;
    let c = crate::codegen::emit_lowered(&mir, Some(crate::codegen::MAX_PRODUCT_C_BYTES))?;
    let (header, runtime) =
        crate::memory::runtime_sources(program.allocation_profile.expect("memory profile"));
    let parent = destination
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."))
        .canonicalize()
        .map_err(|e| e.to_string())?;
    let name = destination
        .file_name()
        .ok_or("bundle destination must name a directory")?;
    let destination = parent.join(name);
    if fs::symlink_metadata(&destination).is_ok() {
        return Err("bundle destination already exists".into());
    }
    let stage = crate::codegen::TempDir::new(&parent)?;
    let files = [
        ("core.json", core),
        ("mir.json", format!("{mir_json}\n")),
        ("program.c", c),
        ("runtime.h", header),
        ("runtime.c", runtime),
    ];
    let mut hashes = serde_json::Map::new();
    for (name, bytes) in &files {
        let mut file = fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(stage.0.join(name))
            .map_err(|e| e.to_string())?;
        file.write_all(bytes.as_bytes())
            .map_err(|e| e.to_string())?;
        hashes.insert(
            (*name).into(),
            serde_json::json!({"sha256":digest(bytes.as_bytes()),"bytes":bytes.len()}),
        );
    }
    let executable = std::env::current_exe().map_err(|e| e.to_string())?;
    let compiler = fs::read(&executable).map_err(|e| e.to_string())?;
    let manifest = serde_json::json!({"schema":"anl-memory-evidence-bundle-v1","semantic_revision":crate::memory::SEMANTIC_REVISION,"runtime":"default","allocation_profile":program.allocation_profile.unwrap().json(),"compiler":{"version":env!("CARGO_PKG_VERSION"),"sha256":digest(&compiler),"memory_evidence":true},"files":hashes,"sources":program.sources.iter().map(|s|serde_json::json!({"path_bytes_hex":s.path.as_os_str().as_encoded_bytes().iter().map(|b|format!("{b:02x}")).collect::<String>(),"sha256":digest(s.text.as_bytes()),"bytes":s.text.len()})).collect::<Vec<_>>()});
    fs::write(stage.0.join("manifest.json"), format!("{manifest}\n")).map_err(|e| e.to_string())?;
    fs::create_dir(&destination)
        .map_err(|e| format!("cannot reserve fresh bundle directory: {e}"))?;
    for name in files
        .iter()
        .map(|(name, _)| *name)
        .chain(std::iter::once("manifest.json"))
    {
        fs::hard_link(stage.0.join(name), destination.join(name))
            .map_err(|e| format!("incomplete evidence bundle: {e}"))?;
    }
    Ok(())
}

/// Validate a bounded raw MIR artifact independently of its producer.
pub fn validate_mir(text: &str) -> Result<(), crate::core::ImportError> {
    crate::mir::wire::import(text).map(|_| ())
}

pub(crate) fn profile(program: &Program) -> Result<crate::memory::AllocationProfile, String> {
    program
        .allocation_profile
        .ok_or_else(|| "missing memory profile".into())
}

use crate::{
    core::{self, StrictValue},
    eval::{EvalError, Value},
    types::{Expr, ExprKind, MemoryExpr},
};
use std::{collections::BTreeSet, fs::File, io::Read, path::PathBuf};
pub(crate) const MAX_TRACE_BYTES: usize = 8_388_608;
pub(crate) const MAX_EVENTS: usize = 65_536;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Site {
    pub function: usize,
    pub heap: usize,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Event {
    Request {
        ordinal: u64,
        site: Site,
        length: u64,
        success: bool,
    },
    Release {
        ordinal: u64,
        site: Site,
    },
    EmptyOpen {
        ordinal: u64,
        site: Site,
    },
    EmptyClose {
        ordinal: u64,
        site: Site,
    },
}
impl Event {
    fn json(self) -> serde_json::Value {
        let site = |s: Site| serde_json::json!({"function":s.function,"heap":s.heap});
        match self {
            Self::Request {
                ordinal,
                site: s,
                length,
                success,
            } => {
                serde_json::json!({"kind":"request","request":ordinal.to_string(),"site":site(s),"length":length.to_string(),"response":if success{"success"}else{"refused"}})
            }
            Self::Release { ordinal, site: s } => {
                serde_json::json!({"kind":"release","request":ordinal.to_string(),"site":site(s)})
            }
            Self::EmptyOpen { ordinal, site: s } => {
                serde_json::json!({"kind":"empty_open","empty":ordinal.to_string(),"site":site(s)})
            }
            Self::EmptyClose { ordinal, site: s } => {
                serde_json::json!({"kind":"empty_close","empty":ordinal.to_string(),"site":site(s)})
            }
        }
    }
}
fn message(e: impl std::fmt::Display) -> String {
    e.to_string()
}
fn canonical(v: &serde_json::Value) -> Result<u64, String> {
    let s = core::string(v).map_err(message)?;
    let n = s.parse::<u64>().map_err(message)?;
    if n.to_string() != s {
        return Err("noncanonical evidence natural".into());
    }
    Ok(n)
}
fn sites(program: &Program) -> BTreeSet<(usize, usize)> {
    fn scan(e: &Expr, f: usize, out: &mut BTreeSet<(usize, usize)>) {
        match &e.kind {
            ExprKind::Memory(m) => {
                if let MemoryExpr::Heap { site, .. } = m.as_ref() {
                    out.insert((f, *site));
                }
                for c in m.children() {
                    scan(c, f, out);
                }
            }
            ExprKind::Tuple(xs) => {
                for x in xs {
                    scan(x, f, out)
                }
            }
            ExprKind::Project { value, .. }
            | ExprKind::Assign { value, .. }
            | ExprKind::Unary { operand: value, .. } => scan(value, f, out),
            ExprKind::Let { value, body } | ExprKind::LetMut { value, body } => {
                scan(value, f, out);
                scan(body, f, out);
            }
            ExprKind::While { condition, body } => {
                scan(condition, f, out);
                scan(body, f, out);
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                scan(condition, f, out);
                scan(then_branch, f, out);
                scan(else_branch, f, out);
            }
            ExprKind::Binary { left, right, .. } => {
                scan(left, f, out);
                scan(right, f, out);
            }
            ExprKind::Call { arguments, .. } => {
                for a in arguments {
                    scan(a, f, out)
                }
            }
            _ => {}
        }
    }
    let mut out = BTreeSet::new();
    for (i, f) in program.functions.iter().enumerate() {
        scan(&f.body, i, &mut out);
    }
    out
}
fn completion(v: &serde_json::Value) -> Result<(), String> {
    let kind = v
        .get("kind")
        .and_then(serde_json::Value::as_str)
        .ok_or("missing replay completion")?;
    match kind {
        "value" => {
            let o = core::object(v, &["kind", "type", "value"]).map_err(message)?;
            if o["type"] != "i64" {
                return Err("entry replay value must be i64".into());
            }
            let s = core::string(&o["value"]).map_err(message)?;
            let n = s.parse::<i64>().map_err(message)?;
            if n.to_string() != s {
                return Err("noncanonical replay value".into());
            }
        }
        "trap" => {
            let o = core::object(v, &["kind", "trap"]).map_err(message)?;
            if !matches!(
                o["trap"].as_str(),
                Some(
                    "arithmetic_overflow"
                        | "division_by_zero"
                        | "invalid_length"
                        | "index_out_of_bounds"
                )
            ) {
                return Err("unknown replay trap".into());
            }
        }
        _ => return Err("only complete value or trap traces can be replayed".into()),
    }
    Ok(())
}
#[derive(Clone)]
struct Replay {
    events: Vec<Event>,
    completion: serde_json::Value,
}
fn parse_replay(text: &str, program: &Program) -> Result<Replay, String> {
    let StrictValue(v) = serde_json::from_str(text).map_err(message)?;
    let o = core::object(
        &v,
        &[
            "schema",
            "semantic_revision",
            "allocation_profile",
            "events",
            "completion",
        ],
    )
    .map_err(message)?;
    if o["schema"] != "anl-memory-trace-v1"
        || o["semantic_revision"] != crate::memory::SEMANTIC_REVISION
        || core::profile(&o["allocation_profile"]).map_err(message)? != profile(program)?
    {
        return Err("replay revision/profile mismatch".into());
    }
    completion(&o["completion"])?;
    let input = core::array(&o["events"]).map_err(message)?;
    if input.len() > MAX_EVENTS {
        return Err("replay event bound exceeded".into());
    }
    let allowed = sites(program);
    let mut next_request = 0;
    let mut next_empty = 0;
    let mut open = Vec::new();
    let mut events = Vec::new();
    events.try_reserve_exact(input.len()).map_err(message)?;
    open.try_reserve_exact(input.len()).map_err(message)?;
    for v in input {
        let tag = v
            .get("kind")
            .and_then(serde_json::Value::as_str)
            .ok_or("missing replay event tag")?;
        let fields: &[&str] = match tag {
            "request" => &["kind", "request", "site", "length", "response"],
            "release" => &["kind", "request", "site"],
            "empty_open" | "empty_close" => &["kind", "empty", "site"],
            _ => return Err("unknown replay event".into()),
        };
        let o = core::object(v, fields).map_err(message)?;
        let so = core::object(&o["site"], &["function", "heap"]).map_err(message)?;
        let site = Site {
            function: core::natural(&so["function"]).map_err(message)?,
            heap: core::natural(&so["heap"]).map_err(message)?,
        };
        if !allowed.contains(&(site.function, site.heap)) {
            return Err("replay site is absent from checked program".into());
        }
        let ordinal = canonical(
            &o[if tag.starts_with("empty") {
                "empty"
            } else {
                "request"
            }],
        )?;
        let event = match tag {
            "request" => {
                if ordinal != next_request {
                    return Err("nonconsecutive request ordinal".into());
                }
                next_request += 1;
                let length = canonical(&o["length"])?;
                if length == 0 || length > profile(program)?.max_cells() {
                    return Err("invalid replay request length".into());
                }
                let success = match o["response"].as_str() {
                    Some("success") => true,
                    Some("refused") => false,
                    _ => return Err("invalid replay response".into()),
                };
                if success {
                    open.push((false, ordinal, site));
                }
                Event::Request {
                    ordinal,
                    site,
                    length,
                    success,
                }
            }
            "release" => {
                if open.pop() != Some((false, ordinal, site)) {
                    return Err("release is not the current live owner".into());
                }
                Event::Release { ordinal, site }
            }
            "empty_open" => {
                if ordinal != next_empty {
                    return Err("nonconsecutive empty ordinal".into());
                }
                next_empty += 1;
                open.push((true, ordinal, site));
                Event::EmptyOpen { ordinal, site }
            }
            "empty_close" => {
                if open.pop() != Some((true, ordinal, site)) {
                    return Err("empty close is not the current live owner".into());
                }
                Event::EmptyClose { ordinal, site }
            }
            _ => unreachable!(),
        };
        events.push(event);
    }
    if o["completion"]["kind"] == "value" && !open.is_empty() {
        return Err("value replay retains owners".into());
    }
    Ok(Replay {
        events,
        completion: o["completion"].clone(),
    })
}
fn normalized(path: &Path) -> Result<PathBuf, String> {
    let parent = path
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."))
        .canonicalize()
        .map_err(message)?;
    let name = path.file_name().ok_or("path requires a final filename")?;
    Ok(parent.join(name))
}
fn resolved_final(path: &Path) -> Result<PathBuf, String> {
    let mut path = normalized(path)?;
    for _ in 0..32 {
        match fs::symlink_metadata(&path) {
            Ok(metadata) if metadata.file_type().is_symlink() => {
                let target = fs::read_link(&path).map_err(message)?;
                path = normalized(&if target.is_absolute() {
                    target
                } else {
                    path.parent().expect("normalized parent").join(target)
                })?;
            }
            Ok(_) => return Ok(path),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(path),
            Err(e) => return Err(message(e)),
        }
    }
    Err("evidence path symlink depth exceeded".into())
}
fn same_file(a: &Path, b: &Path) -> Result<bool, String> {
    if normalized(a)? == normalized(b)? || resolved_final(a)? == resolved_final(b)? {
        return Ok(true);
    }
    let metadata = |p: &Path| -> Result<Option<fs::Metadata>, String> {
        match fs::metadata(p) {
            Ok(m) => Ok(Some(m)),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(None),
            Err(e) => Err(message(e)),
        }
    };
    if let (Some(a), Some(b)) = (metadata(a)?, metadata(b)?) {
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt;
            return Ok(a.dev() == b.dev() && a.ino() == b.ino());
        }
        #[cfg(not(unix))]
        {
            let _ = (a, b);
        }
    }
    Ok(false)
}

pub struct EvidenceOptions {
    destination: PathBuf,
    replay_path: Option<PathBuf>,
    #[cfg(unix)]
    replay_identity: Option<(u64, u64)>,
    replay: Option<Replay>,
    profile: crate::memory::AllocationProfile,
}
impl EvidenceOptions {
    pub(crate) fn check_program(&self, program: &Program) -> Result<(), String> {
        if !program.has_memory() || program.allocation_profile != Some(self.profile) {
            return Err("evidence plan does not match checked memory profile".into());
        }
        Ok(())
    }
    pub fn from_environment(program: &Program) -> Result<Option<Self>, String> {
        if !program.has_memory() {
            return Ok(None);
        }
        let trace = std::env::var_os("ANL_MEMORY_TRACE");
        let replay = std::env::var_os("ANL_MEMORY_REPLAY");
        if trace.is_none() && replay.is_none() {
            return Ok(None);
        }
        let trace = trace
            .filter(|s| !s.is_empty())
            .ok_or("evidence replay requires a nonempty trace destination")?;
        let trace = Path::new(&trace);
        if !trace.is_absolute() {
            return Err("trace destination must be absolute".into());
        }
        let destination = normalized(trace)?;
        if destination.as_os_str().as_encoded_bytes().len() > 4096
            || destination.as_os_str().as_encoded_bytes().contains(&0)
        {
            return Err("trace path byte bound exceeded".into());
        }
        match fs::symlink_metadata(&destination) {
            Ok(_) => return Err("trace destination already exists".into()),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
            Err(e) => return Err(message(e)),
        }
        let mut replay_path = None;
        #[cfg(unix)]
        let mut replay_identity = None;
        let mut snapshot = None;
        if let Some(path) = replay {
            if path.is_empty() {
                return Err("empty replay path".into());
            }
            let path = Path::new(&path).canonicalize().map_err(message)?;
            if same_file(&destination, &path)? {
                return Err("trace/replay paths alias".into());
            }
            let mut open = fs::OpenOptions::new();
            open.read(true);
            #[cfg(unix)]
            {
                use std::os::unix::fs::OpenOptionsExt;
                open.custom_flags(nix::fcntl::OFlag::O_NONBLOCK.bits());
            }
            let file = open.open(&path).map_err(message)?;
            #[cfg(unix)]
            {
                use std::os::unix::fs::MetadataExt;
                let metadata = file.metadata().map_err(message)?;
                replay_identity = Some((metadata.dev(), metadata.ino()));
            }
            if !file.metadata().map_err(message)?.is_file() {
                return Err("replay is not a regular file".into());
            }
            let mut bytes = Vec::new();
            file.take(MAX_TRACE_BYTES as u64 + 1)
                .read_to_end(&mut bytes)
                .map_err(message)?;
            if bytes.len() > MAX_TRACE_BYTES {
                return Err("replay byte bound exceeded".into());
            }
            let text = std::str::from_utf8(&bytes).map_err(message)?;
            snapshot = Some(parse_replay(text, program)?);
            replay_path = Some(path);
        }
        Ok(Some(Self {
            destination,
            replay_path,
            #[cfg(unix)]
            replay_identity,
            replay: snapshot,
            profile: profile(program)?,
        }))
    }
    pub(crate) fn protect_destination(&self, path: &Path) -> Result<(), String> {
        #[cfg(unix)]
        if let (Some(identity), Ok(metadata)) = (self.replay_identity, fs::metadata(path)) {
            use std::os::unix::fs::MetadataExt;
            if identity == (metadata.dev(), metadata.ino()) {
                return Err("executable destination aliases captured replay file".into());
            }
        }
        if same_file(path, &self.destination)?
            || self
                .replay_path
                .as_ref()
                .is_some_and(|r| same_file(path, r).unwrap_or(true))
        {
            return Err("executable destination aliases evidence trace or replay".into());
        }
        Ok(())
    }
    pub(crate) fn session(&self) -> Result<Session, EvalError> {
        let file = fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&self.destination)
            .map_err(|e| {
                EvalError::Infrastructure(format!("cannot exclusively create trace: {e}"))
            })?;
        Ok(Session {
            file,
            profile: self.profile,
            replay: self.replay.clone(),
            events: Vec::new(),
            next_request: 0,
            next_empty: 0,
            bytes: 0,
        })
    }
}
pub(crate) struct Session {
    file: File,
    profile: crate::memory::AllocationProfile,
    replay: Option<Replay>,
    events: Vec<Event>,
    next_request: u64,
    next_empty: u64,
    bytes: usize,
}
impl Session {
    fn fail(reason: &str) -> EvalError {
        EvalError::Infrastructure(reason.into())
    }
    fn record(&mut self, event: Event) -> Result<(), EvalError> {
        if self.events.len() >= MAX_EVENTS {
            return Err(Self::fail("trace event bound exceeded"));
        }
        if self
            .replay
            .as_ref()
            .is_some_and(|r| r.events.get(self.events.len()) != Some(&event))
        {
            return Err(Self::fail("invalid replay event"));
        }
        let bytes = event.json().to_string().len() + 1;
        self.bytes = self
            .bytes
            .checked_add(bytes)
            .filter(|n| *n <= MAX_TRACE_BYTES)
            .ok_or_else(|| Self::fail("trace byte bound exceeded"))?;
        self.events
            .try_reserve(1)
            .map_err(|_| Self::fail("trace metadata allocation failed"))?;
        self.events.push(event);
        Ok(())
    }
    pub(crate) fn response(&self, site: Site, length: u64) -> Result<Option<bool>, EvalError> {
        if self.events.len() >= MAX_EVENTS {
            return Err(Self::fail("trace event bound exceeded"));
        }
        if let Some(r) = &self.replay {
            match r.events.get(self.events.len()) {
                Some(Event::Request {
                    ordinal,
                    site: s,
                    length: n,
                    success,
                }) if *ordinal == self.next_request && *s == site && *n == length => {
                    Ok(Some(*success))
                }
                _ => Err(Self::fail("invalid replay request")),
            }
        } else {
            Ok(None)
        }
    }
    pub(crate) fn request(
        &mut self,
        site: Site,
        length: u64,
        success: bool,
    ) -> Result<u64, EvalError> {
        let ordinal = self.next_request;
        self.record(Event::Request {
            ordinal,
            site,
            length,
            success,
        })?;
        self.next_request += 1;
        Ok(ordinal)
    }
    pub(crate) fn empty(&mut self, site: Site) -> Result<u64, EvalError> {
        let ordinal = self.next_empty;
        self.record(Event::EmptyOpen { ordinal, site })?;
        self.next_empty += 1;
        Ok(ordinal)
    }
    pub(crate) fn close(&mut self, site: Site, ordinal: u64, empty: bool) -> Result<(), EvalError> {
        self.record(if empty {
            Event::EmptyClose { ordinal, site }
        } else {
            Event::Release { ordinal, site }
        })
    }
    pub(crate) fn finish(mut self, result: Result<Value, EvalError>) -> Result<Value, EvalError> {
        use std::io::Write as _;
        let mut result = result;
        let completion = |r: &Result<Value, EvalError>| match r {
            Ok(Value::Integer(n)) => {
                serde_json::json!({"kind":"value","type":"i64","value":n.to_string()})
            }
            Ok(_) => serde_json::json!({"kind":"infrastructure","reason":"invalid entry value"}),
            Err(EvalError::Trap { kind, .. }) => {
                serde_json::json!({"kind":"trap","trap":kind.as_str()})
            }
            Err(EvalError::ResourceLimit { .. }) => serde_json::json!({"kind":"resource_limit"}),
            Err(EvalError::Infrastructure(reason)) => {
                serde_json::json!({"kind":"infrastructure","reason":reason.chars().take(200).collect::<String>()})
            }
            Err(EvalError::InvalidIr) => {
                serde_json::json!({"kind":"infrastructure","reason":"invalid checked execution"})
            }
        };
        let mut end = completion(&result);
        if !matches!(
            result,
            Err(EvalError::ResourceLimit { .. } | EvalError::Infrastructure(_))
        ) && self
            .replay
            .as_ref()
            .is_some_and(|r| r.events.len() != self.events.len() || r.completion != end)
        {
            result = Err(Self::fail("invalid replay completion"));
            end = completion(&result);
        }
        let trace = serde_json::json!({"schema":"anl-memory-trace-v1","semantic_revision":crate::memory::SEMANTIC_REVISION,"allocation_profile":self.profile.json(),"events":self.events.iter().map(|e|e.json()).collect::<Vec<_>>(),"completion":end});
        let mut b = crate::bounded::Buffer::new(Some(MAX_TRACE_BYTES), "trace byte bound exceeded");
        if let Err(e) = serde_json::to_writer(&mut b, &trace) {
            return Err(Self::fail(&format!("cannot encode trace: {e}")));
        }
        let text = match b.finish() {
            Ok(s) => s,
            Err(e) => return Err(Self::fail(&e.to_string())),
        };
        if let Err(e) = self
            .file
            .write_all(text.as_bytes())
            .and_then(|_| self.file.flush())
        {
            return Err(Self::fail(&format!("cannot write trace: {e}")));
        }
        result
    }
}

impl EvidenceOptions {
    pub(crate) fn native_config(&self) -> Result<String, OutputError> {
        use std::fmt::Write as _;
        let mut b = crate::bounded::Buffer::new(
            Some(MAX_TRACE_BYTES),
            "native evidence configuration exceeds 8388608 bytes",
        );
        let mut emit = || -> std::fmt::Result {
            b.write_str("static const unsigned char anl_destination[] = {")?;
            for byte in self.destination.as_os_str().as_encoded_bytes() {
                write!(b, "{byte},")?;
            }
            b.write_str("0};\n")?;
            let prefix = format!(
                "{{\"schema\":\"anl-memory-trace-v1\",\"semantic_revision\":\"{}\",\"allocation_profile\":{},\"events\":[",
                crate::memory::SEMANTIC_REVISION,
                self.profile.json()
            );
            b.write_str("static const char anl_prefix[] = {")?;
            for byte in prefix.bytes() {
                write!(b, "{byte},")?;
            }
            b.write_str("0};\n")?;
            let events = self
                .replay
                .as_ref()
                .map(|r| r.events.as_slice())
                .unwrap_or(&[]);
            writeln!(
                b,
                "static const unsigned anl_replay = {};\nstatic const size_t anl_expected_count = {};",
                usize::from(self.replay.is_some()),
                events.len()
            )?;
            b.write_str("static const anl_event anl_expected[] = {\n")?;
            if events.is_empty() {
                b.write_str("{0,0,0,0,0,0}\n")?;
            }
            for e in events {
                let (kind, ordinal, site, length, success) = match *e {
                    Event::Request {
                        ordinal,
                        site,
                        length,
                        success,
                    } => (1, ordinal, site, length, u8::from(success)),
                    Event::Release { ordinal, site } => (2, ordinal, site, 0, 0),
                    Event::EmptyOpen { ordinal, site } => (3, ordinal, site, 0, 0),
                    Event::EmptyClose { ordinal, site } => (4, ordinal, site, 0, 0),
                };
                writeln!(
                    b,
                    "{{{kind},UINT64_C({ordinal}),UINT64_C({}),UINT64_C({}),UINT64_C({length}),{success}}},",
                    site.function, site.heap
                )?;
            }
            b.write_str("};\n")?;
            let (kind, value, trap) = if let Some(r) = &self.replay {
                if r.completion["kind"] == "value" {
                    (
                        1,
                        r.completion["value"]
                            .as_str()
                            .expect("validated value")
                            .parse::<i64>()
                            .expect("validated i64"),
                        0,
                    )
                } else {
                    (
                        2,
                        0,
                        match r.completion["trap"].as_str().expect("validated trap") {
                            "arithmetic_overflow" => 1,
                            "division_by_zero" => 2,
                            "invalid_length" => 3,
                            "index_out_of_bounds" => 4,
                            _ => unreachable!(),
                        },
                    )
                }
            } else {
                (0, 0, 0)
            };
            let value = if value == i64::MIN {
                "(-INT64_C(9223372036854775807)-INT64_C(1))".to_owned()
            } else if value < 0 {
                format!("(-INT64_C({}))", -value)
            } else {
                format!("INT64_C({value})")
            };
            writeln!(
                b,
                "static const unsigned anl_completion_kind = {kind};\nstatic const int64_t anl_completion_value = {value};\nstatic const unsigned anl_completion_trap = {trap};"
            )
        };
        if emit().is_err() && !b.exhausted() {
            return Err("native evidence formatting failed".into());
        }
        b.finish()
    }
}
