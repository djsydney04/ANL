//! Opt-in, solver-trusted verification of acyclic source programs.
mod formula;
mod loops;
mod solver;
mod state;

use crate::{
    diagnostic::{Diagnostic, Span},
    types::Program,
};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::{
    fs::OpenOptions,
    io::Read,
    path::{Path, PathBuf},
    time::{Duration, Instant},
};

const MAX_NODES: usize = 100_000;
const MAX_QUERY_BYTES: usize = 1_048_576;
const MAX_TOTAL_QUERY_BYTES: usize = 16_777_216;
const MAX_QUERIES: usize = 1024;
const SCHEMA: &str = "apl-verify-v0";
#[derive(Clone, Copy, PartialEq, Eq)]
enum Route {
    Pure,
    State,
    Loops,
}

#[derive(Clone, Debug)]
pub struct VerifyOptions {
    pub solver: PathBuf,
    pub timeout_ms: u64,
}
impl Default for VerifyOptions {
    fn default() -> Self {
        Self {
            solver: "z3".into(),
            timeout_ms: 30_000,
        }
    }
}
#[derive(Debug)]
pub struct VerificationReport {
    data: Value,
    exit: u8,
}
impl VerificationReport {
    pub fn json(&self) -> &Value {
        &self.data
    }
    pub fn exit_code(&self) -> u8 {
        self.exit
    }
    pub fn human(&self) -> String {
        let mut text = format!(
            "{}: {} obligations; trust={}; contracts erased during ordinary execution",
            self.data["status"].as_str().unwrap_or("error"),
            self.data["obligations"].as_array().map_or(0, Vec::len),
            self.data["trust"].as_str().unwrap_or("not_established")
        );
        if let Some(message) = self.data["message"].as_str() {
            text.push_str(&format!("\n{message}"));
        }
        if let Some(obligations) = self.data["obligations"].as_array() {
            for item in obligations {
                if item["status"] != "verified" {
                    text.push_str(&format!(
                        "\n{}:{}:{}: {}: {} ({})",
                        item["location"]["path"].as_str().unwrap_or("<source>"),
                        item["location"]["line"],
                        item["location"]["column"],
                        item["function"].as_str().unwrap_or("<function>"),
                        item["kind"].as_str().unwrap_or("obligation"),
                        item["status"].as_str().unwrap_or("error")
                    ));
                    if let Some(message) = item["message"].as_str() {
                        text.push_str(&format!(": {message}"));
                    }
                }
            }
        }
        text
    }
    pub fn source_error(error: &Diagnostic) -> Self {
        let exit = if error.infrastructure {
            4
        } else if error.resource_limit {
            3
        } else {
            1
        };
        Self {
            data: json!({"schema":SCHEMA,"semantic_revision":null,"status":"error","trust":"smt-trusted","type_checked":false,"tested":false,"dynamic_checks":false,"compiler":null,"solver":null,"sources":null,"functions":null,"obligations":[],"message":error.render("<source>", ""),"source_error":true,"resource_limit":error.resource_limit}),
            exit,
        }
    }
}
#[derive(Debug)]
enum Failure {
    Error(String),
    Unknown(String),
    Unsupported(String),
}
impl Failure {
    fn status(&self) -> &'static str {
        match self {
            Self::Error(_) => "error",
            Self::Unknown(_) => "unknown",
            Self::Unsupported(_) => "unsupported",
        }
    }
    fn message(&self) -> &str {
        match self {
            Self::Error(s) | Self::Unknown(s) | Self::Unsupported(s) => s,
        }
    }
}
fn rank(status: &str) -> usize {
    match status {
        "error" => 5,
        "failed" => 4,
        "unsupported" => 3,
        "unknown" => 2,
        "not_requested" => 1,
        _ => 0,
    }
}
fn combine(report: &mut VerificationReport, status: &str) {
    if rank(status) > rank(report.data["status"].as_str().unwrap_or("verified")) {
        report.data["status"] = json!(status);
    }
    report.exit = match report.data["status"].as_str().unwrap_or("error") {
        "verified" => 0,
        "failed" => 5,
        "unknown" => 6,
        "unsupported" | "not_requested" => 7,
        _ => 4,
    };
}
fn fail(report: &mut VerificationReport, error: Failure) {
    combine(report, error.status());
    report.data["message"] = json!(error.message());
}
fn path_hex(path: &Path) -> String {
    path.as_os_str()
        .as_encoded_bytes()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}
fn sha(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}
fn hash_file(path: &Path, deadline: Instant) -> Result<String, Failure> {
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.custom_flags(nix::fcntl::OFlag::O_NONBLOCK.bits());
    }
    let mut file = options
        .open(path)
        .map_err(|e| Failure::Error(format!("cannot hash {}: {e}", path.display())))?;
    if !file
        .metadata()
        .map_err(|e| Failure::Error(e.to_string()))?
        .is_file()
    {
        return Err(Failure::Error("tool identity is not a regular file".into()));
    }
    let mut hasher = Sha256::new();
    let mut bytes = [0; 65_536];
    loop {
        if Instant::now() >= deadline {
            return Err(Failure::Unknown(
                "verification deadline exceeded while hashing tools".into(),
            ));
        }
        let n = file
            .read(&mut bytes)
            .map_err(|e| Failure::Error(e.to_string()))?;
        if n == 0 {
            break;
        }
        hasher.update(&bytes[..n]);
    }
    Ok(format!("{:x}", hasher.finalize()))
}
fn location(program: &Program, span: Span) -> Value {
    if let Some(source) = program.sources.get(span.source_id) {
        let offset = span.start.min(source.text.len());
        let mut start = offset;
        while !source.text.is_char_boundary(start) {
            start -= 1;
        }
        let prefix = &source.text[..start];
        json!({"path":source.path.to_string_lossy(),"path_bytes_hex":path_hex(&source.path),"source_id":span.source_id,"start":span.start,"end":span.end,"line":prefix.bytes().filter(|b| *b == b'\n').count()+1,"column":prefix.rsplit('\n').next().unwrap_or("").chars().count()+1})
    } else {
        json!({"source_id":span.source_id,"start":span.start,"end":span.end})
    }
}

/// Verify the exact retained source graph; saved reports are never proof inputs.
pub fn verify_file(
    path: impl AsRef<Path>,
    options: &VerifyOptions,
) -> Result<VerificationReport, Diagnostic> {
    if options.timeout_ms == 0 || options.timeout_ms > 600_000 {
        let mut error = Diagnostic::new(
            Span::default(),
            "verification timeout must be in 1..600000 milliseconds",
        );
        error.infrastructure = true;
        return Err(error);
    }
    let program = crate::compile_file(path)?;
    if program.has_memory() {
        let contracts = program
            .contracts
            .as_ref()
            .expect("checked source contracts");
        return Ok(VerificationReport {
            data: json!({
                "schema":"anl-verify-v4", "semantic_revision":crate::memory::SEMANTIC_REVISION,
                "verification_revision":"anl-owned-buffers-unsupported-v1", "status":"unsupported", "trust":"not_established",
                "scope":{"functions":"all_loaded","arithmetic_safety":false,"partial_correctness":false,"termination_proved":false,"native_correctness":false,"model_proof":null,"fragment":"owned_buffers_unsupported"},
                "type_checked":true,"tested":false,"dynamic_checks":false,"contracts_erased":true,
                "compiler":null,"solver":null,"limits":{},"obligations":[],
                "sources":program.sources.iter().enumerate().map(|(id,s)|json!({"id":id,"path":s.path.to_string_lossy(),"path_bytes_hex":path_hex(&s.path),"sha256":sha(s.text.as_bytes()),"bytes":s.text.len()})).collect::<Vec<_>>(),
                "functions":program.functions.iter().enumerate().map(|(i,f)| json!({"id":i,"name":contracts[i].source_name,"lowered_name":f.name,"parameters":contracts[i].param_names,"parameter_types":f.params,"view":f.view.map(|v|json!({"mode":v.as_str(),"name":contracts[i].view_name})),"result":f.result,"location":location(&program,f.span),"requires":contracts[i].requires.len(),"ensures":contracts[i].ensures.len()})).collect::<Vec<_>>(),
                "message":"contract verification does not support buffers or views; type checking is not a contract proof"
            }),
            exit: 7,
        });
    }
    let products = loops::has_products(&program);

    let deadline = Instant::now() + Duration::from_millis(options.timeout_ms);
    let route = if products || loops::contains(&program) {
        Route::Loops
    } else if program.has_local_state() {
        Route::State
    } else {
        Route::Pure
    };
    let stateful = route != Route::Pure;
    let loop_route = route == Route::Loops;
    let mut state_budget = formula::StateBudget::new(deadline);
    let mut report = VerificationReport {
        data: json!({
            "schema":SCHEMA,"semantic_revision":program.semantic_revision(),"status":"verified","trust":"smt-trusted",
            "scope":{"functions":"all_loaded","arithmetic_safety":true,"partial_correctness":true,"termination_proved":false,"model_proof":"See formal/PROOFS.md; model proofs do not certify Rust generation or SMT encoding","native_correctness":false},
            "type_checked":true,"tested":false,"dynamic_checks":false,"contracts_erased":true,
            "limits":{"timeout_ms":options.timeout_ms,"expanded_nodes":MAX_NODES,"expansion_depth":256,"queries":MAX_QUERIES,"query_bytes":MAX_QUERY_BYTES,"total_query_bytes":MAX_TOTAL_QUERY_BYTES,"solver_stdout_bytes":1_048_576,"solver_stderr_bytes":65_536},
            "compiler":null,"solver":null,"sources":program.sources.iter().enumerate().map(|(id,s)|json!({"id":id,"path":s.path.to_string_lossy(),"path_bytes_hex":path_hex(&s.path),"sha256":sha(s.text.as_bytes()),"bytes":s.text.len()})).collect::<Vec<_>>(),
            "functions":[],"obligations":[],"message":null
        }),
        exit: 0,
    };
    if stateful {
        report.data["schema"] = json!("apl-verify-v1");
        report.data["verification_revision"] = json!("apl-state-verify-v1");
        report.data["scope"]["fragment"] = json!("loop_free_local_state_acyclic");
        report.data["limits"]["symbolic_work"] = json!(formula::MAX_SYMBOLIC_WORK);
        report.data["limits"]["arena_nodes"] = json!(formula::MAX_ARENA_NODES);
        report.data["expanded_nodes"] = json!(0);
    }
    if loop_route {
        report.data["verification_revision"] = json!("apl-loop-verify-v1");
        report.data["scope"]["fragment"] = json!("invariant_local_state_acyclic");
        report.data["limits"]["head_symbols"] = json!(4096);
        report.data["loop_policy"] = json!({"fresh_head":"all_visible_mutable_non_unit","query_grouping":"exact_guarded_conjunction","head_models":"abstract_mathematical_assignments"});
        report.data["source_loop_metadata_complete"] = json!(false);
        report.data["expansions"] = json!([]);
        report.data["loop_occurrences"] = json!([]);
    }
    if products {
        report.data["schema"] = json!("anl-verify-v3");
        report.data["verification_revision"] = json!("anl-flat-products-verify-v1");
        report.data["scope"]["fragment"] = json!("invariant_flat_products_acyclic");
        report.data["scope"]["model_proof"] = json!("APL.ProductFlow.contract_queries_sound");
        report.data["scope"]["proof_gaps"] = json!([
            "Rust generation",
            "source annotation correspondence",
            "SMT encoding and solver answers",
            "native execution",
            "termination",
            "generation completeness under production budgets"
        ]);
        report.data["loop_policy"]["fresh_head"] = json!("all_visible_mutable_non_unit_fields");
        report.data["parameter_layout"] = json!({"order":"source_parameter_then_field","unit_slots":"reserved_without_smt_variable","head_logical_identity":"initial_logical_bound_plus_head_index_minus_head_display_start"});
    }
    let Some(contracts) = program.contracts.as_ref() else {
        fail(
            &mut report,
            if loop_route {
                Failure::Unsupported("source contracts are absent".into())
            } else {
                Failure::Error("source contracts are absent".into())
            },
        );
        return Ok(report);
    };
    if contracts.len() != program.functions.len() {
        fail(
            &mut report,
            Failure::Error("source contract table length mismatch".into()),
        );
        return Ok(report);
    }
    if products {
        let function_records = (|| -> Result<Vec<Value>, Failure> {
            let mut records = Vec::new();
            state_budget.reserve(&mut records, program.functions.len())?;
            for (i, f) in program.functions.iter().enumerate() {
                let width = |ty: &crate::types::Type| match ty {
                    crate::types::Type::Tuple(shape) => shape.fields().len(),
                    _ => 1,
                };
                let fields = f.params.iter().map(width).sum::<usize>() + width(&f.result);
                state_budget.charge(
                    12 + fields
                        + contracts[i].source_name.len()
                        + f.name.len()
                        + contracts[i]
                            .param_names
                            .iter()
                            .map(String::len)
                            .sum::<usize>(),
                )?;
                records.push(json!({"id":i,"name":contracts[i].source_name,"lowered_name":f.name,"parameters":contracts[i].param_names,"parameter_types":f.params,"result":f.result,"location":location(&program,f.span),"requires":contracts[i].requires.len(),"ensures":contracts[i].ensures.len()}));
            }
            Ok(records)
        })();
        match function_records {
            Ok(records) => report.data["functions"] = Value::Array(records),
            Err(error) => {
                fail(&mut report, error);
                return Ok(report);
            }
        }
    } else {
        report.data["functions"] = json!(program.functions.iter().enumerate().map(|(i,f)| json!({"id":i,"name":contracts[i].source_name,"lowered_name":f.name,"parameters":contracts[i].param_names,"parameter_types":f.params.iter().map(|p|p.as_str()).collect::<Vec<_>>(),"result":f.result.as_str(),"location":location(&program,f.span),"requires":contracts[i].requires.len(),"ensures":contracts[i].ensures.len()})).collect::<Vec<_>>());
    }
    if loop_route {
        for function in report.data["functions"].as_array_mut().expect("functions") {
            function["invariant_clauses"] = Value::Null;
            function["loops"] = Value::Null;
            function["bindings"] = Value::Null;
        }
    }
    if program.functions.is_empty() {
        combine(&mut report, "not_requested");
        report.data["message"] = json!("no functions were supplied; nothing was verified");
        return Ok(report);
    }
    let supported = if loop_route {
        loops::preflight(&program, &mut report, &mut state_budget)
    } else {
        formula::supported(&program)
            .and_then(|()| formula::acyclic(&program))
            .map(|()| Vec::new())
    };
    let layouts = match supported {
        Ok(layouts) => layouts,
        Err(error) => {
            fail(&mut report, error);
            return Ok(report);
        }
    };
    let compiler = match std::env::current_exe()
        .map_err(|e| Failure::Error(e.to_string()))
        .and_then(|p| hash_file(&p, deadline).map(|h| (p, h)))
    {
        Ok(identity) => identity,
        Err(error) => {
            fail(&mut report, error);
            return Ok(report);
        }
    };
    report.data["compiler"] = json!({"version":env!("CARGO_PKG_VERSION"),"executable":compiler.0.to_string_lossy(),"executable_path_bytes_hex":path_hex(&compiler.0),"sha256":compiler.1});
    let solver = match solver::Solver::discover(&options.solver, deadline) {
        Ok(s) => s,
        Err(error) => {
            fail(&mut report, error);
            return Ok(report);
        }
    };
    report.data["solver"] = json!({"executable":solver.path.to_string_lossy(),"executable_path_bytes_hex":path_hex(&solver.path),"sha256":solver.hash,"version":solver.version,"arguments":["-in","-smt2"]});
    let mut expanded = 0;
    let mut queries = 0;
    let mut bytes = 0;
    let result: Result<(), Failure> = (|| {
        for (id, function) in program.functions.iter().enumerate() {
            if Instant::now() >= deadline {
                return Err(Failure::Unknown("verification deadline exceeded".into()));
            }
            let mut generator = if stateful {
                formula::Generator::with_state_budget(&program, &mut expanded, &mut state_budget)
            } else {
                formula::Generator::new(&program, &mut expanded)
            };
            let (pending, heads) = if loop_route {
                let artifact = loops::obligations(&mut generator, id, &mut report, &layouts)?;
                (artifact.pending, artifact.heads)
            } else {
                let pending = if stateful {
                    state::obligations(&mut generator, id)?
                } else {
                    formula::obligations(&mut generator, id)?
                };
                (
                    pending
                        .into_iter()
                        .map(|pending| loops::LoopPending {
                            pending,
                            checks: Value::Null,
                        })
                        .collect(),
                    Vec::new(),
                )
            };
            for entry in pending {
                let obligation = entry.pending;
                queries += 1;
                if queries > MAX_QUERIES {
                    return Err(Failure::Unknown("verification exceeds 1024 queries".into()));
                }
                let remaining = deadline
                    .checked_duration_since(Instant::now())
                    .ok_or_else(|| Failure::Unknown("verification deadline exceeded".into()))?;
                let script = generator.arena.render(
                    &function.params,
                    obligation.assertion,
                    remaining.as_millis(),
                )?;
                if bytes + script.len() > MAX_TOTAL_QUERY_BYTES {
                    return Err(Failure::Unknown(
                        "verification exceeds 16777216 query bytes".into(),
                    ));
                }
                let mut item = json!({"id":queries-1,"function_id":id,"function":contracts[id].source_name,"kind":obligation.kind,"location":location(&program,obligation.span),"expected_solver_status":if obligation.expected_sat {"sat"}else{"unsat"},"trust":"smt-trusted","query":script,"query_sha256":sha(script.as_bytes()),"status":"unknown","query_complete":false,"solver_status":null,"model":null,"message":null});
                let model_symbols = if loop_route {
                    let symbols = loops::manifest(
                        &mut generator,
                        &function.params,
                        &heads,
                        obligation.assertion,
                    )?;
                    generator.arena.work(symbols.len() * 4)?;
                    item["model_symbols"] = json!(symbols.iter().map(|symbol|json!({"symbol":symbol.name,"type":symbol.ty.as_str(),"origin":symbol.origin})).collect::<Vec<_>>());
                    item["query_assertion"] = json!(format!("n{}", obligation.assertion));
                    item["checks"] = entry.checks;
                    symbols
                } else {
                    Vec::new()
                };
                if stateful && !loop_route {
                    generator.arena.work(function.params.len())?;
                    let mut symbols = Vec::new();
                    for (i, ty) in function.params.iter().enumerate() {
                        generator.arena.work(0)?;
                        if *ty != crate::types::Type::Unit {
                            symbols.push(json!({"symbol":format!("p{i}"),"type":ty.as_str(),"origin":{"kind":"parameter","index":i}}));
                        }
                    }
                    item["model_symbols"] = json!(symbols);
                }
                let attempt = if loop_route {
                    solver.query_symbols(
                        &script,
                        &model_symbols,
                        deadline,
                        MAX_QUERY_BYTES.min(MAX_TOTAL_QUERY_BYTES - bytes),
                        generator.arena.budget()?,
                    )
                } else {
                    solver.query(
                        &script,
                        &function.params,
                        deadline,
                        MAX_QUERY_BYTES.min(MAX_TOTAL_QUERY_BYTES - bytes),
                    )
                };
                bytes += attempt.transcript.len();
                item["query_sha256"] = json!(sha(attempt.transcript.as_bytes()));
                item["query"] = json!(attempt.transcript);
                match attempt.outcome {
                    Ok(answer) => {
                        let status = if answer.status == "unknown" {
                            "unknown"
                        } else if (answer.status == "sat") == obligation.expected_sat {
                            "verified"
                        } else {
                            "failed"
                        };
                        item["query_complete"] = json!(true);
                        item["status"] = json!(status);
                        item["solver_status"] = json!(answer.status);
                        item["model"] = answer.model;
                        if status == "failed" {
                            item["message"] = json!(if obligation.expected_sat {
                                "preconditions are unsatisfiable"
                            } else if model_symbols.iter().any(|symbol| symbol.head.is_some()) {
                                "solver supplied an unreplayed abstract candidate counterexample"
                            } else {
                                "solver supplied an unreplayed candidate counterexample"
                            });
                        }
                        combine(&mut report, status);
                    }
                    Err(error) => {
                        item["status"] = json!(error.status());
                        item["message"] = json!(error.message());
                        report.data["obligations"]
                            .as_array_mut()
                            .expect("obligations array")
                            .push(item);
                        return Err(error);
                    }
                }
                report.data["obligations"]
                    .as_array_mut()
                    .expect("obligations array")
                    .push(item);
            }
        }
        Ok(())
    })();
    if let Err(error) = result {
        fail(&mut report, error);
    }
    if Instant::now() < deadline {
        for (path, expected) in [(&compiler.0, &compiler.1), (&solver.path, &solver.hash)] {
            match hash_file(path, deadline) {
                Ok(actual) if actual == *expected => {}
                Ok(_) => fail(
                    &mut report,
                    Failure::Error("tool executable changed during verification".into()),
                ),
                Err(error) => fail(&mut report, error),
            }
        }
    } else {
        fail(
            &mut report,
            Failure::Unknown(
                "verification deadline exceeded before final tool identity check".into(),
            ),
        );
    }
    report.data["expanded_nodes"] = json!(expanded);
    if products {
        if let Err(error) = state_budget.charge(6) {
            fail(&mut report, error);
        }
        report.data["resources"] = state_budget.usage();
    }
    Ok(report)
}
