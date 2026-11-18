use super::{CheckedProgram, Operation, Primitive, TailEdge};
use crate::{
    diagnostic::{Diagnostic, Sources, Span},
    syntax,
    types::{Expr, ExprKind, Function, FunctionContract, Type},
    word::WordWidth,
};
use std::collections::HashSet;

fn error(message: &str) -> Diagnostic {
    Diagnostic::new(Span::default(), message)
}
fn park(e: &Expr) -> bool {
    matches!(&e.kind, ExprKind::While { condition, body }
        if e.ty == Type::Unit && condition.ty == Type::Bool && body.ty == Type::Unit
        && matches!(condition.kind, ExprKind::Boolean(true)) && matches!(body.kind, ExprKind::Unit))
}
fn handler(e: &Expr) -> bool {
    matches!(&e.kind, ExprKind::Let { value, body }
        if e.ty == Type::Unit && park(value) && body.ty == Type::Unit && matches!(body.kind, ExprKind::Unit))
}
fn tail(e: &Expr) -> Option<Vec<TailEdge>> {
    if park(e) {
        return Some(Vec::new());
    }
    if let ExprKind::Let { value, body } | ExprKind::LetMut { value, body } = &e.kind {
        if let Some(mut p) = tail(value) {
            p.insert(0, TailEdge::Value);
            return Some(p);
        }
        if let Some(mut p) = tail(body) {
            p.insert(0, TailEdge::Body);
            return Some(p);
        }
    }
    None
}
fn calls(e: &Expr) -> Vec<usize> {
    let mut out = Vec::new();
    fn walk(e: &Expr, out: &mut Vec<usize>) {
        match &e.kind {
            ExprKind::Call {
                function,
                arguments,
            } => {
                out.push(*function);
                for a in arguments {
                    walk(a, out);
                }
            }
            ExprKind::Tuple(xs) => {
                for a in xs {
                    walk(a, out);
                }
            }
            ExprKind::Project { value, .. }
            | ExprKind::Assign { value, .. }
            | ExprKind::Unary { operand: value, .. }
            | ExprKind::Convert { operand: value, .. } => walk(value, out),
            ExprKind::Let { value, body } | ExprKind::LetMut { value, body } => {
                walk(value, out);
                walk(body, out);
            }
            ExprKind::While { condition, body } => {
                walk(condition, out);
                walk(body, out);
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                walk(condition, out);
                walk(then_branch, out);
                walk(else_branch, out);
            }
            ExprKind::Binary { left, right, .. } => {
                walk(left, out);
                walk(right, out);
            }
            _ => {}
        }
    }
    walk(e, &mut out);
    out
}
fn operation(primitives: &[Primitive], defined: usize, id: usize) -> Option<&Operation> {
    id.checked_sub(defined)
        .and_then(|i| primitives.get(i))
        .map(|p| &p.operation)
}
fn rest<'a>(
    mut e: &'a Expr,
    primitives: &[Primitive],
    defined: usize,
    hardware: usize,
) -> Option<&'a Expr> {
    let expected = [
        Operation::CsrClear {
            authority: 0,
            register: "sstatus".into(),
            mask: 2,
        },
        Operation::CsrWrite {
            authority: 0,
            register: "sie".into(),
            value: 0,
        },
        Operation::InstallTrap {
            authority: 0,
            handler: hardware as u64,
        },
    ];
    for expected in expected {
        let ExprKind::Let { value, body } = &e.kind else {
            return None;
        };
        let ExprKind::Call {
            function,
            arguments,
        } = &value.kind
        else {
            return None;
        };
        if e.ty != Type::Unit
            || value.ty != Type::Unit
            || !arguments.is_empty()
            || operation(primitives, defined, *function) != Some(&expected)
        {
            return None;
        }
        e = body;
    }
    Some(e)
}

pub(super) fn finish(
    profile: super::Profile,
    functions: Vec<Function>,
    effects: Vec<Vec<u64>>,
    primitives: Vec<Primitive>,
    entries: [usize; 3],
    sources: Sources,
    contracts: Option<Vec<FunctionContract>>,
) -> Result<CheckedProgram, Diagnostic> {
    let count = functions.len();
    if effects.len() != count
        || entries.iter().any(|&id| id >= count)
        || entries[0] == entries[1]
        || entries[0] == entries[2]
        || entries[1] == entries[2]
    {
        return Err(error("invalid boot role table"));
    }
    let mut names = HashSet::new();
    for f in &functions {
        if !syntax::identifier(&f.name)
            || f.name.starts_with("__hw_")
            || f.name.starts_with("__carrier_")
            || !names.insert(&f.name)
            || f.view.is_some()
        {
            return Err(error("invalid boot defined function"));
        }
        if f.body.any(&|e| matches!(e.kind, ExprKind::Memory(_))) {
            return Err(error(
                "memory operations are unavailable in the boot profile",
            ));
        }
    }
    for (i, p) in primitives.iter().enumerate() {
        if p.id != count + i
            || p.name != format!("__hw_{}", p.id)
            || !syntax::identifier(&p.name)
            || !p.operation.valid(profile, entries[1])
            || p.params != p.operation.params()
            || p.result != p.operation.result()
            || p.effects != p.operation.effects()
        {
            return Err(error("invalid boot primitive declaration"));
        }
    }
    let word = Type::Word(WordWidth::U64);
    let role_params = [
        vec![word, word],
        vec![word, word, word],
        vec![Type::Word(WordWidth::U8)],
    ];
    for (id, params) in entries.into_iter().zip(role_params) {
        if functions[id].params != params || functions[id].result != Type::Unit {
            return Err(error("invalid boot role signature"));
        }
    }
    if !handler(&functions[entries[1]].body) || !handler(&functions[entries[2]].body) {
        return Err(error(
            "trap handlers must contain exactly the terminal loop",
        ));
    }
    let mut all_calls = Vec::with_capacity(count);
    let mut first_uses = Vec::new();
    for (id, f) in functions.iter().enumerate() {
        let expected = if id == entries[0] {
            effects[id] == [0, 1]
        } else if entries[1..].contains(&id) {
            effects[id].is_empty()
        } else {
            effects[id].is_empty() || effects[id] == [1]
        };
        if !expected {
            return Err(error("invalid boot function effects"));
        }
        let body = if id == entries[0] {
            rest(&f.body, &primitives, count, entries[1]).ok_or_else(|| {
                error("boot entry requires the exact machine initialization prefix")
            })?
        } else {
            &f.body
        };
        for callee in calls(body) {
            if entries.contains(&callee) {
                return Err(error("ordinary calls cannot target a boot role"));
            }
            let required = if callee < count {
                &effects[callee]
            } else {
                let p = callee
                    .checked_sub(count)
                    .and_then(|i| primitives.get(i))
                    .ok_or_else(|| error("unknown boot call target"))?;
                if !p.operation.rest_allowed(profile) {
                    return Err(error("machine operations are confined to the boot prefix"));
                }
                &p.effects
            };
            if required.iter().any(|effect| !effects[id].contains(effect)) {
                return Err(error("callee effects exceed caller authority"));
            }
        }
        let targets = calls(&f.body);
        for &callee in &targets {
            if let Some(op) = operation(&primitives, count, callee)
                && !first_uses.contains(op)
            {
                first_uses.push(op.clone());
            }
        }
        all_calls.push(targets);
    }
    if first_uses
        != primitives
            .iter()
            .map(|p| p.operation.clone())
            .collect::<Vec<_>>()
    {
        return Err(error(
            "primitive table must match canonical first-use order",
        ));
    }
    // Iterative DFS avoids using the host call stack for a long acyclic function graph.
    let mut colors = vec![0u8; count];
    for start in 0..count {
        if colors[start] != 0 {
            continue;
        }
        let mut stack = vec![(start, 0)];
        colors[start] = 1;
        while let Some((id, next)) = stack.last_mut() {
            if *next == all_calls[*id].len() {
                colors[*id] = 2;
                stack.pop();
                continue;
            }
            let target = all_calls[*id][*next];
            *next += 1;
            if target >= count {
                continue;
            }
            if colors[target] == 1 {
                return Err(error("recursive calls are unavailable in the boot profile"));
            }
            if colors[target] == 0 {
                colors[target] = 1;
                stack.push((target, 0));
            }
        }
    }
    let tails = [
        tail(&functions[entries[0]].body)
            .ok_or_else(|| error("boot entry requires a designated terminal loop"))?,
        tail(&functions[entries[1]].body).expect("checked handler"),
        tail(&functions[entries[2]].body).expect("checked handler"),
    ];
    Ok(CheckedProgram {
        profile,
        functions,
        effects,
        primitives,
        entries,
        _tails: tails,
        _sources: sources,
        _contracts: contracts,
    })
}
