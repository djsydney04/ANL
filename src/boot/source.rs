use super::{CheckedProgram, Operation, Primitive, Profile, check};
use crate::{
    diagnostic::{Diagnostic, Sources, Span},
    resolve,
    syntax::{self, Expr, ExprKind, Statement},
    word::WordWidth,
};

fn reserved(name: &str, span: Span) -> Result<(), Diagnostic> {
    if ["hw", "machine", "uart0", "boot_stack", "terminal_stack"].contains(&name)
        || name.starts_with("__hw_")
        || name.starts_with("__carrier_")
    {
        Err(Diagnostic::new(
            span,
            "identifier is reserved in boot source",
        ))
    } else {
        Ok(())
    }
}
fn ungroup(mut e: &Expr) -> &Expr {
    while let ExprKind::Group(value) = &e.kind {
        e = value;
    }
    e
}
fn name(e: &Expr, expected: &str) -> bool {
    matches!(&ungroup(e).kind, ExprKind::Name(n) if n == expected)
}
fn natural(e: &Expr) -> Option<u64> {
    if let ExprKind::Integer(s) = &ungroup(e).kind {
        let n = s.parse::<u64>().ok()?;
        (n.to_string() == *s).then_some(n)
    } else {
        None
    }
}
fn word(e: &Expr) -> Option<u64> {
    if let ExprKind::Word(s, WordWidth::U64) = &ungroup(e).kind {
        s.parse().ok()
    } else {
        None
    }
}
fn discover(
    e: &mut Expr,
    profile: Profile,
    count: usize,
    hardware_name: &str,
    hardware_id: usize,
    primitives: &mut Vec<Primitive>,
) -> Result<(), Diagnostic> {
    if let ExprKind::Call {
        name: call,
        arguments: args,
    } = &mut e.kind
    {
        if call.starts_with("__hw_") || call.starts_with("__carrier_") {
            return Err(Diagnostic::new(
                e.span,
                "generated functions are not source call targets",
            ));
        }
        if call.starts_with("hw::") {
            let op = match (call.as_str(), args.as_slice()) {
                ("hw::illegal_instruction", [authority])
                    if profile.allows_illegal_instruction() && name(authority, "machine") =>
                {
                    Some(Operation::IllegalInstruction { authority: 0 })
                }
                ("hw::read8", [device, offset]) if name(device, "uart0") => natural(offset)
                    .filter(|&n| n == 5)
                    .map(|offset| Operation::Read8 { region: 0, offset }),
                ("hw::write8", [device, offset, _]) if name(device, "uart0") => natural(offset)
                    .filter(|&n| n <= 4)
                    .map(|offset| Operation::Write8 { region: 0, offset }),
                ("hw::fence_io", [device]) if name(device, "uart0") => {
                    Some(Operation::Fence { region: 0 })
                }
                ("hw::csr_clear", [authority, register, mask])
                    if name(authority, "machine")
                        && name(register, "sstatus")
                        && word(mask) == Some(2) =>
                {
                    Some(Operation::CsrClear {
                        authority: 0,
                        register: "sstatus".into(),
                        mask: 2,
                    })
                }
                ("hw::csr_write", [authority, register, value])
                    if name(authority, "machine")
                        && name(register, "sie")
                        && word(value) == Some(0) =>
                {
                    Some(Operation::CsrWrite {
                        authority: 0,
                        register: "sie".into(),
                        value: 0,
                    })
                }
                ("hw::install_trap", [authority, handler])
                    if name(authority, "machine") && name(handler, hardware_name) =>
                {
                    Some(Operation::InstallTrap {
                        authority: 0,
                        handler: hardware_id as u64,
                    })
                }
                _ => None,
            }
            .ok_or_else(|| {
                Diagnostic::new(e.span, "invalid hardware operation or static selectors")
            })?;
            let i = if let Some(i) = primitives.iter().position(|p| p.operation == op) {
                i
            } else {
                let i = primitives.len();
                let id = count + i;
                primitives.push(Primitive {
                    id,
                    name: format!("__hw_{id}"),
                    params: op.params(),
                    result: op.result(),
                    effects: op.effects(),
                    operation: op.clone(),
                });
                i
            };
            *call = primitives[i].name.clone();
            if matches!(op, Operation::Write8 { .. }) {
                *args = args.split_off(2);
            } else {
                args.clear();
            }
        }
    }
    match &mut e.kind {
        ExprKind::Memory(_) => {
            return Err(Diagnostic::new(
                e.span,
                "memory operations are unavailable in the boot profile",
            ));
        }
        ExprKind::Call { arguments, .. } | ExprKind::Tuple(arguments) => {
            for a in arguments {
                discover(a, profile, count, hardware_name, hardware_id, primitives)?;
            }
        }
        ExprKind::Convert { operand, .. }
        | ExprKind::Unary { operand, .. }
        | ExprKind::Group(operand)
        | ExprKind::Project { value: operand, .. } => discover(
            operand,
            profile,
            count,
            hardware_name,
            hardware_id,
            primitives,
        )?,
        ExprKind::Binary { left, right, .. } => {
            discover(left, profile, count, hardware_name, hardware_id, primitives)?;
            discover(
                right,
                profile,
                count,
                hardware_name,
                hardware_id,
                primitives,
            )?;
        }
        ExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            for a in [condition, then_branch, else_branch] {
                discover(a, profile, count, hardware_name, hardware_id, primitives)?;
            }
        }
        ExprKind::Block { statements, tail } => {
            for statement in statements {
                match statement {
                    Statement::Let {
                        name, span, value, ..
                    } => {
                        reserved(name, *span)?;
                        discover(
                            value,
                            profile,
                            count,
                            hardware_name,
                            hardware_id,
                            primitives,
                        )?;
                    }
                    Statement::Assign { value, .. } | Statement::Discard(value) => discover(
                        value,
                        profile,
                        count,
                        hardware_name,
                        hardware_id,
                        primitives,
                    )?,
                    Statement::While {
                        condition, body, ..
                    } => {
                        discover(
                            condition,
                            profile,
                            count,
                            hardware_name,
                            hardware_id,
                            primitives,
                        )?;
                        discover(body, profile, count, hardware_name, hardware_id, primitives)?;
                    }
                }
            }
            if let Some(value) = tail {
                discover(
                    value,
                    profile,
                    count,
                    hardware_name,
                    hardware_id,
                    primitives,
                )?;
            }
        }
        _ => {}
    }
    Ok(())
}

pub(crate) fn check_source(
    mut file: syntax::File,
    sources: Sources,
) -> Result<CheckedProgram, Diagnostic> {
    let platform = file.platform.take().ok_or_else(|| {
        Diagnostic::new(
            Span::default(),
            "boot target requires a platform declaration",
        )
    })?;
    if !file.modules.is_empty() {
        return Err(Diagnostic::new(
            platform.span,
            "boot source cannot import modules",
        ));
    }
    let mut entries = [0; 3];
    for (i, name) in platform.entries.iter().enumerate() {
        entries[i] = file
            .functions
            .iter()
            .position(|f| &f.name == name)
            .ok_or_else(|| {
                Diagnostic::new(platform.span, "platform role names an undefined function")
            })?;
    }
    let count = file.functions.len();
    let mut effects = Vec::with_capacity(count);
    let mut primitives = Vec::new();
    for f in &mut file.functions {
        reserved(&f.name, f.span)?;
        if f.view.is_some() {
            return Err(Diagnostic::new(f.span, "boot functions cannot take views"));
        }
        for p in &f.params {
            reserved(&p.name, p.span)?;
        }
        for p in &f.ensures {
            reserved(&p.binder, p.binder_span)?;
        }
        let mut set = Vec::new();
        for (name, span) in f.effects.take().unwrap_or_default() {
            let id = match name.as_str() {
                "machine" => 0,
                "uart0" => 1,
                _ => return Err(Diagnostic::new(span, "unknown boot authority")),
            };
            if set.contains(&id) {
                return Err(Diagnostic::new(span, "duplicate boot authority"));
            }
            set.push(id);
        }
        set.sort_unstable();
        effects.push(set);
        discover(
            &mut f.body,
            platform.profile,
            count,
            &platform.entries[1],
            entries[1],
            &mut primitives,
        )?;
    }
    let ExprKind::Block { statements, .. } = &file.functions[entries[0]].body.kind else {
        unreachable!("function bodies are parsed blocks")
    };
    if statements.len() < 3 || statements[..3].iter().any(|s| !matches!(s, Statement::Discard(e) if matches!(ungroup(e).kind, ExprKind::Call { .. }))) {
        return Err(Diagnostic::new(file.functions[entries[0]].span, "boot initialization must be the first three statements"));
    }
    let signatures = primitives
        .iter()
        .map(|p| resolve::ExternalSignature {
            name: p.name.clone(),
            params: p.params.clone(),
            result: p.result,
        })
        .collect();
    let checked = resolve::check_functions(
        vec![resolve::Module {
            functions: file.functions,
            imports: vec![],
        }],
        signatures,
    )?;
    check::finish(
        platform.profile,
        checked.functions,
        effects,
        primitives,
        entries,
        sources,
        Some(checked.contracts),
    )
}
