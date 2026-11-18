//! Closed RV64IM instruction descriptors and boot-profile exclusions.
use crate::text::elf::{ErrorClass, StructuralError};

type Result<T> = std::result::Result<T, StructuralError>;
fn fail<T>(class: ErrorClass, reason: &'static str) -> Result<T> {
    Err(StructuralError { class, reason })
}
fn invalid<T>(reason: &'static str) -> Result<T> {
    fail(ErrorClass::Infrastructure, reason)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op {
    Nop,
    Lui,
    Auipc,
    Addi,
    Slti,
    Sltiu,
    Xori,
    Ori,
    Andi,
    Slli,
    Srli,
    Srai,
    Addiw,
    Slliw,
    Srliw,
    Sraiw,
    Add,
    Sub,
    Sll,
    Slt,
    Sltu,
    Xor,
    Srl,
    Sra,
    Or,
    And,
    Addw,
    Subw,
    Sllw,
    Srlw,
    Sraw,
    Mul,
    Mulh,
    Mulhsu,
    Mulhu,
    Div,
    Divu,
    Rem,
    Remu,
    Mulw,
    Divw,
    Divuw,
    Remw,
    Remuw,
    Lb,
    Lh,
    Lw,
    Ld,
    Lbu,
    Lhu,
    Lwu,
    Sb,
    Sh,
    Sw,
    Sd,
    Beq,
    Bne,
    Blt,
    Bge,
    Bltu,
    Bgeu,
    Jal,
    Jalr,
    Csrrw,
    Csrrs,
    Csrrc,
    Csrrwi,
    Csrrsi,
    Csrrci,
    Fence,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CsrSource {
    Register(u8),
    Immediate(u8),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Operands {
    None,
    Upper { rd: u8, immediate: i64 },
    Immediate { rd: u8, rs1: u8, immediate: i64 },
    Registers { rd: u8, rs1: u8, rs2: u8 },
    Load { rd: u8, base: u8, offset: i64 },
    Store { source: u8, base: u8, offset: i64 },
    Branch { rs1: u8, rs2: u8, displacement: i64 },
    Jump { rd: u8, displacement: i64 },
    Indirect { rd: u8, base: u8, offset: i64 },
    Csr { rd: u8, csr: u16, source: CsrSource },
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Registers {
    pub reads: u32,
    pub writes: u32,
    pub discarded_result: bool,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Effect {
    None,
    Load { bytes: u8, sign_extend: bool },
    Store { bytes: u8 },
    Csr { reads: bool, writes: bool },
    Fence,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Decoded {
    pub operation: Op,
    pub operands: Operands,
    pub registers: Registers,
    /// Arithmetic width before XLEN extension; W results sign-extend from 32.
    pub result_bits: Option<u8>,
    pub effect: Effect,
}

fn signed(value: u32, bits: u32) -> i64 {
    i64::from(((value << (32 - bits)) as i32) >> (32 - bits))
}
fn bit(reg: u8) -> u32 {
    if reg == 0 { 0 } else { 1_u32 << reg }
}
fn register_use(operands: Operands) -> Registers {
    let (reads, destination) = match operands {
        Operands::None => (0, None),
        Operands::Upper { rd, .. } | Operands::Jump { rd, .. } => (0, Some(rd)),
        Operands::Immediate { rd, rs1, .. } => (bit(rs1), Some(rd)),
        Operands::Registers { rd, rs1, rs2 } => (bit(rs1) | bit(rs2), Some(rd)),
        Operands::Load { rd, base, .. } | Operands::Indirect { rd, base, .. } => {
            (bit(base), Some(rd))
        }
        Operands::Store { source, base, .. } => (bit(source) | bit(base), None),
        Operands::Branch { rs1, rs2, .. } => (bit(rs1) | bit(rs2), None),
        Operands::Csr { rd, source, .. } => (
            match source {
                CsrSource::Register(r) => bit(r),
                CsrSource::Immediate(_) => 0,
            },
            Some(rd),
        ),
    };
    Registers {
        reads,
        writes: destination.map(bit).unwrap_or(0),
        discarded_result: destination == Some(0),
    }
}

/// Describes a word; does not compute values, targets, ABI or site authority.
pub fn decode(raw: u32) -> Result<Decoded> {
    use Op::*;
    if raw & 3 != 3 || raw & 0x1f == 0x1f {
        return invalid("non-32-bit instruction is forbidden");
    }
    let opcode = raw & 127;
    let rd = ((raw >> 7) & 31) as u8;
    let rs1 = ((raw >> 15) & 31) as u8;
    let rs2 = ((raw >> 20) & 31) as u8;
    let f3 = (raw >> 12) & 7;
    let f7 = raw >> 25;
    let i = signed(raw >> 20, 12);
    let mut effect = Effect::None;
    let mut result_bits = Some(64);
    let mut base_hint = false;
    let (operation, operands) = match opcode {
        0x37 | 0x17 => {
            base_hint = rd == 0;
            (
                if opcode == 0x37 { Lui } else { Auipc },
                Operands::Upper {
                    rd,
                    immediate: i64::from((raw & 0xffff_f000) as i32),
                },
            )
        }
        0x13 | 0x1b => {
            let word = opcode == 0x1b;
            let op = if word {
                result_bits = Some(32);
                match (f3, f7) {
                    (0, _) => Addiw,
                    (1, 0) => Slliw,
                    (5, 0) => Srliw,
                    (5, 32) => Sraiw,
                    _ => return invalid("invalid word immediate operation"),
                }
            } else {
                match f3 {
                    0 => Addi,
                    2 => Slti,
                    3 => Sltiu,
                    4 => Xori,
                    6 => Ori,
                    7 => Andi,
                    1 if raw >> 26 == 0 => Slli,
                    5 if raw >> 26 == 0 => Srli,
                    5 if raw >> 26 == 16 => Srai,
                    _ => return invalid("invalid immediate operation"),
                }
            };
            let immediate = if matches!(op, Slli | Srli | Srai | Slliw | Srliw | Sraiw) {
                i64::from((raw >> 20) & if word { 31 } else { 63 })
            } else {
                i
            };
            base_hint = rd == 0;
            (op, Operands::Immediate { rd, rs1, immediate })
        }
        0x33 | 0x3b => {
            let word = opcode == 0x3b;
            let op = if word {
                result_bits = Some(32);
                match (f7, f3) {
                    (0, 0) => Addw,
                    (0, 1) => Sllw,
                    (0, 5) => Srlw,
                    (32, 0) => Subw,
                    (32, 5) => Sraw,
                    (1, 0) => Mulw,
                    (1, 4) => Divw,
                    (1, 5) => Divuw,
                    (1, 6) => Remw,
                    (1, 7) => Remuw,
                    _ => return invalid("invalid word register operation"),
                }
            } else {
                match (f7, f3) {
                    (0, 0) => Add,
                    (0, 1) => Sll,
                    (0, 2) => Slt,
                    (0, 3) => Sltu,
                    (0, 4) => Xor,
                    (0, 5) => Srl,
                    (0, 6) => Or,
                    (0, 7) => And,
                    (32, 0) => Sub,
                    (32, 5) => Sra,
                    (1, 0) => Mul,
                    (1, 1) => Mulh,
                    (1, 2) => Mulhsu,
                    (1, 3) => Mulhu,
                    (1, 4) => Div,
                    (1, 5) => Divu,
                    (1, 6) => Rem,
                    (1, 7) => Remu,
                    _ => return invalid("invalid register operation"),
                }
            };
            if op == Add && rd == 0 && rs1 == 0 && (2..=5).contains(&rs2) {
                return invalid("NTL hint is outside the profile");
            }
            base_hint = rd == 0 && f7 != 1;
            (op, Operands::Registers { rd, rs1, rs2 })
        }
        0x03 => {
            let (op, bytes, sign_extend) = match f3 {
                0 => (Lb, 1, true),
                1 => (Lh, 2, true),
                2 => (Lw, 4, true),
                3 => (Ld, 8, false),
                4 => (Lbu, 1, false),
                5 => (Lhu, 2, false),
                6 => (Lwu, 4, false),
                _ => return invalid("invalid load encoding"),
            };
            effect = Effect::Load { bytes, sign_extend };
            (
                op,
                Operands::Load {
                    rd,
                    base: rs1,
                    offset: i,
                },
            )
        }
        0x23 => {
            let (op, bytes) = match f3 {
                0 => (Sb, 1),
                1 => (Sh, 2),
                2 => (Sw, 4),
                3 => (Sd, 8),
                _ => return invalid("invalid store encoding"),
            };
            effect = Effect::Store { bytes };
            result_bits = None;
            (
                op,
                Operands::Store {
                    source: rs2,
                    base: rs1,
                    offset: signed(((raw >> 25) << 5) | ((raw >> 7) & 31), 12),
                },
            )
        }
        0x63 => {
            let op = match f3 {
                0 => Beq,
                1 => Bne,
                4 => Blt,
                5 => Bge,
                6 => Bltu,
                7 => Bgeu,
                _ => return invalid("invalid branch encoding"),
            };
            result_bits = None;
            let bits = ((raw >> 31) << 12)
                | (((raw >> 7) & 1) << 11)
                | (((raw >> 25) & 63) << 5)
                | (((raw >> 8) & 15) << 1);
            (
                op,
                Operands::Branch {
                    rs1,
                    rs2,
                    displacement: signed(bits, 13),
                },
            )
        }
        0x6f => {
            let bits = ((raw >> 31) << 20)
                | (((raw >> 12) & 255) << 12)
                | (((raw >> 20) & 1) << 11)
                | (((raw >> 21) & 1023) << 1);
            (
                Jal,
                Operands::Jump {
                    rd,
                    displacement: signed(bits, 21),
                },
            )
        }
        0x67 if f3 == 0 => (
            Jalr,
            Operands::Indirect {
                rd,
                base: rs1,
                offset: i,
            },
        ),
        0x73 => {
            let csr = (raw >> 20) as u16;
            let (op, source, reads, writes) = match f3 {
                1 => (Csrrw, CsrSource::Register(rs1), rd != 0, true),
                2 => (Csrrs, CsrSource::Register(rs1), true, rs1 != 0),
                3 => (Csrrc, CsrSource::Register(rs1), true, rs1 != 0),
                5 => (Csrrwi, CsrSource::Immediate(rs1), rd != 0, true),
                6 => (Csrrsi, CsrSource::Immediate(rs1), true, rs1 != 0),
                7 => (Csrrci, CsrSource::Immediate(rs1), true, rs1 != 0),
                _ => return invalid("system instruction is forbidden"),
            };
            let allowed = matches!(
                (op, csr, rd, rs1),
                (Csrrci, 0x100, 0, 2)
                    | (Csrrw, 0x104, 0, 0)
                    | (Csrrw, 0x105, 0, _)
                    | (Csrrs, 0x141..=0x143, _, 0)
            );
            if !allowed {
                return invalid("CSR form or mask is outside the profile");
            }
            effect = Effect::Csr { reads, writes };
            (op, Operands::Csr { rd, csr, source })
        }
        0x0f if raw == 0x0ff0_000f => {
            effect = Effect::Fence;
            result_bits = None;
            (Fence, Operands::None)
        }
        _ => return invalid("instruction encoding is outside the profile"),
    };
    if raw == 0x0000_0013 {
        return Ok(Decoded {
            operation: Nop,
            operands,
            registers: Registers::default(),
            result_bits: None,
            effect,
        });
    }
    if base_hint {
        return fail(
            ErrorClass::Unsupported,
            "base computational HINT is not implemented",
        );
    }
    let registers = register_use(operands);
    if (registers.reads | registers.writes) & ((1 << 3) | (1 << 4)) != 0 {
        return invalid("gp or tp register use is forbidden");
    }
    Ok(Decoded {
        operation,
        operands,
        registers,
        result_bits,
        effect,
    })
}
