use crate::bounded::Buffer;
use std::fmt::{self, Write};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Helper {
    Add,
    Sub,
    Mul,
    Neg,
    Div,
    Rem,
    WordAdd,
    WordSub,
    WordMul,
    WordDiv,
    WordRem,
    WordWrapAdd,
    WordWrapSub,
    WordWrapMul,
    WordBitAnd,
    WordBitXor,
    WordBitOr,
    WordNot,
    WordShl,
    WordShr,
    WordCastI64,
    WordCastWord,
    WordTruncateI64,
    WordTruncateWord,
    WordToI64,
}

#[derive(Clone, Copy)]
enum Trap {
    Overflow,
    DivisionByZero,
    InvalidShift,
}
impl Trap {
    fn emit(self, boot: bool, text: &mut Buffer) -> fmt::Result {
        let (name, tag) = match self {
            Self::Overflow => ("arithmetic_overflow", 1),
            Self::DivisionByZero => ("division_by_zero", 2),
            Self::InvalidShift => ("invalid_shift", 3),
        };
        if boot {
            write!(text, "anl_boot_language_entry(UINT8_C({tag}))")
        } else {
            write!(text, "apl_trap(\"{name}\")")
        }
    }
}

pub(super) const SIGNED: &[Helper] = &[
    Helper::Add,
    Helper::Sub,
    Helper::Mul,
    Helper::Neg,
    Helper::Div,
    Helper::Rem,
];
pub(super) const WORD: &[Helper] = &[
    Helper::WordAdd,
    Helper::WordSub,
    Helper::WordMul,
    Helper::WordDiv,
    Helper::WordRem,
    Helper::WordWrapAdd,
    Helper::WordWrapSub,
    Helper::WordWrapMul,
    Helper::WordBitAnd,
    Helper::WordBitXor,
    Helper::WordBitOr,
    Helper::WordNot,
    Helper::WordShl,
    Helper::WordShr,
    Helper::WordCastI64,
    Helper::WordCastWord,
    Helper::WordTruncateI64,
    Helper::WordTruncateWord,
    Helper::WordToI64,
];
impl Helper {
    pub(super) fn emit(self, boot: bool, text: &mut Buffer) -> fmt::Result {
        match self {
            Self::Add => {
                text.write_str(
                    r#"static int64_t apl_add(int64_t a, int64_t b) {
    if ((b > 0 && a > INT64_MAX - b) || (b < 0 && a < INT64_MIN - b)) "#,
                )?;
                Trap::Overflow.emit(boot, text)?;
                text.write_str(
                    r#";
    return a + b;
}
"#,
                )?;
                Ok(())
            }
            Self::Sub => {
                text.write_str(
                    r#"static int64_t apl_sub(int64_t a, int64_t b) {
    if ((b > 0 && a < INT64_MIN + b) || (b < 0 && a > INT64_MAX + b)) "#,
                )?;
                Trap::Overflow.emit(boot, text)?;
                text.write_str(
                    r#";
    return a - b;
}
"#,
                )?;
                Ok(())
            }
            Self::Mul => {
                text.write_str(
                    r#"static int64_t apl_mul(int64_t a, int64_t b) {
    if (a > 0) {
        if ((b > 0 && a > INT64_MAX / b) || (b < 0 && b < INT64_MIN / a)) "#,
                )?;
                Trap::Overflow.emit(boot, text)?;
                text.write_str(
                    r#";
    } else if (a < 0) {
        if ((b > 0 && a < INT64_MIN / b) || (b < 0 && a < INT64_MAX / b)) "#,
                )?;
                Trap::Overflow.emit(boot, text)?;
                text.write_str(
                    r#";
    }
    return a * b;
}
"#,
                )?;
                Ok(())
            }
            Self::Neg => {
                text.write_str(
                    r#"static int64_t apl_neg(int64_t a) {
    if (a == INT64_MIN) "#,
                )?;
                Trap::Overflow.emit(boot, text)?;
                text.write_str(
                    r#";
    return -a;
}
"#,
                )?;
                Ok(())
            }
            Self::Div => {
                text.write_str(
                    r#"static int64_t apl_div(int64_t a, int64_t b) {
    if (b == 0) "#,
                )?;
                Trap::DivisionByZero.emit(boot, text)?;
                text.write_str(
                    r#";
    if (a == INT64_MIN && b == -1) "#,
                )?;
                Trap::Overflow.emit(boot, text)?;
                text.write_str(
                    r#";
    return a / b;
}
"#,
                )?;
                Ok(())
            }
            Self::Rem => {
                text.write_str(
                    r#"static int64_t apl_rem(int64_t a, int64_t b) {
    if (b == 0) "#,
                )?;
                Trap::DivisionByZero.emit(boot, text)?;
                text.write_str(
                    r#";
    if (a == INT64_MIN && b == -1) "#,
                )?;
                Trap::Overflow.emit(boot, text)?;
                text.write_str(
                    r#";
    return a % b;
}
"#,
                )?;
                Ok(())
            }
            Self::WordAdd => {
                text.write_str(
                    r#"static uint64_t apl_word_add(uint64_t a, uint64_t b, uint64_t maximum) {
    if (a > maximum - b) "#,
                )?;
                Trap::Overflow.emit(boot, text)?;
                text.write_str(
                    r#";
    return a + b;
}
"#,
                )?;
                Ok(())
            }
            Self::WordSub => {
                text.write_str(
                    r#"static uint64_t apl_word_sub(uint64_t a, uint64_t b, uint64_t maximum) {
    (void)maximum;
    if (a < b) "#,
                )?;
                Trap::Overflow.emit(boot, text)?;
                text.write_str(
                    r#";
    return a - b;
}
"#,
                )?;
                Ok(())
            }
            Self::WordMul => {
                text.write_str(
                    r#"static uint64_t apl_word_mul(uint64_t a, uint64_t b, uint64_t maximum) {
    if (b != 0 && a > maximum / b) "#,
                )?;
                Trap::Overflow.emit(boot, text)?;
                text.write_str(
                    r#";
    return a * b;
}
"#,
                )?;
                Ok(())
            }
            Self::WordDiv => {
                text.write_str(
                    r#"static uint64_t apl_word_div(uint64_t a, uint64_t b, uint64_t maximum) {
    (void)maximum;
    if (b == 0) "#,
                )?;
                Trap::DivisionByZero.emit(boot, text)?;
                text.write_str(
                    r#";
    return a / b;
}
"#,
                )?;
                Ok(())
            }
            Self::WordRem => {
                text.write_str(
                    r#"static uint64_t apl_word_rem(uint64_t a, uint64_t b, uint64_t maximum) {
    (void)maximum;
    if (b == 0) "#,
                )?;
                Trap::DivisionByZero.emit(boot, text)?;
                text.write_str(
                    r#";
    return a % b;
}
"#,
                )?;
                Ok(())
            }
            Self::WordWrapAdd => {
                text.write_str(
                    r#"static uint64_t apl_word_wrap_add(uint64_t a, uint64_t b, uint64_t maximum) {
    return ((uintmax_t)a + (uintmax_t)b) & maximum;
}
"#,
                )?;
                Ok(())
            }
            Self::WordWrapSub => {
                text.write_str(
                    r#"static uint64_t apl_word_wrap_sub(uint64_t a, uint64_t b, uint64_t maximum) {
    return ((uintmax_t)a - (uintmax_t)b) & maximum;
}
"#,
                )?;
                Ok(())
            }
            Self::WordWrapMul => {
                text.write_str(
                    r#"static uint64_t apl_word_wrap_mul(uint64_t a, uint64_t b, uint64_t maximum) {
    return ((uintmax_t)a * (uintmax_t)b) & maximum;
}
"#,
                )?;
                Ok(())
            }
            Self::WordBitAnd => {
                text.write_str(
                    r#"static uint64_t apl_word_bit_and(uint64_t a, uint64_t b, uint64_t maximum) {
    (void)maximum;
    return a & b;
}
"#,
                )?;
                Ok(())
            }
            Self::WordBitXor => {
                text.write_str(
                    r#"static uint64_t apl_word_bit_xor(uint64_t a, uint64_t b, uint64_t maximum) {
    (void)maximum;
    return a ^ b;
}
"#,
                )?;
                Ok(())
            }
            Self::WordBitOr => {
                text.write_str(
                    r#"static uint64_t apl_word_bit_or(uint64_t a, uint64_t b, uint64_t maximum) {
    (void)maximum;
    return a | b;
}
"#,
                )?;
                Ok(())
            }
            Self::WordNot => {
                text.write_str(
                    r#"static uint64_t apl_word_not(uint64_t a, uint64_t maximum) {
    return (~(uintmax_t)a) & maximum;
}
"#,
                )?;
                Ok(())
            }
            Self::WordShl => {
                text.write_str(r#"static uint64_t apl_word_shl(uint64_t a, int64_t count, unsigned width, uint64_t maximum) {
    if (count < 0 || (uint64_t)count >= width) "#)?;
                Trap::InvalidShift.emit(boot, text)?;
                text.write_str(
                    r#";
    return ((uintmax_t)a << (unsigned)count) & maximum;
}
"#,
                )?;
                Ok(())
            }
            Self::WordShr => {
                text.write_str(r#"static uint64_t apl_word_shr(uint64_t a, int64_t count, unsigned width, uint64_t maximum) {
    (void)maximum;
    if (count < 0 || (uint64_t)count >= width) "#)?;
                Trap::InvalidShift.emit(boot, text)?;
                text.write_str(
                    r#";
    return a >> (unsigned)count;
}
"#,
                )?;
                Ok(())
            }
            Self::WordCastI64 => {
                text.write_str(
                    r#"static uint64_t apl_word_cast_i64(int64_t a, uint64_t maximum) {
    if (a < 0 || (uint64_t)a > maximum) "#,
                )?;
                Trap::Overflow.emit(boot, text)?;
                text.write_str(
                    r#";
    return (uint64_t)a;
}
"#,
                )?;
                Ok(())
            }
            Self::WordCastWord => {
                text.write_str(
                    r#"static uint64_t apl_word_cast_word(uint64_t a, uint64_t maximum) {
    if (a > maximum) "#,
                )?;
                Trap::Overflow.emit(boot, text)?;
                text.write_str(
                    r#";
    return a;
}
"#,
                )?;
                Ok(())
            }
            Self::WordTruncateI64 => {
                text.write_str(
                    r#"static uint64_t apl_word_truncate_i64(int64_t a, uint64_t maximum) {
    return (uint64_t)a & maximum;
}
"#,
                )?;
                Ok(())
            }
            Self::WordTruncateWord => {
                text.write_str(
                    r#"static uint64_t apl_word_truncate_word(uint64_t a, uint64_t maximum) {
    return a & maximum;
}
"#,
                )?;
                Ok(())
            }
            Self::WordToI64 => {
                text.write_str(
                    r#"static int64_t apl_word_to_i64(uint64_t a) {
    if (a > (uint64_t)INT64_MAX) "#,
                )?;
                Trap::Overflow.emit(boot, text)?;
                text.write_str(
                    r#";
    return (int64_t)a;
}
"#,
                )?;
                Ok(())
            }
        }
    }
}
