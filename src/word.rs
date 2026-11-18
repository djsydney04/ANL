//! Width-bounded scalar payloads shared by the ordinary compiler pipeline.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum WordWidth {
    U8,
    U16,
    U32,
    U64,
}
impl WordWidth {
    pub fn bits(self) -> u32 {
        match self {
            Self::U8 => 8,
            Self::U16 => 16,
            Self::U32 => 32,
            Self::U64 => 64,
        }
    }
    pub fn max(self) -> u64 {
        match self {
            Self::U64 => u64::MAX,
            _ => (1u64 << self.bits()) - 1,
        }
    }
    pub fn as_str(self) -> &'static str {
        match self {
            Self::U8 => "u8",
            Self::U16 => "u16",
            Self::U32 => "u32",
            Self::U64 => "u64",
        }
    }
    pub fn from_bits(bits: u64) -> Option<Self> {
        match bits {
            8 => Some(Self::U8),
            16 => Some(Self::U16),
            32 => Some(Self::U32),
            64 => Some(Self::U64),
            _ => None,
        }
    }
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "u8" => Some(Self::U8),
            "u16" => Some(Self::U16),
            "u32" => Some(Self::U32),
            "u64" => Some(Self::U64),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WordValue {
    width: WordWidth,
    value: u64,
}
impl WordValue {
    pub fn new(width: WordWidth, value: u64) -> Option<Self> {
        (value <= width.max()).then_some(Self { width, value })
    }
    pub fn width(self) -> WordWidth {
        self.width
    }
    pub fn value(self) -> u64 {
        self.value
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConvertMode {
    Checked,
    Truncate,
}
impl ConvertMode {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Checked => "checked",
            Self::Truncate => "truncate",
        }
    }
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "checked" => Some(Self::Checked),
            "truncate" => Some(Self::Truncate),
            _ => None,
        }
    }
}
