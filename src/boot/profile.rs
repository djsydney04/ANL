//! Closed metadata revisions retained by checked boot programs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Profile {
    V1,
    V2,
    V3,
}
impl Profile {
    pub const fn source_name(self) -> &'static str {
        match self {
            Self::V1 => "rv64_virt_sbi_v1",
            Self::V2 => "rv64_virt_sbi_v2",
            Self::V3 => "rv64_virt_sbi_v3",
        }
    }
    pub const fn target(self) -> &'static str {
        match self {
            Self::V1 => "rv64-virt-sbi-v1",
            Self::V2 => "rv64-virt-sbi-v2",
            Self::V3 => "rv64-virt-sbi-v3",
        }
    }
    pub const fn core_schema(self) -> &'static str {
        match self {
            Self::V1 => "anl-boot-core-v1",
            Self::V2 => "anl-boot-core-v2",
            Self::V3 => "anl-boot-core-v3",
        }
    }
    pub const fn mir_schema(self) -> &'static str {
        match self {
            Self::V1 => "anl-boot-mir-v1",
            Self::V2 => "anl-boot-mir-v2",
            Self::V3 => "anl-boot-mir-v3",
        }
    }
    pub const fn semantic_revision(self) -> &'static str {
        match self {
            Self::V1 => "anl-boot-rv64-virt-v1",
            Self::V2 => "anl-boot-rv64-virt-v2",
            Self::V3 => "anl-boot-rv64-virt-v3",
        }
    }
    pub const fn bundle_schema(self) -> &'static str {
        match self {
            Self::V1 => "anl-boot-bundle-v1",
            Self::V2 => "anl-boot-bundle-v2",
            Self::V3 => "anl-boot-bundle-v3",
        }
    }
    pub const fn verification_schema(self) -> &'static str {
        match self {
            Self::V1 => "anl-boot-verify-v1",
            Self::V2 => "anl-boot-verify-v2",
            Self::V3 => "anl-boot-verify-v3",
        }
    }
    pub const fn verification_revision(self) -> &'static str {
        match self {
            Self::V1 => "anl-boot-unsupported-v1",
            Self::V2 => "anl-boot-unsupported-v2",
            Self::V3 => "anl-boot-unsupported-v3",
        }
    }
    pub(super) const fn allows_illegal_instruction(self) -> bool {
        matches!(self, Self::V2 | Self::V3)
    }
}
