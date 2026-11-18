//! Bounded instruction/known-edge inspection, never native admission.
#![forbid(unsafe_code)]

pub use anl_native_text as text;
pub mod decode;
pub mod machine;

pub use machine::{
    IllegalSite, InstructionKind, MachineError, MachineInspection, MachineInventoryView, Stage,
    V3IllegalSite, V3UartMachineInspection, inspect_machine, inspect_machine_with_illegal,
    inspect_uart_machine_v3,
};

pub const UNCHECKED: &[&str] = &[
    "emitted_identity",
    "attribute_agreement",
    "frames_and_returns",
    "memory_and_primitive_authority",
    "stack_metadata_and_paths",
    "selected_source_mapping",
    "selected_closed_components",
    "producer_provenance",
    "native_correspondence",
];
