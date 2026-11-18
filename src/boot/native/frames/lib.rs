//! Conditional local frames and closed setup-call composition; never native admission.
#![forbid(unsafe_code)]

pub use anl_native_machine as machine;
pub mod frames;
pub use frames::{
    ConditionalBootFaultPrefix, ConditionalRoleDepth, ExceptionStackError,
    ExceptionStackInspection, FaultStackObservation, FrameError, IoEvent, IoObservation,
    LocalFrameInspection, SetupStackInspection, StackError, UartByteCounters, UartByteError,
    UartByteInspection, UartByteLeaf, UartBytePhase, UartByteRelation, UartDiagnostic,
    UartInspectionError, UartLeaf, UartLeafInspection, UartPhase, inspect_exception_setup_stacks,
    inspect_local_frames, inspect_setup_stacks, inspect_uart_bytes_v3, inspect_uart_leaves_v3,
};

pub const COMPLETE_FRAMES_AND_RETURNS: bool = false;
pub const CALL_STACK_BOUND_ESTABLISHED: bool = false;
pub const EMITTED_IDENTITY_ESTABLISHED: bool = false;
pub const NATIVE_ADMITTED: bool = false;
