//! Conditional local frames and closed setup-call composition; never native admission.
#![forbid(unsafe_code)]

pub use anl_native_machine as machine;
pub mod frames;
pub use frames::{
    FrameError, LocalFrameInspection, SetupStackInspection, StackError, inspect_local_frames,
    inspect_setup_stacks,
};

pub const COMPLETE_FRAMES_AND_RETURNS: bool = false;
pub const CALL_STACK_BOUND_ESTABLISHED: bool = false;
pub const EMITTED_IDENTITY_ESTABLISHED: bool = false;
pub const NATIVE_ADMITTED: bool = false;
