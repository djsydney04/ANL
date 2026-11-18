//! Conditional local frame facts; never native admission or call composition.
#![forbid(unsafe_code)]

pub use anl_native_machine as machine;
pub mod frames;
pub use frames::{FrameError, LocalFrameInspection, inspect_local_frames};

pub const COMPLETE_FRAMES_AND_RETURNS: bool = false;
pub const CALL_STACK_BOUND_ESTABLISHED: bool = false;
pub const EMITTED_IDENTITY_ESTABLISHED: bool = false;
pub const NATIVE_ADMITTED: bool = false;
