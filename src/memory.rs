use serde_json::{Value, json};
pub const SEMANTIC_REVISION: &str = "anl-owned-buffers-v1";
pub const MAX_LIVE_CELLS: usize = 1_048_576;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AllocationProfile {
    pub(crate) i64_align: u32,
    pub(crate) size_bits: u32,
    pub(crate) ptrdiff_bits: u32,
}
impl AllocationProfile {
    pub(crate) fn host() -> Result<Self, String> {
        let p = Self {
            i64_align: std::mem::align_of::<i64>() as u32,
            size_bits: usize::BITS,
            ptrdiff_bits: isize::BITS,
        };
        if std::mem::size_of::<i64>() != 8 || !p.valid() {
            return Err("unsupported host allocation profile".into());
        }
        Ok(p)
    }
    pub(crate) fn valid(self) -> bool {
        matches!(self.i64_align, 1 | 2 | 4 | 8 | 16)
            && matches!(self.size_bits, 32 | 64)
            && matches!(self.ptrdiff_bits, 32 | 64)
    }
    pub(crate) fn max_cells(self) -> u64 {
        (((1u128 << self.size_bits) - 1) / 8)
            .min(((1u128 << (self.ptrdiff_bits - 1)) - 1) / 8)
            .min(i64::MAX as u128) as u64
    }
    pub(crate) fn key(self) -> String {
        format!(
            "c8_i8_a{}_s{}_d{}",
            self.i64_align, self.size_bits, self.ptrdiff_bits
        )
    }
    pub(crate) fn json(self) -> Value {
        json!({"abi":"anl-buffer-c11-v1","char_bits":8,"i64_bytes":8,"i64_align":self.i64_align,"size_bits":self.size_bits,"ptrdiff_bits":self.ptrdiff_bits})
    }
}

pub(crate) fn runtime_sources(profile: AllocationProfile) -> (String, String) {
    let key = profile.key();
    let size_max = ((1u128 << profile.size_bits) - 1) as u64;
    let ptrdiff_max = ((1u128 << (profile.ptrdiff_bits - 1)) - 1) as u64;
    let header = format!(
        r#"#ifndef ANL_BUFFER_RUNTIME_V1
#define ANL_BUFFER_RUNTIME_V1 1
_Static_assert(ANL_BUFFER_RUNTIME_V1 == 1, "ANL buffer ABI version mismatch");
#include <stdint.h>
#include <stddef.h>
#include <limits.h>
_Static_assert(CHAR_BIT == 8 && sizeof(int64_t) == 8, "ANL byte profile mismatch");
_Static_assert(_Alignof(int64_t) == {align}, "ANL i64 alignment mismatch");
_Static_assert(SIZE_MAX == UINT64_C({size_max}), "ANL size profile mismatch");
_Static_assert(PTRDIFF_MAX == INT64_C({ptrdiff_max}), "ANL ptrdiff profile mismatch");
typedef struct {{ int64_t *data; int64_t length; }} anl_buffer;
#define ANL_MAX_CELLS UINT64_C({max_cells})
#ifdef ANL_MEMORY_EVIDENCE
#define anl_memory_request anl_buffer_request_e1_{key}
#define anl_memory_release anl_buffer_release_e1_{key}
#define anl_memory_begin anl_buffer_begin_e1_{key}
#define anl_memory_value anl_buffer_value_e1_{key}
#define anl_memory_trap anl_buffer_trap_e1_{key}
#define anl_memory_empty_open anl_buffer_empty_open_e1_{key}
#define anl_memory_empty_close anl_buffer_empty_close_e1_{key}
void anl_memory_begin(void);
void anl_memory_value(int64_t);
void anl_memory_trap(const char *);
void anl_memory_empty_open(uint64_t,uint64_t);
void anl_memory_empty_close(uint64_t,uint64_t);
#else
#define anl_memory_request anl_buffer_request_v1_{key}
#define anl_memory_release anl_buffer_release_v1_{key}
#define anl_memory_begin() ((void)0)
#define anl_memory_value(value) ((void)0)
#define anl_memory_trap(tag) ((void)0)
#define anl_memory_empty_open(function,site) ((void)0)
#define anl_memory_empty_close(function,site) ((void)0)
#endif
int64_t *anl_memory_request(int64_t, uint64_t, uint64_t);
void anl_memory_release(int64_t *, uint64_t, uint64_t);
#endif
"#,
        align = profile.i64_align,
        max_cells = profile.max_cells()
    );
    let runtime = include_str!("../runtime/buffer.c").to_owned();
    (header, runtime)
}
