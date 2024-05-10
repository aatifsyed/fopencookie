//! Platform bindigns for [`fopencookie`](https://docs.rs/fopencookie)

#![allow(
    non_upper_case_globals,
    non_camel_case_types,
    non_snake_case,
    improper_ctypes,
    deref_nullptr
)]
include!(concat!(env!("OUT_DIR"), "/bindings.rs"));
