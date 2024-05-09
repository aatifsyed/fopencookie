use std::{env, error::Error, path::PathBuf};

fn main() -> Result<(), Box<dyn Error>> {
    let bindings_rs =
        PathBuf::from(env::var_os("OUT_DIR").ok_or(env::VarError::NotPresent)?).join("bindings.rs");
    bindgen::builder()
        .header_contents("header.h", "#include <stdio.h>")
        .clang_arg("-fretain-comments-from-system-headers")
        .clang_arg("-fparse-all-comments")
        .clang_arg("-D_GNU_SOURCE")
        .allowlist_function("fopencookie")
        .generate()?
        .write_to_file(bindings_rs)?;
    Ok(())
}
