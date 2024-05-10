use std::{env, error::Error, path::PathBuf};

fn main() -> Result<(), Box<dyn Error>> {
    let bindings_rs = PathBuf::from(env::var("OUT_DIR")?).join("bindings.rs");
    bindgen::builder()
        .clang_arg("-DSTB_IMAGE_IMPLEMENTATION")
        .header("stb_image.h")
        .allowlist_item("stbi.*")
        .generate()?
        .write_to_file(bindings_rs)?;
    let file = "stb_image.c";
    println!("cargo::rerun-if-changed={}", file);
    cc::Build::new().file(file).compile("stb_image");
    Ok(())
}
