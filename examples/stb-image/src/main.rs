use std::{ffi::CStr, io, process::exit};

mod sys {
    #![allow(non_upper_case_globals, non_camel_case_types, non_snake_case, unused)]
    include!(concat!(env!("OUT_DIR"), "/bindings.rs"));
}

fn main() {
    let mut x = 0;
    let mut y = 0;
    let mut comp = 0;

    let i = fopencookie::IoCStream::reader(io::stdin());
    //                take a std::io::Read ^^^^^^^^^^^
    let ok = unsafe { sys::stbi_info_from_file(i.as_ptr().cast(), &mut x, &mut y, &mut comp) };
    //                   use a *mut libc::FILE ^^^^^^^^^^

    if ok == true as _ {
        println!("width={x}, height={y}, components={comp}");
    } else {
        let reason = unsafe { CStr::from_ptr(sys::stbi_failure_reason()) }.to_string_lossy();
        eprintln!("error getting info: {}", reason);
        exit(1)
    }
}
