<!-- cargo-rdme start -->

Convert an [`io::Write`]/[`io::Read`]/[`io::Seek`] to a [`libc::FILE`] stream
using the [`fopencookie`](https://man7.org/linux/man-pages/man3/fopencookie.3.html) syscall.

Great for passing rust traits across FFI.
```rust
let mut v = vec![];
let stream = fopencookie::IoCStream::writer(&mut v);

// Use the libc stream functions
assert_eq!(
    unsafe {
        libc::fprintf(stream.as_ptr(), c"hello, world!".as_ptr())
    },
    13 // all bytes written
);

// It's reflected in our rust type!
assert_eq!(v, b"hello, world!");
```

Trait objects are supported!

```rust
let mut reader: Box<dyn io::Read>;
let stream = fopencookie::IoCStream::reader(reader);
```

You can use the [`Builder`] for more flexibility.

```rust
let mut file: File;
let stream = fopencookie::Builder::new()
    .read()
    .write()
    .seek()
    .build(file);
```

<!-- cargo-rdme end -->
