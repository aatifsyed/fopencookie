<!-- cargo-rdme start -->

Utilities for [`libc::FILE`] streams 'c streams'

# Features
- Owned and borrowed c streams.
  Mirroring [`std::os::fd`](https://doc.rust-lang.org/std/os/fd/index.html)'s API.
- Rusty wrappers around [`libc`]'s stream-oriented functions.
  [`libc::fgets`] becomes [`gets`], etc.
- An [`Io`] wrapper, which implements [`io`](std::io) traits.

<!-- cargo-rdme end -->
