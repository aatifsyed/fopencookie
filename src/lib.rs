//! Convert an [`io::Write`] to a [`libc::FILE`], useful for FFI.
//!
//! ```
//! # use fopencookie::Mode;
//! let mut v = vec![];
//! let ffi = fopencookie::Builder::new()
//!     .writing()
//!     .build(Mode::ReadPlus, &mut v)
//!     .unwrap();
//!
//! // Use the *mut FILE
//! unsafe {
//!     assert!(
//!         libc::fprintf(ffi.as_ptr(), c"hello, world!".as_ptr()) == 13
//!     );
//!     assert!(
//!         libc::fflush(ffi.as_ptr()) == 0
//!     );
//! }
//!
//! // It's reflected in our rust type!
//! assert_eq!(v, b"hello, world!");
//! ```
//!
//! Trait objects are supported!
//!
//! ```
//! # use std::io;
//! # use fopencookie::Mode;
//! let mut writer: Box<dyn io::Write>;
//! # writer = Box::new(vec![]);
//! let ffi = fopencookie::Builder::<Box<dyn io::Write>>::new()
//!     .writing()
//!     .build(Mode::ReadPlus, writer)
//!     .unwrap();
//! ```

use core::fmt;
use std::{
    ffi::CStr,
    io::{self, SeekFrom},
    marker::PhantomData,
    ptr::NonNull,
    slice,
    str::FromStr,
};

use fopencookie_sys as sys;
use libc::{c_char, c_int, c_long, c_void, off_t, size_t};

#[derive(Clone, Copy)]
struct VTable {
    read: sys::cookie_read_function_t,
    write: sys::cookie_write_function_t,
    seek: sys::cookie_seek_function_t,
    flush: sys::cookie_close_function_t,
    drop: sys::cookie_close_function_t,
}

#[cfg(not(doctest))]
impl VTable {
    /**
    This function implements read operations for the stream.
    When called, it receives three arguments:

        ssize_t read(void *cookie, char *buf, size_t size);

    The buf and size arguments are, respectively, a buffer
    into which input data can be placed and the size of that
    buffer.  As its function result, the read function should
    return the number of bytes copied into buf, 0 on end of
    file, or -1 on error.  The read function should update the
    stream offset appropriately.

    If *read is a null pointer, then reads from the custom
    stream always return end of file.
    */
    unsafe extern "C" fn read<T: ?Sized + io::Read>(
        cookie: *mut c_void,
        buf: *mut c_char,
        len: size_t,
    ) -> c_long {
        let reader: &mut Cookie<T> = &mut *cookie.cast::<Cookie<T>>();
        let buf = slice::from_raw_parts_mut(buf.cast::<u8>(), len);
        reader
            .io
            .read(buf)
            .map_err(setting_errno)
            .and_then(|n| n.try_into().map_err(|_| set_errno(libc::EOVERFLOW)))
            .unwrap_or(-1)
    }
    /**
    This function implements write operations for the stream.
    When called, it receives three arguments:

        ssize_t write(void *cookie, const char *buf, size_t size);

    The buf and size arguments are, respectively, a buffer of
    data to be output to the stream and the size of that
    buffer.  As its function result, the write function should
    return the number of bytes copied from buf, or 0 on error.
    (The function must not return a negative value.)  The
    write function should update the stream offset
    appropriately.

    If *write is a null pointer, then output to the stream is
    discarded.
     */
    unsafe extern "C" fn write<T: ?Sized + io::Write>(
        cookie: *mut c_void,
        buf: *const c_char,
        len: size_t,
    ) -> c_long {
        let writer: &mut Cookie<T> = &mut *cookie.cast::<Cookie<T>>();
        let buf = slice::from_raw_parts(buf.cast::<u8>(), len);
        writer
            .io
            .write(buf)
            .map_err(setting_errno)
            .and_then(|n| n.try_into().map_err(|_| set_errno(libc::EOVERFLOW)))
            .unwrap_or_default()
    }
    /**
    This function closes the stream.  The hook function can do
    things such as freeing buffers allocated for the stream.
    When called, it receives one argument:

        int close(void *cookie);

    The cookie argument is the cookie that the programmer
    supplied when calling fopencookie().

    As its function result, the close function should return 0
    on success, and EOF on error.

    If *close is NULL, then no special action is performed
    when the stream is closed.
     */
    unsafe extern "C" fn drop<T: ?Sized>(cookie: *mut c_void) -> c_int {
        drop(Box::from_raw(cookie.cast::<Cookie<T>>()));
        0
    }
    /// See [`Self::drop`]
    unsafe extern "C" fn flush<T: ?Sized + io::Write>(cookie: *mut c_void) -> c_int {
        let writer: &mut Cookie<T> = &mut *cookie.cast::<Cookie<T>>();
        writer
            .io
            .flush()
            .map(|_| 0)
            .map_err(setting_errno)
            .unwrap_or(libc::EOF)
    }
    /**
    This function implements seek operations on the stream.
    When called, it receives three arguments:

        int seek(void *cookie, off_t *offset, int whence);

    The *offset argument specifies the new file offset
    depending on which of the following three values is
    supplied in whence:

    SEEK_SET
            The stream offset should be set *offset bytes from
            the start of the stream.

    SEEK_CUR
            *offset should be added to the current stream
            offset.

    SEEK_END
            The stream offset should be set to the size of the
            stream plus *offset.

    Before returning, the seek function should update *offset
    to indicate the new stream offset.

    As its function result, the seek function should return 0
    on success, and -1 on error.

    If *seek is a null pointer, then it is not possible to
    perform seek operations on the stream.
     */
    unsafe extern "C" fn seek<T: ?Sized + io::Seek>(
        cookie: *mut c_void,
        offset: *mut off_t,
        whence: c_int,
    ) -> c_int {
        let seeker: &mut Cookie<T> = &mut *cookie.cast::<Cookie<T>>();
        let requested_offset = *offset;
        let pos = match whence {
            libc::SEEK_SET => match requested_offset.try_into() {
                Ok(it) => SeekFrom::Start(it),
                Err(_) => {
                    set_errno(libc::EOVERFLOW);
                    return -1;
                }
            },
            libc::SEEK_CUR => SeekFrom::Current(requested_offset),
            libc::SEEK_END => SeekFrom::End(requested_offset),
            _ => panic!("invalid value for `whence`: {}", whence),
        };
        match seeker.io.seek(pos).map_err(setting_errno) {
            Ok(new_offset) => match new_offset.try_into() {
                Ok(new_offset) => {
                    *offset = new_offset;
                    0
                }
                Err(_) => {
                    set_errno(libc::EOVERFLOW);
                    -1
                }
            },
            Err(_) => -1,
        }
    }
}

/// Builder for a [`libc::FILE`].
///
/// See [`module documentation`](mod@self) for more.
pub struct Builder<T: ?Sized> {
    vtable: VTable,
    leak_if_panicking: bool,
    _phantom: PhantomData<fn() -> T>,
}

impl<T: ?Sized> Builder<T> {
    /// Start the builder.
    pub const fn new() -> Self {
        Self {
            vtable: VTable {
                read: None,
                write: None,
                seek: None,
                flush: None,
                drop: Some(VTable::drop::<T>),
            },
            leak_if_panicking: false,
            _phantom: PhantomData,
        }
    }
    /// Add [`io::Read`] support to the [`libc::FILE`].
    pub const fn reading(mut self) -> Self
    where
        T: io::Read,
    {
        self.vtable.read = Some(VTable::read::<T>);
        self
    }
    /// Add [`io::Write`] support to the [`libc::FILE`].
    pub const fn writing(mut self) -> Self
    where
        T: io::Write,
    {
        self.vtable.write = Some(VTable::write::<T>);
        self.vtable.flush = Some(VTable::flush::<T>);
        self
    }
    /// Add [`io::Seek`] support to the [`libc::FILE`].
    pub const fn seeking(mut self) -> Self
    where
        T: io::Seek,
    {
        self.vtable.seek = Some(VTable::seek::<T>);
        self
    }
    /// When cleaning up a process the OS will typically flush/close all open files.
    /// However, on unwinding, Rust's destructors will run _before_ that.
    /// So if `T: !'static`, this will cause a double free!
    ///
    /// ```no_run
    /// # use fopencookie::Mode;
    /// // 1. Allocate on the stack
    /// let mut v: vec![];
    /// // 2. Register a file with the OS
    /// //    This file depends on our stack!
    /// fopencookie::Builder::new().build(Mode::ReadPlus, &mut v).unwrap();
    /// // 3. Unwind the stack, calling the destructor for `v`
    /// panic!();
    /// // 4. After the stack has unwound,
    /// //    the OS tries to flush/close the file.
    /// //    But that memory has already been cleaned up, so you get instant UB!
    /// ```
    ///
    /// For the specific case where the [`libc::FILE`] will only be used on the
    /// current thread, and the thread panics,
    /// you can choose to skip the destructor.
    ///
    /// This is NOT a general safety mechanism.
    pub const fn leak_if_panicking(mut self) -> Self {
        self.leak_if_panicking = true;
        self
    }
    /// Make the call to [`fopencookie`](https://man7.org/linux/man-pages/man3/fopencookie.3.html).
    pub fn build(self, mode: Mode, io: impl Into<Box<T>>) -> io::Result<NonNull<libc::FILE>> {
        let Self {
            vtable,
            leak_if_panicking,
            _phantom,
        } = self;
        let io_funcs = sys::cookie_io_functions_t {
            read: Some({
                unsafe extern "C" fn forward_read(
                    cookie: *mut c_void,
                    buf: *mut c_char,
                    len: size_t,
                ) -> c_long {
                    let _cookie: &Cookie<()> = &*cookie.cast::<Cookie<()>>();
                    match _cookie.vtable.read {
                        Some(f) => f(cookie, buf, len),
                        None => -1,
                    }
                }
                forward_read
            }),
            write: Some({
                unsafe extern "C" fn forward_write(
                    cookie: *mut c_void,
                    buf: *const c_char,
                    len: size_t,
                ) -> c_long {
                    let _cookie: &Cookie<()> = &*cookie.cast::<Cookie<()>>();
                    match _cookie.vtable.write {
                        Some(f) => f(cookie, buf, len),
                        None => {
                            set_errno(libc::ENOTSUP);
                            0
                        }
                    }
                }
                forward_write
            }),
            seek: Some({
                unsafe extern "C" fn forward_seek(
                    cookie: *mut c_void,
                    offset: *mut off_t,
                    whence: c_int,
                ) -> c_int {
                    let _cookie: &Cookie<()> = &*cookie.cast::<Cookie<()>>();
                    match _cookie.vtable.seek {
                        Some(f) => f(cookie, offset, whence),
                        None => {
                            set_errno(libc::ENOTSUP);
                            -1
                        }
                    }
                }
                forward_seek
            }),
            close: Some({
                unsafe extern "C" fn forward_flush_and_drop(cookie: *mut c_void) -> c_int {
                    let _cookie: &Cookie<()> = &*cookie.cast::<Cookie<()>>();
                    match (
                        _cookie.leak_if_panicking,
                        _cookie.vtable.drop,
                        _cookie.vtable.flush,
                    ) {
                        (true, None, None) => 0,
                        (true, None, Some(f)) => f(cookie),
                        (true, Some(d), None) => match std::thread::panicking() {
                            true => 0, // leak
                            false => d(cookie),
                        },
                        (true, Some(d), Some(f)) => {
                            let ret = f(cookie);
                            match std::thread::panicking() {
                                true => ret, // leak
                                false => {
                                    d(cookie);
                                    ret
                                }
                            }
                        }
                        (false, None, None) => 0,
                        (false, None, Some(f)) => f(cookie),
                        (false, Some(d), None) => d(cookie),
                        (false, Some(d), Some(f)) => {
                            let ret = f(cookie);
                            d(cookie);
                            ret
                        }
                    }
                }
                forward_flush_and_drop
            }),
        };

        let cookie = Box::into_raw(Box::new(Cookie {
            vtable,
            leak_if_panicking,
            io: io.into(),
        }));
        let cookie = cookie.cast::<c_void>();
        let ret = unsafe { sys::fopencookie(cookie, mode.as_cstr().as_ptr(), io_funcs) };

        match NonNull::new(ret.cast::<libc::FILE>()) {
            Some(it) => Ok(it),
            None => {
                if let Some(d) = vtable.drop {
                    unsafe { d(cookie) };
                };
                Err(io::Error::last_os_error())
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Mode {
    /// Open text file for reading.  The stream is positioned at
    /// the beginning of the file.
    Read,

    /// Open for reading and writing.  The stream is positioned at
    /// the beginning of the file.
    ReadPlus,

    /// Truncate file to zero length or create text file for
    /// writing.  The stream is positioned at the beginning of the
    /// file.
    Write,

    /// Open for reading and writing.  The file is created if it
    /// does not exist, otherwise it is truncated.  The stream is
    /// positioned at the beginning of the file.
    WritePlus,

    /// Open for appending (writing at end of file).  The file is
    /// created if it does not exist.  The stream is positioned at
    /// the end of the file.
    Append,

    /// Open for reading and appending (writing at end of file).
    /// The file is created if it does not exist.  Output is
    /// always appended to the end of the file.  POSIX is silent
    /// on what the initial read position is when using this mode.
    /// For glibc, the initial file position for reading is at the
    /// beginning of the file, but for Android/BSD/MacOS, the
    /// initial file position for reading is at the end of the
    /// file.
    AppendPlus,
}

impl Mode {
    const ALL: &'static [Self] = &[
        Mode::Read,
        Mode::ReadPlus,
        Mode::Write,
        Mode::WritePlus,
        Mode::Append,
        Mode::AppendPlus,
    ];
}

impl fmt::Display for Mode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl FromStr for Mode {
    type Err = UnrecognisedMode;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::from_str(s)
    }
}

impl Mode {
    pub const fn as_cstr(&self) -> &'static CStr {
        match self {
            Mode::Read => c"r",
            Mode::ReadPlus => c"r+",
            Mode::Write => c"w",
            Mode::WritePlus => c"w+",
            Mode::Append => c"a",
            Mode::AppendPlus => c"a+",
        }
    }
    pub const fn as_str(&self) -> &'static str {
        match self.as_cstr().to_str() {
            Ok(it) => it,
            Err(_) => unreachable!(),
        }
    }
    pub const fn from_str(s: &str) -> Result<Self, UnrecognisedMode> {
        let mut ix = Self::ALL.len();
        while let Some(nix) = ix.checked_sub(1) {
            ix = nix;
            let candidate = Self::ALL[ix];
            if slice_eq(s.as_bytes(), candidate.as_str().as_bytes()) {
                return Ok(candidate);
            }
        }
        Err(UnrecognisedMode)
    }
}
const fn slice_eq(left: &[u8], right: &[u8]) -> bool {
    if left.len() != right.len() {
        return false;
    }
    let mut ix = left.len();
    while let Some(nix) = ix.checked_sub(1) {
        ix = nix;
        if left[ix] != right[ix] {
            return false;
        }
    }
    true
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UnrecognisedMode;

impl fmt::Display for UnrecognisedMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("unrecognised mode")
    }
}

impl std::error::Error for UnrecognisedMode {}

struct Cookie<T: ?Sized> {
    vtable: VTable,
    leak_if_panicking: bool,
    io: Box<T>, // allow this to be a trait object
}

fn setting_errno(e: io::Error) {
    if let Some(errno) = e.raw_os_error() {
        set_errno(errno)
    }
}

fn set_errno(to: c_int) {
    let dst = unsafe { &mut *libc::__errno_location() };
    *dst = to;
}

#[cfg(test)]
mod tests {
    use std::ptr;

    use super::*;

    const TEST_TEXT: &CStr = c"hello, world!";
    const TEST_TEXT_LEN: i32 = TEST_TEXT.to_bytes().len() as _;

    #[test]
    fn borrowed() {
        let mut v = vec![];
        let file = Builder::new()
            .writing()
            .build(Mode::WritePlus, &mut v)
            .unwrap();
        unsafe {
            assert_eq!(
                libc::fprintf(file.as_ptr(), TEST_TEXT.as_ptr()),
                TEST_TEXT_LEN
            );
            assert_eq!(libc::fclose(file.as_ptr()), 0);
        };
        assert_eq!(v, TEST_TEXT.to_bytes());
    }

    #[test]
    fn trait_object() {
        let mut v = vec![];
        let file = Builder::<Box<dyn io::Write>>::new()
            .writing()
            .build(Mode::WritePlus, Box::new(&mut v) as Box<dyn io::Write>)
            .unwrap();
        unsafe {
            assert_eq!(
                libc::fprintf(file.as_ptr(), TEST_TEXT.as_ptr()),
                TEST_TEXT_LEN
            );
            assert_eq!(libc::fclose(file.as_ptr()), 0);
        };
        assert_eq!(v, TEST_TEXT.to_bytes());
    }

    #[test]
    fn fopencookie_never_fails() {
        for mode in Mode::ALL {
            for read in [None, Some(noop_err::read as _)] {
                for write in [None, Some(noop_err::write as _)] {
                    for seek in [None, Some(noop_err::seek as _)] {
                        for close in [None, Some(noop_err::close as _)] {
                            let ret = unsafe {
                                sys::fopencookie(
                                    ptr::null_mut(),
                                    mode.as_cstr().as_ptr(),
                                    sys::cookie_io_functions_t {
                                        read,
                                        write,
                                        seek,
                                        close,
                                    },
                                )
                            };
                            assert_ne!(ret, ptr::null_mut())
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn fail_to_open() {
        struct Dummy;
        impl io::Seek for Dummy {
            fn seek(&mut self, _: SeekFrom) -> io::Result<u64> {
                Err(io::Error::other("seek"))
            }
        }
        impl io::Write for Dummy {
            fn write(&mut self, _: &[u8]) -> io::Result<usize> {
                Err(io::Error::other("write"))
            }

            fn flush(&mut self) -> io::Result<()> {
                Err(io::Error::other("flush"))
            }
        }
        impl io::Read for Dummy {
            fn read(&mut self, _: &mut [u8]) -> io::Result<usize> {
                Err(io::Error::other("read"))
            }
        }
        for mode in [
            Mode::Append,
            Mode::AppendPlus,
            Mode::Read,
            Mode::ReadPlus,
            Mode::Write,
            Mode::WritePlus,
        ] {
            let res = Builder::new()
                .reading()
                .writing()
                .seeking()
                .build(mode, Dummy);
            let _ = dbg!(res);
        }
    }

    mod noop_err {
        use libc::{c_char, c_int, c_long, c_void, off_t, size_t};

        pub unsafe extern "C" fn read(
            _cookie: *mut c_void,
            _buf: *mut c_char,
            _len: size_t,
        ) -> c_long {
            -1
        }
        pub unsafe extern "C" fn write(
            _cookie: *mut c_void,
            _buf: *const c_char,
            _len: size_t,
        ) -> c_long {
            0
        }
        pub unsafe extern "C" fn close(_cookie: *mut c_void) -> c_int {
            libc::EOF
        }
        pub unsafe extern "C" fn seek(
            _cookie: *mut c_void,
            _offset: *mut off_t,
            _whence: c_int,
        ) -> c_int {
            -1
        }
    }
}
