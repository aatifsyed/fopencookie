//! Convert an [`io::Write`] to a [`libc::FILE`] using the [`fopencookie`](https://man7.org/linux/man-pages/man3/fopencookie.3.html) syscall.
//! Useful for FFI.
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
    fmt::Write,
    io::{self, SeekFrom},
    num::TryFromIntError,
    ptr::NonNull,
    slice,
    str::FromStr,
};

use fopencookie_sys as sys;
use libc::{c_char, c_int, c_long, c_void, off_t, size_t};

type ReadFnPtr<T = ()> = fn(&mut T, &mut [u8]) -> io::Result<usize>;
type WriteFnPtr<T = ()> = fn(&mut T, &[u8]) -> io::Result<usize>;
type FlushFnPtr<T = ()> = fn(&mut T) -> io::Result<()>;
type SeekFnPtr<T = ()> = fn(&mut T, SeekFrom) -> io::Result<u64>;

#[derive(Clone, Copy)]
struct VTable<T> {
    read: Action<ReadFnPtr<T>>,
    write: Action<WriteFnPtr<T>>,
    flush: Option<FlushFnPtr<T>>,
    seek: Option<SeekFnPtr<T>>,
}

#[derive(Clone, Copy)]
enum Action<T> {
    Do(T),
    Ignore,
    Unsupported,
}

/// Builder for a call to [`fopencookie`](https://man7.org/linux/man-pages/man3/fopencookie.3.html).
///
/// See [module documentation](mod@self) for more.
#[must_use = "Call `build` to actually create the file handle"]
pub struct Builder<T> {
    vtable: VTable<T>,
    leak: Option<Leak>,
}

impl<T> Builder<T> {
    /// Start the builder.
    pub const fn new() -> Self {
        Self {
            vtable: VTable {
                read: Action::Ignore,
                write: Action::Ignore,
                flush: None,
                seek: None,
            },
            leak: None,
        }
    }
    pub const fn read(mut self) -> Self
    where
        T: io::Read,
    {
        self.vtable.read = Action::Do(T::read);
        self
    }
    pub const fn write(mut self) -> Self
    where
        T: io::Write,
    {
        self.vtable.write = Action::Do(T::write);
        self
    }
    pub const fn seek(mut self) -> Self
    where
        T: io::Seek,
    {
        self.vtable.seek = Some(T::seek);
        self
    }
    pub const fn strict(mut self) -> Self {
        if matches!(self.vtable.read, Action::Ignore) {
            self.vtable.read = Action::Unsupported
        }
        if matches!(self.vtable.write, Action::Ignore) {
            self.vtable.write = Action::Unsupported
        }
        self
    }
    pub const fn leak(mut self, leak: Leak) -> Self {
        self.leak = Some(leak);
        self
    }
    pub fn build(self, mode: Mode, inner: T) -> io::Result<NonNull<libc::FILE>> {
        let Self { vtable, leak } = self;
        let cookie = Box::into_raw(Box::new(Cookie { vtable, inner }));
        let file = unsafe {
            sys::fopencookie(
                cookie.cast::<c_void>(),
                mode.as_cstr().as_ptr(),
                sys::cookie_io_functions_t {
                    read: Some(Cookie::<T>::read),
                    write: Some(Cookie::<T>::write),
                    seek: Some(Cookie::<T>::seek),
                    close: Some(match leak {
                        Some(Leak::Always) => Cookie::<T>::maybe_flush_do_not_drop,
                        Some(Leak::IfPanicking) => Cookie::<T>::maybe_flush_drop_if_not_panicking,
                        None => Cookie::<T>::maybe_flush_always_drop,
                    }),
                },
            )
        };
        match NonNull::new(file.cast::<libc::FILE>()) {
            Some(it) => Ok(it),
            None => {
                drop(unsafe { Box::from_raw(cookie) });
                Err(io::Error::last_os_error())
            }
        }
    }
}

struct Cookie<T> {
    vtable: VTable<T>,
    inner: T,
}

impl<T> Cookie<T> {
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
    unsafe extern "C" fn read(cookie: *mut c_void, buf: *mut c_char, len: size_t) -> c_long {
        let cookie = &mut *cookie.cast::<Cookie<T>>();
        match cookie.vtable.read {
            Action::Do(f) => f(
                &mut cookie.inner,
                slice::from_raw_parts_mut(buf.cast::<u8>(), len),
            )
            .map_err(setting_errno)
            .and_then(|n| n.try_into().map_err(setting_errno))
            .unwrap_or(-1),
            Action::Unsupported => {
                set_errno(libc::ENOTSUP);
                -1
            }
            Action::Ignore => 0,
        }
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
    unsafe extern "C" fn write(cookie: *mut c_void, buf: *const c_char, len: size_t) -> c_long {
        let cookie = &mut *cookie.cast::<Cookie<T>>();
        match cookie.vtable.write {
            Action::Do(f) => f(
                &mut cookie.inner,
                slice::from_raw_parts(buf.cast::<u8>(), len),
            )
            .map_err(setting_errno)
            .and_then(|n| n.try_into().map_err(setting_errno))
            .unwrap_or(0),
            Action::Unsupported => {
                set_errno(libc::ENOTSUP);
                0
            }
            Action::Ignore => len.try_into().unwrap_or(c_long::MAX),
        }
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
    #[allow(unused)] // useful for the docs
    unsafe extern "C" fn close(cookie: *mut c_void) -> c_int {
        Self::maybe_flush_always_drop(cookie)
    }
    unsafe extern "C" fn maybe_flush_always_drop(cookie: *mut c_void) -> c_int {
        let ret = Self::maybe_flush_do_not_drop(cookie);
        drop(Box::from_raw(cookie.cast::<Cookie<T>>()));
        ret
    }
    unsafe extern "C" fn maybe_flush_drop_if_not_panicking(cookie: *mut c_void) -> c_int {
        if !std::thread::panicking() {
            let ret = Self::maybe_flush_do_not_drop(cookie);
            drop(Box::from_raw(cookie.cast::<Cookie<T>>()));
            ret
        } else {
            0
        }
    }
    unsafe extern "C" fn maybe_flush_do_not_drop(cookie: *mut c_void) -> c_int {
        let cookie = &mut *cookie.cast::<Cookie<T>>();
        match cookie.vtable.flush {
            Some(f) => match f(&mut cookie.inner).map_err(setting_errno) {
                Ok(()) => 0,
                Err(()) => libc::EOF,
            },
            None => 0,
        }
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
    unsafe extern "C" fn seek(cookie: *mut c_void, offset: *mut off_t, whence: c_int) -> c_int {
        let cookie = &mut *cookie.cast::<Cookie<T>>();
        let requested_offset = *offset;
        let pos = match whence {
            libc::SEEK_SET => match requested_offset.try_into().map_err(setting_errno) {
                Ok(it) => SeekFrom::Start(it),
                Err(()) => return -1,
            },
            libc::SEEK_CUR => SeekFrom::Current(requested_offset),
            libc::SEEK_END => SeekFrom::End(requested_offset),
            _ => {
                set_errno(libc::EINVAL);
                return -1;
            }
        };
        match cookie.vtable.seek {
            Some(f) => match f(&mut cookie.inner, pos).map_err(setting_errno) {
                Ok(n) => match n.try_into().map_err(setting_errno) {
                    Ok(new_offset) => {
                        *offset = new_offset;
                        0
                    }
                    Err(()) => -1,
                },
                Err(()) => -1,
            },
            None => {
                set_errno(libc::ENOTSUP);
                -1
            }
        }
    }
}

/// Configuration for leaking the [`libc::FILE`] handle.
///
/// See [`Builder::leak`] for more.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Leak {
    /// Never drop the object when [`libc::fclose`] is called.
    Always,
    /// Drop the object unless [the current thread is panicking](std::thread::panicking).
    IfPanicking,
}

/// The modes supported by [`fopencookie`](https://man7.org/linux/man-pages/man3/fopencookie.3.html).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub enum Mode {
    /// Open text file for reading.  The stream is positioned at
    /// the beginning of the file.
    Read,

    /// Open for reading and writing.  The stream is positioned at
    /// the beginning of the file.
    #[default]
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
        f.write_str("unrecognised mode (expected one of")?;
        for it in Mode::ALL {
            f.write_char(' ')?;
            f.write_str(it.as_str())?;
        }
        f.write_char(')')
    }
}

impl std::error::Error for UnrecognisedMode {}

trait SetErrno {
    fn errno(self) -> Option<c_int>;
}

impl SetErrno for io::Error {
    fn errno(self) -> Option<c_int> {
        self.raw_os_error()
    }
}
impl SetErrno for TryFromIntError {
    fn errno(self) -> Option<c_int> {
        Some(libc::EOVERFLOW)
    }
}

fn setting_errno(e: impl SetErrno) {
    if let Some(errno) = e.errno() {
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
            .write()
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
            .write()
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
    fn seek_with_no_seek() {
        unsafe {
            let handle = sys::fopencookie(
                ptr::null_mut(),
                Mode::Read.as_cstr().as_ptr(),
                sys::cookie_io_functions_t {
                    read: None,
                    write: None,
                    seek: None,
                    close: None,
                },
            )
            .cast::<libc::FILE>();
            assert!(!handle.is_null());
            let ret = libc::fseek(handle, 0, libc::SEEK_SET);
            // dbg!(io::Error::last_os_error());
            assert_eq!(ret, -1);
        };
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
            let res = Builder::new().read().write().seek().build(mode, Dummy);
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
