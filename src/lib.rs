//! Convert an [`io::Write`]/[`io::Read`]/[`io::Seek`] to a [`libc::FILE`] stream
//! using the [`fopencookie`](https://man7.org/linux/man-pages/man3/fopencookie.3.html) syscall.
//!
//! Great for passing rust traits across FFI.
//! ```
//! let mut v = vec![];
//! let stream = fopencookie::IoCStream::writer(&mut v);
//!
//! // Use the libc stream functions
//! assert_eq!(
//!     unsafe {
//!         libc::fprintf(stream.as_ptr(), c"hello, world!".as_ptr())
//!     },
//!     13 // all bytes written
//! );
//!
//! // It's reflected in our rust type!
//! assert_eq!(v, b"hello, world!");
//! ```
//!
//! Trait objects are supported!
//!
//! ```
//! # use std::io;
//! let mut reader: Box<dyn io::Read>;
//! # reader = Box::new(io::empty());
//! let stream = fopencookie::IoCStream::reader(reader);
//! ```
//!
//! You can use the [`Builder`] for more flexibility.
//!
//! ```no_run
//! # use std::fs::File;
//! let mut file: File;
//! # file = unimplemented!();
//! let stream = fopencookie::Builder::new()
//!     .read()
//!     .write()
//!     .seek()
//!     .build(file);
//! ```

use core::fmt;
use cstream::{
    AsCStream, AsRawCStream, BorrowedCStream, FromRawCStream, IntoRawCStream, OwnedCStream,
};
use fopencookie_sys as sys;
use libc::{c_char, c_int, c_long, c_void, off_t, size_t};
use std::{
    ffi::CStr,
    fmt::Write,
    io::{self, SeekFrom},
    mem,
    num::TryFromIntError,
    ptr::{self, NonNull},
    slice,
    str::FromStr,
};

type ReadFnPtr<T = ()> = fn(&mut T, &mut [u8]) -> io::Result<usize>;
type WriteFnPtr<T = ()> = fn(&mut T, &[u8]) -> io::Result<usize>;
type FlushFnPtr<T = ()> = fn(&mut T) -> io::Result<()>;
type SeekFnPtr<T = ()> = fn(&mut T, SeekFrom) -> io::Result<u64>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct VTable<T> {
    read: Action<ReadFnPtr<T>>,
    write: Action<WriteFnPtr<T>>,
    flush: Option<FlushFnPtr<T>>,
    seek: Option<SeekFnPtr<T>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
enum Action<T> {
    Do(T),
    #[default]
    Ignore,
    Unsupported,
}

/// Builder for [`IoCStream`] where you opt-in to forwarding [`io`] traits from
/// the underlying type.
///
/// See [module documentation](mod@self) for more.
#[must_use = "Call `build` to actually create the IoStream"]
pub struct Builder<T> {
    vtable: VTable<T>,
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
        }
    }
    /// Enable [`io::Read`] on the [`IoCStream`].
    pub const fn read(mut self) -> Self
    where
        T: io::Read,
    {
        self.vtable.read = Action::Do(T::read);
        self
    }
    /// Enable [`io::Write`] on the [`IoCStream`].
    pub const fn write(mut self) -> Self
    where
        T: io::Write,
    {
        self.vtable.write = Action::Do(T::write);
        self
    }
    /// Enable [`io::Seek`] on the [`IoCStream`].
    pub const fn seek(mut self) -> Self
    where
        T: io::Seek,
    {
        self.vtable.seek = Some(T::seek);
        self
    }
    /// By default, [`libc::read`]/[`libc::write`] operations on [`IoCStream`] will be ignored
    /// if they haven't been enabled with this builder.
    ///
    /// Calling this function makes such attempts return an error instead.
    pub const fn strict(mut self) -> Self {
        if matches!(self.vtable.read, Action::Ignore) {
            self.vtable.read = Action::Unsupported
        }
        if matches!(self.vtable.write, Action::Ignore) {
            self.vtable.write = Action::Unsupported
        }
        self
    }
    /// Finish the build, with a default [`Mode::ReadPlus`].
    ///
    /// # Panics
    /// - See [`Self::build_with_mode`].
    pub fn build(self, inner: T) -> IoCStream<T> {
        self.build_with_mode(Mode::default(), inner)
    }
    /// Finish the build.
    ///
    /// # Panics
    /// - If the underlying call to [`fopencookie`](https://man7.org/linux/man-pages/man3/fopencookie.3.html)
    ///   fails (typically due to an allocation failure)
    pub fn build_with_mode(self, mode: Mode, inner: T) -> IoCStream<T> {
        let Self { vtable } = self;
        let cookie = Box::new(Cookie {
            vtable,
            inner,
            drop_on_close: false,
        });
        let file = unsafe {
            sys::fopencookie(
                &*cookie as *const Cookie<T> as *const c_void as *mut c_void,
                mode.as_cstr().as_ptr(),
                sys::cookie_io_functions_t {
                    read: Some(Cookie::<T>::read),
                    write: Some(Cookie::<T>::write),
                    seek: Some(Cookie::<T>::seek),
                    close: Some(Cookie::<T>::close),
                },
            )
        };
        match NonNull::new(file.cast::<libc::FILE>()) {
            Some(raw) => {
                // remove buffering.
                unsafe { libc::setbuf(raw.as_ptr(), ptr::null_mut()) }
                IoCStream {
                    stream: unsafe { OwnedCStream::from_raw_c_stream(raw) },
                    cookie,
                }
            }
            None => panic!(
                "call to `fopencookie` failed, despite having a valid `mode`,\
                 perhaps an allocation failed?\
                 last os error: {}",
                io::Error::last_os_error()
            ),
        }
    }
}

/// Compatibility layer between [`io::Read`]/[`io::Write`]/[`io::Seek`] and
/// [`libc::FILE`] streams.
///
/// This implements [`cstream`] traits for accessing the stream, or you can
/// do so via [`Self::as_ptr`].
///
/// This struct owns two resources with tied lifetimes:
/// - The underlying io type, `T`.
/// - An open [`libc::FILE`] stream.
#[derive(Debug)]
pub struct IoCStream<T> {
    // this needs to be first so that it's dropped first
    stream: OwnedCStream,
    cookie: Box<Cookie<T>>,
}

impl<T> IoCStream<T> {
    /// Convenience function for an [`io::Read`].
    ///
    /// See [`Builder`] for more.
    pub fn reader(inner: T) -> Self
    where
        T: io::Read,
    {
        Builder::new().read().build_with_mode(Mode::Read, inner)
    }
    /// Convenience function for an [`io::Write`].
    ///
    /// See [`Builder`] for more.
    pub fn writer(inner: T) -> Self
    where
        T: io::Write,
    {
        Builder::new().write().build_with_mode(Mode::Write, inner)
    }
    /// Get a shared reference ot the inner io resource.
    pub fn get_ref(&self) -> &T {
        &self.cookie.inner
    }
    /// Get a mutable reference ot the inner io resource.
    pub fn get_mut(&mut self) -> &mut T {
        &mut self.cookie.inner
    }
    /// Consume this object, [`libc::fclose`]-ing the associated stream.
    /// [`libc::FILE`] pointers from this object MUST NOT be used after this point.
    pub fn into_inner(self) -> T {
        self.cookie.inner
    }
    /// Shortcut via [`AsRawCStream::as_raw_c_stream`], without requiring that
    /// trait to be in scope.
    ///
    /// Calling [`libc::fclose`] on this pointer will result in undefined behaviour.
    pub fn as_ptr(&self) -> *mut libc::FILE {
        self.as_raw_c_stream().as_ptr()
    }
    /// Defers freeing the inner io to the [`OwnedCStream`].
    ///
    /// # Safety
    /// - The returned object must NOT outlive any underlying io.
    ///   This is trivial if `T: 'static`.
    pub unsafe fn into_owned_c_stream_unchecked(self) -> OwnedCStream {
        let Self { stream, mut cookie } = self;
        cookie.drop_on_close = true;
        mem::forget(cookie);
        stream
    }
    /// Defers freeing the inner io to the [`OwnedCStream`].
    pub fn into_owned_c_stream(self) -> OwnedCStream
    where
        T: 'static,
    {
        unsafe { self.into_owned_c_stream_unchecked() }
    }
}

impl<T> From<IoCStream<T>> for OwnedCStream
where
    T: 'static,
{
    fn from(value: IoCStream<T>) -> Self {
        value.into_owned_c_stream()
    }
}

impl<T> AsCStream for IoCStream<T> {
    fn as_c_stream(&self) -> BorrowedCStream<'_> {
        self.stream.as_c_stream()
    }
}

impl<T> AsRawCStream for IoCStream<T> {
    fn as_raw_c_stream(&self) -> cstream::RawCStream {
        self.stream.as_raw_c_stream()
    }
}

impl<T> IntoRawCStream for IoCStream<T>
where
    T: 'static,
{
    /// See [`Self::into_owned_c_stream`]
    fn into_raw_c_stream(self) -> cstream::RawCStream {
        self.into_owned_c_stream().into_raw_c_stream()
    }
}

impl<T: io::Write> io::Write for IoCStream<T> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.cookie.inner.write(buf)
    }
    fn flush(&mut self) -> io::Result<()> {
        self.cookie.inner.flush()
    }
}

impl<T: io::Read> io::Read for IoCStream<T> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.cookie.inner.read(buf)
    }
}

impl<T: io::Seek> io::Seek for IoCStream<T> {
    fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
        self.cookie.inner.seek(pos)
    }
}

unsafe impl<T: Send> Send for IoCStream<T> {}
unsafe impl<T: Sync> Sync for IoCStream<T> {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Cookie<T> {
    vtable: VTable<T>,
    drop_on_close: bool,
    inner: T,
}

#[cfg(not(doctest))]
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
        let cookie = &mut *cookie.cast::<Cookie<T>>();
        let ret = match cookie.vtable.flush {
            Some(f) => match f(&mut cookie.inner).map_err(setting_errno) {
                Ok(()) => 0,
                Err(()) => libc::EOF,
            },
            None => 0,
        };
        match cookie.drop_on_close {
            true => drop(Box::from_raw(cookie)),
            false => {}
        }
        ret
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
    use super::*;

    const TEST_TEXT: &str = "hello, world!";

    #[test]
    fn borrowed() {
        let mut v = vec![];
        let stream = Builder::new().write().build(&mut v);

        assert_eq!(
            cstream::write(TEST_TEXT.as_bytes(), stream),
            TEST_TEXT.len()
        );
        assert_eq!(v, TEST_TEXT.as_bytes());
    }

    #[test]
    fn trait_object() {
        let mut v = vec![];
        let stream = Builder::<Box<dyn io::Write>>::new()
            .write()
            .build(Box::new(&mut v));

        assert_eq!(
            cstream::write(TEST_TEXT.as_bytes(), stream),
            TEST_TEXT.len()
        );
        assert_eq!(v, TEST_TEXT.as_bytes());
    }

    #[test]
    fn streams_have_no_fileno() {
        let stream = IoCStream::writer(io::empty());
        assert_eq!(cstream::fileno(&stream), None);
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

    /// Cookie functions which always return the error state.
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
