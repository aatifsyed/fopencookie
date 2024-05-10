//! - Owned and borrowed [`libc::FILE`] streams.
//!   Mirroring [`std::os::fd`](https://doc.rust-lang.org/std/os/fd/index.html)'s API.
//! - Rusty wrappers around [`libc`]'s stream-oriented functions

#![cfg_attr(not(feature = "std"), no_std)]
#[cfg(feature = "alloc")]
extern crate alloc;

use core::{
    ffi::CStr,
    fmt,
    marker::PhantomData,
    mem,
    ptr::{self, NonNull},
};
use libc::{c_char, c_int, c_void};

#[cfg(feature = "std")]
mod io;
#[cfg(feature = "std")]
pub use io::Io;

/// A [`libc::FILE`] stream.
pub type RawCStream = NonNull<libc::FILE>;

/// An owned [`RawCStream`].
/// This [`libc::fclose`]s the stream on drop.
/// It is guaranteed that nobody else will close the stream.
///
/// This uses `#[repr(transparent)]` and has the representation of a host stream,
/// so it can be used in FFI in places where a stream is passed as a consumed argument
/// or returned as an owned value, and it never has the value `NULL`.
#[derive(Debug)]
#[repr(transparent)]
pub struct OwnedCStream {
    raw: RawCStream,
}

impl Drop for OwnedCStream {
    fn drop(&mut self) {
        unsafe {
            // Errors are ignored
            let _ = libc::fclose(self.raw.as_ptr());
        }
    }
}

impl AsCStream for OwnedCStream {
    fn as_c_stream(&self) -> BorrowedCStream<'_> {
        unsafe { BorrowedCStream::borrow_raw(self.raw) }
    }
}

impl AsRawCStream for OwnedCStream {
    fn as_raw_c_stream(&self) -> RawCStream {
        self.raw
    }
}

impl FromRawCStream for OwnedCStream {
    unsafe fn from_raw_c_stream(raw: RawCStream) -> Self {
        Self { raw }
    }
}

impl IntoRawCStream for OwnedCStream {
    fn into_raw_c_stream(self) -> RawCStream {
        let raw = self.raw;
        mem::forget(self);
        raw
    }
}

#[cfg(feature = "alloc")]
#[derive(Debug)]
pub struct BufferedCStream {
    stream: OwnedCStream,
    #[allow(unused)]
    buffer: alloc::boxed::Box<[u8]>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BufferMode {
    Block,
    Line,
}

#[cfg(feature = "alloc")]
impl BufferedCStream {
    pub fn new(stream: OwnedCStream, size: usize, mode: BufferMode) -> Option<Self> {
        let mut buffer = alloc::vec![0; size].into_boxed_slice();
        match unsafe {
            libc::setvbuf(
                ptr(&stream),
                buffer.as_mut_ptr().cast::<c_char>(),
                match mode {
                    BufferMode::Block => libc::_IOFBF,
                    BufferMode::Line => libc::_IONBF,
                },
                buffer.len(),
            )
        } {
            0 => Some(Self { stream, buffer }),
            _ => None,
        }
    }
}

#[cfg(feature = "alloc")]
impl AsCStream for BufferedCStream {
    fn as_c_stream(&self) -> BorrowedCStream<'_> {
        self.stream.as_c_stream()
    }
}

#[cfg(feature = "alloc")]
impl AsRawCStream for BufferedCStream {
    fn as_raw_c_stream(&self) -> RawCStream {
        self.stream.as_raw_c_stream()
    }
}

/// A borrowed [`RawCStream`].
///
/// This has a lifetime parameter to tie it to the lifetime of something that owns the stream.
/// For the duration of that lifetime, it is guaranteed that nobody will close the stream.
///
/// This uses `#[repr(transparent)]` and has the representation of a host stream,
/// so it can be used in FFI in places where a file descriptor is passed as an argument,
/// it is not captured or consumed, and it never has the value `NULL`.
///
/// This type’s [`Clone`] implementation returns another [`BorrowedCStream`] rather than an [`OwnedCStream`].
/// It just makes a trivial copy of the raw file descriptor,
/// which is then borrowed under the same lifetime.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct BorrowedCStream<'a> {
    raw: RawCStream,
    lifetime: PhantomData<&'a OwnedCStream>,
}

impl<'a> BorrowedCStream<'a> {
    /// Return a [`BorrowedCStream`] holding the given stream.
    ///
    /// # Safety
    /// The resource pointed to by `raw` must remain open for the duration of the returned [`BorrowedCStream`].
    pub const unsafe fn borrow_raw(raw: RawCStream) -> Self {
        Self {
            raw,
            lifetime: PhantomData,
        }
    }
}

impl AsCStream for BorrowedCStream<'_> {
    fn as_c_stream(&self) -> BorrowedCStream<'_> {
        *self
    }
}

impl AsRawCStream for BorrowedCStream<'_> {
    fn as_raw_c_stream(&self) -> RawCStream {
        self.raw
    }
}

macro_rules! pointer_impls {
    ($trait:ident, $method:ident, $return:ty) => {
        impl<T: $trait + ?Sized> $trait for &T {
            fn $method(&self) -> $return {
                T::$method(self)
            }
        }
        impl<T: $trait + ?Sized> $trait for &mut T {
            fn $method(&self) -> $return {
                T::$method(self)
            }
        }
        #[cfg(feature = "alloc")]
        impl<T: $trait + ?Sized> $trait for alloc::boxed::Box<T> {
            fn $method(&self) -> $return {
                T::$method(self)
            }
        }
        #[cfg(feature = "alloc")]
        impl<T: $trait + ?Sized> $trait for alloc::rc::Rc<T> {
            fn $method(&self) -> $return {
                T::$method(self)
            }
        }
        #[cfg(feature = "alloc")]
        impl<T: $trait + ?Sized> $trait for alloc::sync::Arc<T> {
            fn $method(&self) -> $return {
                T::$method(self)
            }
        }
    };
}

/// A trait to borrow a stream from an underlying object.
pub trait AsCStream {
    /// Borrows the stream.
    fn as_c_stream(&self) -> BorrowedCStream<'_>;
}
pointer_impls!(AsCStream, as_c_stream, BorrowedCStream<'_>);

/// A trait to extract the raw stream from an underlying object.
pub trait AsRawCStream {
    /// Extracts the raw stream.
    ///
    /// This function is typically used to borrow an owned stream.
    /// When used in this way,
    /// this method does not pass ownership of the raw stream to the caller,
    /// and the stream is only guaranteed to be valid while the original object has not yet been destroyed.
    ///
    /// However, borrowing is not strictly required.
    /// See [`AsCStream::as_c_stream`] for an API which strictly borrows a stream.
    fn as_raw_c_stream(&self) -> RawCStream;
}
pointer_impls!(AsRawCStream, as_raw_c_stream, RawCStream);

/// A trait to express the ability to construct an object from a raw stream.
pub trait FromRawCStream {
    /// Constructs a new instance of `Self` from the given raw stream.
    ///
    /// This function is typically used to consume ownership of the specified stream.
    /// When used in this way,
    /// the returned object will take responsibility for closing it when the object goes out of scope.
    ///
    /// # Safety
    /// - The stream passed in must be an [owned stream](https://doc.rust-lang.org/std/io/index.html#io-safety); in particular, it must be open.
    unsafe fn from_raw_c_stream(raw: RawCStream) -> Self;
}
impl FromRawCStream for RawCStream {
    unsafe fn from_raw_c_stream(raw: RawCStream) -> Self {
        raw
    }
}

/// A trait to express the ability to consume an object and acquire ownership of its raw stream.
pub trait IntoRawCStream {
    /// Consumes this object, returning the raw underlying stream.
    ///
    /// This function is typically used to transfer ownership of the underlying stream to the caller.
    /// When used in this way,
    /// callers are then the unique owners of the file descriptor and must close it once it’s no longer needed.
    fn into_raw_c_stream(self) -> RawCStream;
}

impl IntoRawCStream for RawCStream {
    fn into_raw_c_stream(self) -> RawCStream {
        self
    }
}

//////////////////////
// Operations on files
//////////////////////

pub fn tmpfile() -> Option<OwnedCStream> {
    let raw = NonNull::new(unsafe { libc::tmpfile() })?;
    Some(unsafe { OwnedCStream::from_raw_c_stream(raw) })
}

//////////////
// File access
//////////////

/// Take `&T` to ensure that `stream` is alive for the outer scope
fn ptr<T: AsCStream>(stream: &T) -> *mut libc::FILE {
    stream.as_c_stream().as_raw_c_stream().as_ptr()
}

#[allow(clippy::result_unit_err)]
pub fn flush<T: AsCStream>(stream: T) -> Result<(), ()> {
    let ret = unsafe { libc::fflush(ptr(&stream)) };
    match ret {
        0 => Ok(()),
        libc::EOF => Err(()),
        _undocumented => Err(()),
    }
}

pub fn open(filename: &CStr, mode: &CStr) -> Option<OwnedCStream> {
    let raw = NonNull::new(unsafe { libc::fopen(filename.as_ptr(), mode.as_ptr()) })?;
    Some(unsafe { OwnedCStream::from_raw_c_stream(raw) })
}

pub fn reopen(filename: Option<&CStr>, mode: &CStr, stream: OwnedCStream) -> Option<OwnedCStream> {
    let raw = NonNull::new(unsafe {
        libc::freopen(
            filename.map(CStr::as_ptr).unwrap_or_else(ptr::null),
            mode.as_ptr(),
            stream.into_raw_c_stream().as_ptr(),
        )
    })?;
    Some(unsafe { OwnedCStream::from_raw_c_stream(raw) })
}

pub fn fileno<T: AsCStream>(stream: T) -> Option<c_int> {
    match unsafe { libc::fileno(ptr(&stream)) } {
        -1 => None,
        other => Some(other),
    }
}

/////////////////////////
// Character input/output
/////////////////////////
pub fn getc<T: AsCStream>(stream: T) -> Option<u8> {
    match unsafe { libc::fgetc(ptr(&stream)) } {
        libc::EOF => None,
        it => Some(it as u8),
    }
}

#[allow(clippy::result_unit_err)]
pub fn ungetc<T: AsCStream>(char: u8, stream: T) -> Result<(), ()> {
    match unsafe { libc::ungetc(char as c_int, ptr(&stream)) } {
        libc::EOF => Err(()),
        _ => Ok(()),
    }
}

pub fn gets<T: AsCStream>(buf: &mut [u8], stream: T) -> Option<&CStr> {
    match unsafe {
        libc::fgets(
            buf.as_mut_ptr().cast::<c_char>(),
            buf.len().try_into().ok()?,
            ptr(&stream),
        )
    }
    .is_null()
    {
        true => None,
        false => CStr::from_bytes_until_nul(buf).ok(),
    }
}

#[allow(clippy::result_unit_err, clippy::if_same_then_else)]
pub fn putc<T: AsCStream>(char: u8, stream: T) -> Result<(), ()> {
    let ret = unsafe { libc::fputc(char as c_int, ptr(&stream)) };
    if ret == libc::EOF {
        Err(())
    } else {
        Ok(())
    }
}

#[allow(clippy::result_unit_err)]
pub fn puts<T: AsCStream>(s: &CStr, stream: T) -> Result<(), ()> {
    let ret = unsafe { libc::fputs(s.as_ptr(), ptr(&stream)) };
    if ret == libc::EOF {
        Err(())
    } else if ret > 0 {
        Ok(())
    } else {
        Err(()) // undocumented
    }
}

//////////////////////
// Direct input/output
//////////////////////

pub fn read<T: AsCStream>(buf: &mut [u8], stream: T) -> usize {
    unsafe {
        libc::fread(
            buf.as_mut_ptr().cast::<c_void>(),
            1,
            buf.len(),
            ptr(&stream),
        )
    }
}

pub fn write<T: AsCStream>(buf: &[u8], stream: T) -> usize {
    unsafe { libc::fwrite(buf.as_ptr().cast::<c_void>(), 1, buf.len(), ptr(&stream)) }
}
///////////////////
// File positioning
///////////////////
#[cfg(feature = "std")]
#[allow(clippy::result_unit_err)]
pub fn seek<T: AsCStream>(stream: T, pos: std::io::SeekFrom) -> Result<(), ()> {
    let (offset, whence) = match pos {
        std::io::SeekFrom::Start(it) => (it.try_into().map_err(|_| ())?, libc::SEEK_SET),
        std::io::SeekFrom::End(it) => (it, libc::SEEK_END),
        std::io::SeekFrom::Current(it) => (it, libc::SEEK_CUR),
    };
    match unsafe { libc::fseek(ptr(&stream), offset, whence) } {
        0 => Ok(()),
        -1 => Err(()),
        _undocumented => Err(()),
    }
}

pub fn tell<T: AsCStream>(stream: T) -> Option<u64> {
    unsafe { libc::ftell(ptr(&stream)) }.try_into().ok()
}

pub fn rewind<T: AsCStream>(stream: T) {
    unsafe { libc::rewind(ptr(&stream)) }
}

/////////////////
// Error-handling
/////////////////

pub fn eof<T: AsCStream>(stream: T) -> bool {
    unsafe { libc::feof(ptr(&stream)) != 0 }
}

pub fn clear_errors<T: AsCStream>(stream: T) {
    unsafe { libc::clearerr(ptr(&stream)) }
}

/// A capture of the error indicator on a [`RawCStream`].
#[derive(Debug, Clone)]
pub struct FError(pub i32);

impl FError {
    pub fn of<T: AsCStream>(stream: T) -> Self {
        Self(unsafe { libc::ferror(ptr(&stream)) })
    }
}

impl fmt::Display for FError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("error indicator {} was set on stream", self.0))
    }
}

#[cfg(feature = "std")]
impl std::error::Error for FError {}

#[cfg(all(test, feature = "std"))]
fn read_to_string(mut f: impl std::io::Read) -> String {
    let mut s = String::new();
    f.read_to_string(&mut s).unwrap();
    s
}

#[cfg(all(test, feature = "std"))]
mod tests {
    use super::*;
    use std::{ffi::CString, fs, os::unix::ffi::OsStrExt as _};
    use tempfile::NamedTempFile;

    #[test]
    fn test() {
        let named = NamedTempFile::new().unwrap();
        let path = CString::new(named.path().as_os_str().as_bytes()).unwrap();
        let stream = open(&path, c"rw+").unwrap();
        assert_eq!(write(b"hello, world!", stream), 13);
        assert_eq!(fs::read_to_string(named.path()).unwrap(), "hello, world!");
    }
}
