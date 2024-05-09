//! Owned and borrowed [`libc::FILE`] streams.
//!
//! This library's design largely mirrors that of [`std::os::fd`](https://doc.rust-lang.org/std/os/fd/index.html).

#![no_std]

use core::{marker::PhantomData, mem, ptr::NonNull};

/// A [`libc::FILE`] stream.
pub type RawCStream = NonNull<libc::FILE>;

/// An owned [`RawCStream`].
/// This closes the stream on drop.
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

/// A trait to borrow a stream from an underlying object.
pub trait AsCStream {
    /// Borrows the stream.
    fn as_c_stream(&self) -> BorrowedCStream<'_>;
}

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
/// A trait to express the ability to consume an object and acquire ownership of its raw stream.
pub trait IntoRawCStream {
    /// Consumes this object, returning the raw underlying stream.
    ///
    /// This function is typically used to transfer ownership of the underlying stream to the caller.
    /// When used in this way,
    /// callers are then the unique owners of the file descriptor and must close it once it’s no longer needed.
    fn into_raw_c_stream(self) -> RawCStream;
}
