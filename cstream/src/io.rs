use crate::{ptr, AsCStream, FError};
use libc::c_void;
use std::io;

/// A wrapper around an [`AsCStream`] that implements [`io::Read`], [`io::Write`]
/// and [`io::Seek`] through [`libc`] functions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Io<T>(pub T);

impl<T: AsCStream> io::Read for Io<T> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let n = unsafe {
            libc::fread(
                buf.as_mut_ptr().cast::<c_void>(),
                1,
                buf.len(),
                ptr(&self.0),
            )
        };
        if n == 0 {
            match (buf.len(), super::eof(&self.0), FError::of(&self.0)) {
                (0, _, _) => Ok(0),
                (_, true, _) => Ok(0),
                (_, _, e) => Err(io::Error::other(e)),
            }
        } else {
            Ok(n)
        }
    }
}

impl<T: AsCStream> io::Write for Io<T> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let n = unsafe { libc::fwrite(buf.as_ptr().cast::<c_void>(), 1, buf.len(), ptr(&self.0)) };
        if n == 0 {
            if buf.is_empty() {
                Ok(0)
            } else {
                Err(io::Error::last_os_error())
            }
        } else {
            Ok(n)
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        match unsafe { libc::fflush(ptr(&self.0)) } {
            0 => Ok(()),
            libc::EOF => Err(io::Error::last_os_error()),
            _undocumented => Err(io::Error::last_os_error()),
        }
    }
}

impl<T: AsCStream> io::Seek for Io<T> {
    fn seek(&mut self, pos: io::SeekFrom) -> io::Result<u64> {
        let (offset, whence) = match pos {
            io::SeekFrom::Start(it) => match it.try_into() {
                Ok(it) => (it, libc::SEEK_SET),
                Err(e) => return Err(io::Error::new(io::ErrorKind::Other, e)),
            },
            io::SeekFrom::End(it) => (it, libc::SEEK_END),
            io::SeekFrom::Current(it) => (it, libc::SEEK_CUR),
        };
        match unsafe { libc::fseek(ptr(&self.0), offset, whence) } {
            0 => unsafe { libc::ftell(ptr(&self.0)) }
                .try_into()
                .map_err(|_| io::Error::last_os_error()),
            -1 => Err(io::Error::last_os_error()),
            _undocumented => Err(io::Error::last_os_error()),
        }
    }
}

#[cfg(test)]
mod tests {
    use core::ptr::NonNull;
    use std::{
        io::{Seek, Write},
        os::fd::AsRawFd as _,
    };

    use tempfile::tempfile;

    use crate::{read_to_string, BorrowedCStream};

    use super::*;

    #[test]
    fn test() {
        let mut file = tempfile().unwrap();
        let stream =
            NonNull::new(unsafe { libc::fdopen(file.as_raw_fd(), c"r+".as_ptr()) }).unwrap();
        let mut stream = Io(unsafe { BorrowedCStream::borrow_raw(stream) });
        stream.write_all(b"hello, world!").unwrap();
        stream.flush().unwrap();
        file.rewind().unwrap();
        assert_eq!(read_to_string(file), "hello, world!");
    }
}
