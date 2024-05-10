use std::io;
use std::os::fd::{AsFd, AsRawFd};

use libc::c_void;

pub struct FdIo<T>(pub T);

impl<T: AsFd> io::Write for FdIo<T> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        unsafe {
            libc::write(
                self.0.as_fd().as_raw_fd(),
                buf.as_ptr().cast::<c_void>(),
                buf.len(),
            )
        }
        .try_into()
        .map_err(|_| io::Error::last_os_error())
    }

    fn flush(&mut self) -> io::Result<()> {
        match unsafe { libc::fsync(self.0.as_fd().as_raw_fd()) } {
            0 => Ok(()),
            -1 => Err(io::Error::last_os_error()),
            _undocumented => Err(io::Error::last_os_error()),
        }
    }
}

impl<T: AsFd> io::Read for FdIo<T> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        unsafe {
            libc::read(
                self.0.as_fd().as_raw_fd(),
                buf.as_mut_ptr().cast::<c_void>(),
                buf.len(),
            )
        }
        .try_into()
        .map_err(|_| io::Error::last_os_error())
    }
}

impl<T: AsFd> io::Seek for FdIo<T> {
    fn seek(&mut self, pos: io::SeekFrom) -> io::Result<u64> {
        todo!()
    }
}
