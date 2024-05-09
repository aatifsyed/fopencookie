use std::{
    borrow::Borrow,
    io::{self, SeekFrom},
    marker::PhantomData,
    ptr::NonNull,
    slice,
};

use fopencookie_sys as sys;
use libc::{c_char, c_int, c_long, c_void, off_t, size_t};

#[derive(Debug, Clone, Copy)]
pub struct Builder<T> {
    funcs: sys::cookie_io_functions_t,
    _phantom: PhantomData<fn() -> T>,
}

impl<T> Builder<T> {
    pub const fn new() -> Self {
        Self {
            funcs: sys::cookie_io_functions_t {
                read: None,
                write: None,
                seek: None,
                close: Some({
                    unsafe extern "C" fn do_drop<T>(cookie: *mut c_void) -> c_int {
                        drop(Box::from_raw(cookie.cast::<T>()));
                        0
                    }
                    do_drop::<T>
                }),
            },
            _phantom: PhantomData,
        }
    }
    pub const fn reading(mut self) -> Self
    where
        T: io::Read,
    {
        unsafe extern "C" fn read<T: io::Read>(
            cookie: *mut c_void,
            buf: *mut c_char,
            len: size_t,
        ) -> c_long {
            let reader: &mut T = &mut *cookie.cast::<T>();
            let buf = slice::from_raw_parts_mut(buf.cast::<u8>(), len);
            reader
                .read(buf)
                .map_err(setting_errno)
                .and_then(|n| n.try_into().map_err(|_| set_errno(libc::EOVERFLOW)))
                .unwrap_or(-1)
        }
        self.funcs.read = Some(read::<T>);
        self
    }
    pub const fn seeking(mut self) -> Self
    where
        T: io::Seek,
    {
        unsafe extern "C" fn seek<T: io::Seek>(
            cookie: *mut c_void,
            offset: *mut off_t,
            whence: c_int,
        ) -> c_int {
            let seeker: &mut T = &mut *cookie.cast::<T>();
            let offset = *offset;
            let pos = match whence {
                libc::SEEK_SET => match offset.try_into() {
                    Ok(it) => SeekFrom::Start(it),
                    Err(_) => {
                        set_errno(libc::EOVERFLOW);
                        return -1;
                    }
                },
                libc::SEEK_CUR => SeekFrom::Current(offset),
                libc::SEEK_END => SeekFrom::End(offset),
                _ => panic!("invalid value for `whence`: {}", whence),
            };
            match seeker.seek(pos).map_err(setting_errno) {
                Ok(_) => 0,
                Err(_) => -1,
            }
        }
        self.funcs.seek = Some(seek::<T>);
        self
    }
    pub const fn writing(mut self) -> Self
    where
        T: io::Write,
    {
        unsafe extern "C" fn write<T: io::Write>(
            cookie: *mut c_void,
            buf: *const c_char,
            len: size_t,
        ) -> c_long {
            let writer: &mut T = &mut *cookie.cast::<T>();
            let buf = slice::from_raw_parts(buf.cast::<u8>(), len);
            writer
                .write(buf)
                .map_err(setting_errno)
                .and_then(|n| n.try_into().map_err(|_| set_errno(libc::EOVERFLOW)))
                .unwrap_or_default()
        }
        unsafe extern "C" fn flush_and_drop<T: io::Write>(cookie: *mut c_void) -> c_int {
            let writer: &mut T = &mut *cookie.cast::<T>();
            let ret = writer
                .flush()
                .map(|_| 0)
                .map_err(setting_errno)
                .unwrap_or(libc::EOF);
            drop(Box::from_raw(cookie.cast::<T>()));
            ret
        }
        self.funcs.write = Some(write::<T>);
        self.funcs.close = Some(flush_and_drop::<T>);
        self
    }
}

impl<T> Builder<T> {
    pub fn fopen(self, io: T) -> Option<NonNull<libc::FILE>> {
        let Self { funcs, _phantom } = self;
        let modes = match funcs {
            sys::cookie_io_functions_t {
                read: None,
                write: None,
                seek: _,
                close: _,
            } => c"",
            sys::cookie_io_functions_t {
                read: Some(_),
                write: None,
                seek: _,
                close: _,
            } => c"r",
            sys::cookie_io_functions_t {
                read: None,
                write: Some(_),
                seek: _,
                close: _,
            } => c"w",
            sys::cookie_io_functions_t {
                read: Some(_),
                write: Some(_),
                seek: _,
                close: _,
            } => c"rw",
        };
        NonNull::new(unsafe {
            sys::fopencookie(
                Box::into_raw(Box::new(io)).cast::<c_void>(),
                modes.as_ptr(),
                funcs,
            )
            .cast::<libc::FILE>()
        })
    }
}

fn setting_errno(e: impl Borrow<io::Error>) {
    if let Some(errno) = e.borrow().raw_os_error() {
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

    #[test]
    fn test() {
        let mut v = vec![];
        let file = Builder::new().writing().fopen(&mut v).unwrap();
        unsafe {
            libc::fprintf(file.as_ptr(), c"hello, world!".as_ptr());
            libc::fclose(file.as_ptr());
        };
        assert_eq!(v, b"hello, world!");
    }
}
