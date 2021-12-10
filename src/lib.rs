//! # precisej-printable-errno
//! Printable system call errors for `nix`. **CURRENTLY IN DEVELOPMENT**
//!
//! # What?
//! `precisej-printable-errno` is a simple library that adds the
//! possibility of attaching a printable error message to every [Errno].
//! It additionally lets you add an integer error code that can be used
//! to exit the application.
//!
//! The library is intended to be used by lower-level applications that
//! intend to use `nix`'s Rust-friendly bindings to libc system functions.
//!
//! **Note**: `precisej-printable-errno`'s authors have no relationship
//! with the `nix-rust` maintainers.
//!
//! # Where?
//! Any system that `nix` supports should be supported by
//! `precisej-printable-errno`. To use this library, add
//! `precisej-printable-errno = "$LIB_VERSION"` (replacing `$LIB_VERSION`
//! with the latest version available in [crates.io](https://crates.io/)).
//!
//! Projects currently using `precisej-printable-errno`:
//! * initd
//!
//! If you are the author of another Rust project, are using the library,
//! and would like to be mentioned here, please contact me.
//!
//! # Why?
//! When writing initd, I found that there wasn't a straightforward way
//! to bubble up an exit code, and resorted to having a main() function
//! call a function which would return an `i32`, and then call
//! [std::process::exit] with the resulting error code. This was
//! unergonomic and bypassed Rust's excellent Result handling. Therefore
//! I decided to create special Error structs containing an error message
//! and an exit code, and since I found it useful I decided to turn it
//! into a library crate.
//!
//! I didn't find out how to do anything similar with other libraries
//! such as `anyhow`. If someone finds a better, equally lightweight
//! alternative please contact me.
//!
//! # How?
//! ```no_run
//! # use nix::fcntl::{OFlag, open};
//! # use nix::sys::stat::Mode;
//! # use nix::unistd::read;
//! # use precisej_printable_errno::{ErrnoResult, ExitError, PrintableResult};
//! /* use ... */
//!
//! const PROGRAM_NAME: &'static str = "example-program";
//!
//! pub fn main() {
//!     if let Err(e) = start() {
//!         e.eprint_and_exit()
//!     }
//! }
//!
//! pub fn start() -> Result<(), ExitError> {
//!     let init_file = open("/sbin/init", OFlag::O_RDONLY, Mode::empty())
//!         .printable(PROGRAM_NAME, "unable to open /sbin/init")
//!         .bail(1)?;
//!
//!     let mut buf = [0; 1024];
//!     read(init_file, &mut buf)
//!         .printable(PROGRAM_NAME, "unable to read first KB of /sbin/init")
//!         .bail(2)?;
//!
//!     drop(buf);
//!
//!     open("/path/to/nonexistent/file", OFlag::O_RDONLY, Mode::empty())
//!         .printable(PROGRAM_NAME, "unable to open /path/to/nonexistent/file")
//!         .bail(3)?;
//!
//!     // That last call should have caused the process to exit with
//!     // code 3 and the following error message:
//!     //
//!     // example-program: unable to open /path/to/nonexistent/file: No such file or directory
//!
//!     Ok(())
//! }
//! ```
#![crate_name = "precisej_printable_errno"]
#![cfg_attr(test, deny(warnings))]
#![deny(unused)]
#![deny(unstable_features)]
#![warn(missing_docs)]

use std::{
    error::Error,
    ffi::c_void,
    fmt::{
        Display,
        Formatter,
    },
    os::unix::io::RawFd,
    process::{abort, exit},
};
use nix::{
    errno::Errno,
    libc::{_exit, write},
};

/// This is the base struct containing basic error information. Unless
/// you call [printable_error] or you unwrap the error on a [Result]
/// containing a `PrintableErrno`, you probably won't use this directly.
///
/// When printed, the error message will look like the following:
/// * If there is an associated errno:
///   `$program_name: $message: ${errno.desc()}`
/// * If there is no errno (called from [printable_error]):
///   `$program_name: $message`
///
/// Printed error tries to follow `perror(3p)`'s format with the
/// addition of the program name.
#[derive(Debug)]
pub struct PrintableErrno {
    /// The name of the program responsible for generating this Error.
    /// This is normally the name of the final binary crate, usually
    /// saved as a const in the main.rs file.
    program_name: &'static str,

    /// The error message to be printed. While `PrintableErrno` can hold any valid String,
    /// we recommend you specify the name of the function you tried to call or the action
    /// you tried to perform. For example, if you are trying to call
    /// `open("/path/to/file", OFlag::O_RDONLY, Mode::empty())`, the message could be as
    /// simple as `open`, or more detailed like `unable to open /path/to/file`.
    /// `PrintableErrno` will fill in the description of the [Errno] if it was available.
    message: String,

    /// The originating [Errno] value. This is always present unless this `PrintableErrno`
    /// originates from a call to [printable_error].
    errno: Option<Errno>,
}
impl PrintableErrno {
    /// Attach an exit code to the Error. Useful for bubbling up errors from a deep
    /// function using the `?` operator.
    pub fn bail(self, exit_code: i32) -> ExitError {
        ExitError {
            exit_code,
            errno: self,
        }
    }

    /// Print the error to stderr.
    pub fn eprint(self) {
        eprintln!("{}", self);
    }

    /// Same as [PrintableErrno::eprint], but attempts to `write()` directly to stderr
    /// and not to call any non-signal-safe functions. Useful when one is the child
    /// in a multi-threaded program after a call to `fork()`.
    ///
    /// # Note
    /// No allocations should be made in this function in order to comply with `fork()`s
    /// contract of signal-safety.
    ///
    /// # Safety
    /// The caller must ensure that stderr (fd 2) remains open for the entirety of this
    /// function call. A naive attempt at detecting a closed file descriptor is made on
    /// first write. However, any subsequent writes may silently fail if stderr is closed
    /// while this function is running.
    pub fn eprint_signalsafe(&self) {
        const STDERR: RawFd = nix::libc::STDERR_FILENO;
        const CONST_COLON: &'static [u8] = b": ";
        const CONST_NEWLINE: &'static [u8] = b"\n";

        let program_name = &self.program_name.as_bytes();
        let message = &self.message.as_bytes();
        let res = unsafe { write(STDERR, program_name.as_ptr() as *const c_void, program_name.len()) };
        if res < 0 {
            // abort() should be signal-safe according to ISO C 99 (7.14.1.1p5).
            // However, some versions of POSIX (before 1003.1-2004) required abort()
            // to flush stdio streams, which would be hard (or impossible) to do
            // safely while upholding the contract. In fact there are glibc
            // implementations (before commit 91e7cf982d01) that perform the flush
            // unsafely.
            // Fortunately, Rust's stdlib makes no use of stdio buffering, so we
            // can assume that most unsafe abort() implementations will be safe
            // for us to call, as no buffer will be flushed.
            abort()
        }

        unsafe {
            write(STDERR, CONST_COLON.as_ptr() as *const c_void, CONST_COLON.len());
            write(STDERR, message.as_ptr() as *const c_void, message.len());
        }

        let errno = self.errno.as_ref();
        if let Some(errno) = errno {
            let desc = errno.desc().as_bytes();
            unsafe {
                write(STDERR, CONST_COLON.as_ptr() as *const c_void, CONST_COLON.len());
                write(STDERR, desc.as_ptr() as *const c_void, desc.len());
                write(STDERR, CONST_NEWLINE.as_ptr() as *const c_void, CONST_NEWLINE.len());
            }
        }
    }
}
impl Display for PrintableErrno {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.errno {
            Some(errno) => write!(f, "{}: {}: {}", self.program_name, self.message, errno.desc()),
            None => write!(f, "{}: {}", self.program_name, self.message),
        }
    }
}
impl Error for PrintableErrno {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self.errno {
            Some(ref x) => Some(x),
            None => None,
        }
    }
}

// ***

/// This struct contains an exit code and basic error information (from
/// [PrintableErrno]). Unless you unwrap the error on a [Result] containing
/// an `ExitError`, you probably won't use this directly.
///
/// When printed, the error message will look like the following:
/// * If there is an associated errno:
///   `$program_name: $message: ${errno.desc()}`
/// * If there is no errno (originally called from [printable_error]):
///   `$program_name: $message`
///
/// Printed error tries to follow `perror(3p)`'s format with the
/// addition of the program name.
///
/// `eprint_and_exit` and `eprint_signal_safe_exit` also call `exit(exit_code)`
/// and `_exit(exit_code)` respectively, exiting the process with the supplied
/// exit code.
#[derive(Debug)]
pub struct ExitError {
    exit_code: i32,
    errno: PrintableErrno,
}
impl ExitError {
    /// Print the error to stderr and exit with the supplied code.
    ///
    /// # Safety
    /// The caller must ensure that stderr (fd 2) is open.
    pub fn eprint_and_exit(self) -> ! {
        eprintln!("{}", self);
        exit(self.exit_code)
    }

    /// Same as [ExitError::eprint_and_exit], but attempts to `write()` directly to stderr
    /// and not to call any non-signal-safe functions. Useful when one is the child
    /// in a multi-threaded program after a call to `fork()`.
    ///
    /// # Safety
    /// The caller must ensure that stderr (fd 2) remains open for the entirety of this
    /// function call.
    ///
    /// `_exit` is safe to call from the fork()-ed child as it's signal-safe. However, it
    /// doesn't call destructors (as opposed to exiting from main) nor does it call any exit
    /// functions if they are set, so caller should only call this from a fork()-ed child.
    #[allow(unused_unsafe)]
    pub unsafe fn eprint_signal_safe_exit(self) -> ! {
        self.errno.eprint_signalsafe();
        unsafe {
            _exit(self.exit_code);
        }
    }
}
impl Display for ExitError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.errno.fmt(f)
    }
}
impl Error for ExitError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        Some(&self.errno)
    }
}

// ***

/// This trait defines a [Result] with a nix [Errno], facilitating the conversion
/// of the error to [PrintableErrno].
pub trait ErrnoResult<T> {
    /// Maps the nix [Errno] to a [PrintableErrno] with the program name and the
    /// supplied message. This allows [nix::Result]s to be easily used with this
    /// library's error handling and Rust's `?` operator.
    fn printable<S: Into<String>>(self, program_name: &'static str, message: S) -> Result<T, PrintableErrno>;
}
impl <T> ErrnoResult<T> for Result<T, Errno> {
    fn printable<S: Into<String>>(self, program_name: &'static str, message: S) -> Result<T, PrintableErrno> {
        self.map_err(|e| PrintableErrno {
            program_name,
            message: message.into(),
            errno: Some(e),
        })
    }
}

// ***

/// This trait defines a [Result] with our own [PrintableErrno], allowing further conversion
/// to [ExitError], or printing and returning and Option.
pub trait PrintableResult<T> {
    /// Maps the [PrintableErrno] to an [ExitError] in order to facilitate
    /// bubbling up the error to the appropriate place to quit the program.
    fn bail(self, exit_code: i32) -> Result<T, ExitError>;

    /// Consumes the result, prints the error (if present) to stderr, and returns
    /// an [Option] of the underlying value.
    ///
    /// # Safety
    /// The caller must ensure that stderr (fd 2) is open.
    fn ok_or_eprint(self) -> Option<T>;

    /// Same as [PrintableResult::ok_or_eprint], but attempts to `write()` directly
    /// to stderr and not to call any non-signal-safe functions. Useful when one is
    /// the child in a multi-threaded program after a call to `fork()`.
    ///
    /// # Safety
    /// The caller must ensure that stderr (fd 2) is open.
    fn ok_or_eprint_signal_safe(self) -> Option<T>;
}
impl <T> PrintableResult<T> for Result<T, PrintableErrno> {
    fn bail(self, exit_code: i32) -> Result<T, ExitError> {
        self.map_err(|e| e.bail(exit_code))
    }
    fn ok_or_eprint(self) -> Option<T> {
        match self {
            Ok(t) => Some(t),
            Err(e) => {
                e.eprint();
                None
            }
        }
    }

    fn ok_or_eprint_signal_safe(self) -> Option<T> {
        match self {
            Ok(t) => Some(t),
            Err(e) => {
                e.eprint_signalsafe();
                None
            }
        }
    }
}

// ***

/// This trait defines a [Result] with our own [ExitError]. This allows exiting the program
/// with the error code specified by the [ExitError], as well as consuming itself and
/// returning an [Option] after printing the Error to stderr.
///
/// **Note**: Normally, you should handle the error in the main function as in the provided
/// example (see **`How?`** in crate documentation), but these functions can be useful at
/// times when that might not be practical (for example, the child process failing an
/// [execve][nix::unistd::execve] after a successful [fork][nix::unistd::fork].
pub trait ExitErrorResult<T> {
    /// Similar to [Result::unwrap], but prints the error (if present) to stderr and exits with
    /// the specified exit code instead of causing the program to panic.
    ///
    /// **Note**: Normally, you should handle the error in the main function as in the provided
    /// example (see **`How?`** in crate documentation).
    ///
    /// # Safety
    /// The caller must ensure that stderr (fd 2) is open.
    fn unwrap_or_eprint_exit(self) -> T;

    /// Same as [ExitErrorResult::unwrap_or_eprint_exit], but attempts to `write()` directly
    /// to stderr and not to call any non-signal-safe functions. Useful when one is the child
    /// in a multi-threaded program after a call to `fork()`.
    ///
    /// # Safety
    /// The caller must ensure that stderr (fd 2) is open.
    ///
    /// `_exit` is safe to call from the fork()-ed child as it's signal-safe. However, it
    /// doesn't call destructors (as opposed to exiting from main) nor does it call any exit
    /// functions if they are set, so caller should only call this from a fork()-ed child.
    unsafe fn unwrap_or_eprint_signal_safe_exit(self) -> T;

    /// Consumes the result, prints the error (if present) to stderr, and returns
    /// an [Option] of the underlying value.
    ///
    /// # Safety
    /// The caller must ensure that stderr (fd 2) is open.
    fn ok_or_eprint(self) -> Option<T>;

    /// Same as [ExitErrorResult::ok_or_eprint], but attempts to `write()` directly
    /// to stderr and not to call any non-signal-safe functions. Useful when one is
    /// the child in a multi-threaded program after a call to `fork()`.
    ///
    /// # Safety
    /// The caller must ensure that stderr (fd 2) is open.
    fn ok_or_eprint_signal_safe(self) -> Option<T>;
}
impl <T> ExitErrorResult<T> for Result<T, ExitError> {
    fn unwrap_or_eprint_exit(self) -> T {
        match self {
            Ok(t) => t,
            Err(e) => e.eprint_and_exit()
        }
    }

    #[allow(unused_unsafe)]
    unsafe fn unwrap_or_eprint_signal_safe_exit(self) -> T {
        match self {
            Ok(t) => t,
            Err(e) => unsafe { e.eprint_signal_safe_exit() }
        }
    }

    fn ok_or_eprint(self) -> Option<T> {
        match self {
            Ok(t) => Some(t),
            Err(e) => {
                e.errno.eprint();
                None
            }
        }
    }

    fn ok_or_eprint_signal_safe(self) -> Option<T> {
        match self {
            Ok(t) => Some(t),
            Err(e) => {
                e.errno.eprint_signalsafe();
                None
            }
        }
    }
}

// ***

/// Creates an error out of the program name and the supplied message. Useful
/// when an Errno isn't present, but the program wants to signal a problem to
/// the user and possibly exit if it's fatal.
pub fn printable_error<S: Into<String>>(program_name: &'static str, message: S) -> PrintableErrno {
    PrintableErrno {
        program_name,
        message: message.into(),
        errno: None
    }
}

// ***

#[cfg(test)]
mod tests {
    use nix::errno::Errno;
    use nix::fcntl::{open, OFlag};
    use nix::sys::stat::Mode;
    use crate::{ErrnoResult, PrintableResult, printable_error};
    use nix::unistd::{fork, ForkResult};
    use nix::sys::wait::{waitpid, WaitStatus};

    const TEST_NAME: &str = "precisej-printable-errno";

    #[test]
    fn printable_message_witherrno() {
        println!();
        println!("START TEST 1");

        const MSG1_NAME: &str = "unable to open /pathto/nonexistent/file";

        let result1 = open("/pathto/nonexistent/file", OFlag::O_RDONLY, Mode::empty())
            .printable(TEST_NAME, MSG1_NAME);

        let result2 = open("/pathto/nonexistent/file", OFlag::O_RDONLY, Mode::empty())
            .printable(TEST_NAME, MSG1_NAME);

        result1.ok_or_eprint();
        assert_eq!(
            format!("{}", result2.unwrap_err()),
            format!("{}: {}: {}", TEST_NAME, MSG1_NAME, Errno::ENOENT.desc())
        );

        println!("END TEST 1");
    }

    #[test]
    fn printable_message_noerrno() {
        println!();
        println!("START TEST 2");

        const MSG2_NAME: &str = "expected value 1, got 30";

        let result1 = printable_error(TEST_NAME, MSG2_NAME);
        let result2 = printable_error(TEST_NAME, MSG2_NAME);

        result1.eprint();
        assert_eq!(
            format!("{}", result2),
            format!("{}: {}", TEST_NAME, MSG2_NAME)
        );

        println!("END TEST 2");
    }

    #[test]
    fn bail_correct() {
        println!();
        println!("START TEST 3");

        const MSG3_NAME: &str = "unable to open /pathto/nonexistent/file";
        const MSG3_EXIT_CODE: i32 = 1;

        let result1 = open("/pathto/nonexistent/file", OFlag::O_RDONLY, Mode::empty())
            .printable(TEST_NAME, MSG3_NAME)
            .bail(MSG3_EXIT_CODE);

        let result2 = open("/pathto/nonexistent/file", OFlag::O_RDONLY, Mode::empty())
            .printable(TEST_NAME, MSG3_NAME)
            .bail(MSG3_EXIT_CODE);

        let result1 = result1.unwrap_err();
        eprintln!("{}", result1.errno);
        eprintln!("Process finished with exit code {}.", result1.exit_code);
        assert_eq!(
            result2.unwrap_err().exit_code,
            MSG3_EXIT_CODE
        );

        println!("END TEST 3");
    }

    #[test]
    fn bail_signal_safe() {
        println!();
        println!("START TEST 4");

        const MSG4_NAME: &str = "SIGNAL_SAFE: unable to open /pathto/nonexistent/file: No such file or directory";
        const MSG4_EXIT_CODE: i32 = 1;

        match unsafe { fork() }.unwrap() {
            ForkResult::Parent { child } => {
                loop {
                    let waitpid = waitpid(child, None).unwrap();
                    match waitpid {
                        WaitStatus::Exited(_, code) => {
                            println!("CODE: {}", code);
                            assert_eq!(code, MSG4_EXIT_CODE);
                            break
                        }
                        WaitStatus::Signaled(_, _, _) => {
                            panic!("Child Signaled, expected Exited.")
                        }
                        _ => {
                            // Continue
                        }
                    }
                }
            }
            ForkResult::Child => unsafe {
                printable_error(TEST_NAME, MSG4_NAME).bail(MSG4_EXIT_CODE).eprint_signal_safe_exit()
            }
        }

        println!("END TEST 4");
    }
}
