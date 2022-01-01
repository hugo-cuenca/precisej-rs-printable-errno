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
//! ## Why not Termination?
//! As of 2021-12-10, [std::process::Termination] is unstable and requires
//! the `termination_trait_lib` feature, which can only be activated in
//! nightly versions of Rust. Not all programs can make use of nightly (some,
//! such as `initd`, deny the use of unstable features in its codebase),
//! for which this crate exists.
//!
//! Not all of this library's functionality can be replicated with
//! [std::process::Termination], so this library can be of use even for users
//! of nightly Rust, albeit somewhat awkwardly. Future versions of
//! `precisej-printable-errno` will optionally include an implementation of
//! [std::process::Termination] for [ExitError] as a non-default feature for
//! interested nightly users.
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
//! pub fn start() -> Result<(), ExitError<String>> {
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
//!         .printable(PROGRAM_NAME, format!("unable to open {}", "/path/to/nonexistent/file"))
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
        Debug,
        Display,
        Formatter,
    },
    process::exit,
};
use nix::{
    errno::Errno,
    libc::{STDERR_FILENO, _exit, write},
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
pub struct PrintableErrno<S: AsRef<str>> {
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
    message: S,

    /// The originating [Errno] value. This is always present unless this `PrintableErrno`
    /// originates from a call to [printable_error].
    errno: Option<Errno>,
}
impl <S: AsRef<str>> PrintableErrno<S> {
    /// Attach an exit code to the Error. Useful for bubbling up errors from a deep
    /// function using the `?` operator.
    pub fn bail(self, exit_code: i32) -> ExitError<S> {
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
        // XXX: Is writev signal-safe?
        // signal-safety(7) lists write(2) as signal-safe, but not writev(2).
        // However writev(2) states:
        //     The writev() system call works just like write(2) except that
        //     multiple buffers are written out.
        // Since write(2) is signal-safe, and writev(2) claims to work like
        // write(2), is its omission from signal-safety(7) an oversight? Or
        // is there some other undocumented, unexplained difference between
        // them? Furthermore, since writev(2)'s signal-safety is unclear, can
        // we rely on POSIX-compliant OSes and libc/library authors to not
        // introduce any point of unsafety in this regard? i.e. even if the
        // CSRG issues a revision to the POSIX standard tomorrow that explicitly
        // requires writev(2) to be signal-safe, can we be sure that all
        // supported Linux versions comply, as well as all supported glibc/musl
        // versions in use?
        // Further reading:
        // https://groups.google.com/g/comp.unix.programmer/c/IfHr5I8NwW0
        // https://pubs.opengroup.org/onlinepubs/9699919799/functions/V2_chap02.html
        // https://austingroupbugs.net/view.php?id=1455
        const CONST_COLON: &'static [u8] = b": ";
        const CONST_NEWLINE: &'static [u8] = b"\n";

        let program_name = &self.program_name.as_bytes();
        let message = &self.message.as_ref().as_bytes();
        let res = write_stderr(program_name);
        if !res {
            // error writing to stderr: there is nothing left to do
            return;
        }

        write_stderr(CONST_COLON);
        write_stderr(message);

        let errno = self.errno.as_ref();
        if let Some(errno) = errno {
            let desc = errno.desc().as_bytes();
            write_stderr(CONST_COLON);
            write_stderr(desc);
        }
        write_stderr(CONST_NEWLINE);

        fn write_stderr(buf: &[u8]) -> bool {
            let mut pos = buf.as_ptr() as usize;
            let mut len = buf.len();
            loop {
                let res = unsafe { write(STDERR_FILENO, pos as *const c_void, len) };
                match res {
                    0 => break true,
                    e if e < 0 => {
                        let err = Errno::last();
                        if !matches!(err, Errno::EINTR) {
                            break false;
                        }
                        // EINTR means we can try again, so continue loop
                    }
                    // written will always be positive
                    w if (w as usize) < len => {
                        let written = w as usize;
                        pos += written;
                        len -= written;
                        // try again with remaining
                    }
                    _ => break true,
                }
            }
        }
    }
}
impl <S: AsRef<str>> Display for PrintableErrno<S> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.errno {
            Some(errno) => write!(f, "{}: {}: {}", self.program_name, self.message.as_ref(), errno.desc()),
            None => write!(f, "{}: {}", self.program_name, self.message.as_ref()),
        }
    }
}
impl <S: AsRef<str> + Debug> Error for PrintableErrno<S> {
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
pub struct ExitError<S: AsRef<str>> {
    exit_code: i32,
    errno: PrintableErrno<S>,
}
impl <S: AsRef<str>> ExitError<S> {
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
impl <S: AsRef<str>> Display for ExitError<S> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.errno.fmt(f)
    }
}
impl <S: AsRef<str> + Debug> Error for ExitError<S> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        self.errno.source()
    }
}

// ***

/// This trait defines a [Result] with a nix [Errno], facilitating the conversion
/// of the error to [PrintableErrno].
pub trait ErrnoResult<T> {
    /// Maps the nix [Errno] to a [PrintableErrno] with the program name and the
    /// supplied message. This allows [nix::Result]s to be easily used with this
    /// library's error handling and Rust's `?` operator.
    fn printable<S: AsRef<str>>(self, program_name: &'static str, message: S) -> Result<T, PrintableErrno<S>>;
}
impl <T> ErrnoResult<T> for Result<T, Errno> {
    fn printable<S: AsRef<str>>(self, program_name: &'static str, message: S) -> Result<T, PrintableErrno<S>> {
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
pub trait PrintableResult<T, S: AsRef<str>> {
    /// Maps the [PrintableErrno] to an [ExitError] in order to facilitate
    /// bubbling up the error to the appropriate place to quit the program.
    fn bail(self, exit_code: i32) -> Result<T, ExitError<S>>;

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
impl <T, S: AsRef<str>> PrintableResult<T, S> for Result<T, PrintableErrno<S>> {
    fn bail(self, exit_code: i32) -> Result<T, ExitError<S>> {
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
impl <T, S: AsRef<str>> ExitErrorResult<T> for Result<T, ExitError<S>> {
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
pub fn printable_error<S: AsRef<str>>(program_name: &'static str, message: S) -> PrintableErrno<S> {
    PrintableErrno {
        program_name,
        message: message.into(),
        errno: None
    }
}

// ***

impl From<PrintableErrno<&'_ str>> for PrintableErrno<String> {
    fn from(item: PrintableErrno<&'_ str>) -> Self {
        PrintableErrno {
            program_name: item.program_name,
            message: item.message.to_string(),
            errno: item.errno,
        }
    }
}

impl From<ExitError<&'_ str>> for ExitError<String> {
    fn from(item: ExitError<&'_ str>) -> Self {
        ExitError {
            exit_code: item.exit_code,
            errno: item.errno.into(),
        }
    }
}

// ***

#[cfg(test)]
mod tests {
    use nix::errno::Errno;
    use nix::fcntl::{open, OFlag};
    use nix::sys::stat::Mode;
    use crate::{ErrnoResult, PrintableResult, printable_error, PrintableErrno, ExitError, ExitErrorResult};

    const TEST_NAME: &str = "precisej-printable-errno";

    #[test]
    fn printable_message_witherrno() {
        println!();
        println!("START TEST 1");

        const MSG1_NAME: &str = "test1: unable to open /pathto/nonexistent/file";

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

        const MSG2_NAME: &str = "test2: expected value 1, got 30";

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

        const MSG3_NAME: &str = "test3: unable to open /pathto/nonexistent/file";
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
    fn eprint_signal_safe() {
        println!();
        println!("START TEST 4");

        const MSG4_NAME_1: &str = "test4: unable to open /pathto/nonexistent/file";
        const MSG4_NAME_2: &str = "test4: expected value 1, got 30";

        let result1 = open("/pathto/nonexistent/file", OFlag::O_RDONLY, Mode::empty())
            .printable(TEST_NAME, MSG4_NAME_1);
        result1.ok_or_eprint_signal_safe();

        let result2 = printable_error(TEST_NAME, MSG4_NAME_2);
        let result3 = printable_error(TEST_NAME, MSG4_NAME_2);
        result2.eprint_signalsafe();
        result3.eprint_signalsafe();

        println!("END TEST 4");
    }

    #[test]
    fn from_str_into_string() {
        println!();
        println!("START TEST 5");

        const MSG5_NAME: &str = "test5: expected value 1, got 30";

        let result1 = printable_error(TEST_NAME, MSG5_NAME);
        let result2 = printable_error(TEST_NAME, MSG5_NAME).bail(2);
        let result3: PrintableErrno<String> = result1.into();
        let _: ExitError<String> = result2.into();

        result3.eprint();

        internal_test_5_fn_result_1().ok_or_eprint();
        internal_test_5_fn_result_2().ok_or_eprint();

        println!("END TEST 5");

        fn internal_test_5_fn_result_1() -> Result<(), PrintableErrno<String>> {
            Err::<(), PrintableErrno<&'static str>>(printable_error(TEST_NAME, MSG5_NAME))?;
            Ok(())
        }
        fn internal_test_5_fn_result_2() -> Result<(), ExitError<String>> {
            Err::<(), PrintableErrno<&'static str>>(printable_error(TEST_NAME, MSG5_NAME)).bail(2)?;
            Ok(())
        }
    }
}
