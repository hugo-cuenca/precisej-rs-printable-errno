# precisej-printable-errno

Printable system call errors for `nix`. **CURRENTLY IN DEVELOPMENT**

## What?
`precisej-printable-errno` is a simple library that adds the
possibility of attaching a printable error message to every [Errno].
It additionally lets you add an integer error code that can be used
to exit the application.

The library is intended to be used by lower-level applications that
intend to use `nix`'s Rust-friendly bindings to libc system functions.

**Note**: `precisej-printable-errno`'s authors have no relationship
with the `nix-rust` maintainers.

## Where?
Any system that `nix` supports should be supported by
`precisej-printable-errno`. To use this library, add
`precisej-printable-errno = "$LIB_VERSION"` (replacing `$LIB_VERSION`
with the latest version available in [crates.io](https://crates.io/)).

Projects currently using `precisej-printable-errno`:
* initd

If you are the author of another Rust project, are using the library,
and would like to be mentioned here, please contact me.

## Why?
When writing initd, I found that there wasn't a straightforward way
to bubble up an exit code, and resorted to having a main() function
call a function which would return an `i32`, and then call
[std::process::exit] with the resulting error code. This was
unergonomic and bypassed Rust's excellent Result handling. Therefore
I decided to create special Error structs containing an error message
and an exit code, and since I found it useful I decided to turn it
into a library crate.

I didn't find out how to do anything similar with other libraries
such as `anyhow`. If someone finds a better, equally lightweight
alternative please contact me.

### Why not Termination?
As of 2021-12-10, [std::process::Termination] is unstable and requires
the `termination_trait_lib` feature, which can only be activated in
nightly versions of Rust. Not all programs can make use of nightly (some,
such as `initd`, deny the use of unstable features in its codebase),
for which this crate exists.

Not all of this library's functionality can be replicated with
[std::process::Termination], so this library can be of use even for users
of nightly Rust, albeit somewhat awkwardly. Future versions of
`precisej-printable-errno` will optionally include an implementation of
[std::process::Termination] for [ExitError] as a non-default feature for
interested nightly users.

## How?
```rust
/* use ... */

const PROGRAM_NAME: &'static str = "example-program";

pub fn main() {
    if let Err(e) = start() {
        e.eprint_and_exit()
    }
}

pub fn start() -> Result<(), ExitError<&'static str>> {
    let init_file = open("/sbin/init", OFlag::O_RDONLY, Mode::empty())
        .printable(PROGRAM_NAME, "unable to open /sbin/init")
        .bail(1)?;

    let mut buf = [0; 1024];
    read(init_file, &mut buf)
        .printable(PROGRAM_NAME, "unable to read first KB of /sbin/init")
        .bail(2)?;

    drop(buf);

    open("/path/to/nonexistent/file", OFlag::O_RDONLY, Mode::empty())
        .printable(PROGRAM_NAME, "unable to open /path/to/nonexistent/file")
        .bail(3)?;

    // That last call should have caused the process to exit with
    // code 3 and the following error message:
    //
    // example-program: unable to open /path/to/nonexistent/file: No such file or directory

    Ok(())
}
```

License: MIT
