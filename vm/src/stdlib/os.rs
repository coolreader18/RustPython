//library imports
use std::fs::File;
use std::fs::OpenOptions;
use std::io::ErrorKind;
// use std::env;

//3rd party imports
use num_traits::cast::ToPrimitive;

//custom imports
use crate::obj::objint;
use crate::obj::objstr;
// use crate::obj::objdict;

use crate::pyobject::{PyContext, PyFuncArgs, PyObjectRef, PyResult, TypeProtocol};
use crate::vm::VirtualMachine;

#[cfg(unix)]
pub fn raw_file_number(handle: File) -> i64 {
    use std::os::unix::io::IntoRawFd;

    i64::from(handle.into_raw_fd())
}

#[cfg(unix)]
pub fn rust_file(raw_fileno: i64) -> File {
    use std::os::unix::io::FromRawFd;

    unsafe { File::from_raw_fd(raw_fileno as i32) }
}

#[cfg(windows)]
pub fn raw_file_number(handle: File) -> i64 {
    use std::os::windows::io::IntoRawHandle;

    handle.into_raw_handle() as i64
}

#[cfg(windows)]
pub fn rust_file(raw_fileno: i64) -> File {
    use std::ffi::c_void;
    use std::os::windows::io::FromRawHandle;

    //This seems to work as expected but further testing is required.
    unsafe { File::from_raw_handle(raw_fileno as *mut c_void) }
}

#[cfg(all(not(unix), not(windows)))]
pub fn rust_file(raw_fileno: i64) -> File {
    unimplemented!();
}

#[cfg(all(not(unix), not(windows)))]
pub fn raw_file_number(handle: File) -> i64 {
    unimplemented!();
}

pub fn os_close(vm: &mut VirtualMachine, args: PyFuncArgs) -> PyResult {
    arg_check!(vm, args, required = [(fileno, Some(vm.ctx.int_type()))]);

    let raw_fileno = objint::get_value(&fileno);

    //The File type automatically closes when it goes out of scope.
    //To enable us to close these file descriptors (and hence prevent leaks)
    //we seek to create the relevant File and simply let it pass out of scope!
    rust_file(raw_fileno.to_i64().unwrap());

    Ok(vm.get_none())
}

pub fn os_open(vm: &mut VirtualMachine, args: PyFuncArgs) -> PyResult {
    arg_check!(
        vm,
        args,
        required = [
            (name, Some(vm.ctx.str_type())),
            (mode, Some(vm.ctx.int_type()))
        ]
    );

    let fname = objstr::get_value(&name);

    let handle = match objint::get_value(mode).to_u16().unwrap() {
        0 => OpenOptions::new().read(true).open(&fname),
        1 => OpenOptions::new().write(true).open(&fname),
        512 => OpenOptions::new().write(true).create(true).open(&fname),
        _ => OpenOptions::new().read(true).open(&fname),
    }
    .map_err(|err| match err.kind() {
        ErrorKind::NotFound => {
            let exc_type = vm.ctx.exceptions.file_not_found_error.clone();
            vm.new_exception(exc_type, format!("No such file or directory: {}", &fname))
        }
        ErrorKind::PermissionDenied => {
            let exc_type = vm.ctx.exceptions.permission_error.clone();
            vm.new_exception(exc_type, format!("Permission denied: {}", &fname))
        }
        _ => vm.new_value_error("Unhandled file IO error".to_string()),
    })?;

    Ok(vm.ctx.new_int(raw_file_number(handle)))
}

fn os_error(vm: &mut VirtualMachine, args: PyFuncArgs) -> PyResult {
    arg_check!(
        vm,
        args,
        required = [],
        optional = [(message, Some(vm.ctx.str_type()))]
    );

    let msg = if let Some(val) = message {
        objstr::get_value(&val)
    } else {
        "".to_string()
    };

    Err(vm.new_os_error(msg))
}

pub fn make_module(ctx: &PyContext) -> PyObjectRef {
    let py_mod = py_module!(ctx, "os", {
        "open" => ctx.new_rustfunc(os_open),
        "close" => ctx.new_rustfunc(os_close),
        "error" => ctx.new_rustfunc(os_error),
        "O_RDONLY" => ctx.new_int(0),
        "O_WRONLY" => ctx.new_int(1),
        "O_RDWR" => ctx.new_int(2),
        "O_NONBLOCK" => ctx.new_int(4),
        "O_APPEND" => ctx.new_int(8),
        "O_CREAT" => ctx.new_int(512)
    });

    if cfg!(windows) {
        ctx.set_attr(&py_mod, "name", ctx.new_str("nt".to_string()));
    } else {
        // Assume we're on a POSIX system
        ctx.set_attr(&py_mod, "name", ctx.new_str("posix".to_string()));
    }

    py_mod
}
