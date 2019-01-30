macro_rules! arg_check {
    ( $vm: ident, $args:ident ) => {
        // Zero-arg case
        if $args.args.len() != 0 {
            return Err($vm.new_type_error(format!(
                "Expected no arguments (got: {})", $args.args.len())));
        }
    };
    ( $vm: ident, $args:ident, required=[$( ($arg_name:ident, $arg_type:expr) ),*] ) => {
        arg_check!($vm, $args, required=[$( ($arg_name, $arg_type) ),*], optional=[]);
    };
    ( $vm: ident, $args:ident, required=[$( ($arg_name:ident, $arg_type:expr) ),*], optional=[$( ($optional_arg_name:ident, $optional_arg_type:expr) ),*] ) => {
        let mut expected_args: Vec<(usize, &str, Option<PyObjectRef>)> = vec![];
        let mut arg_count = 0;

        $(
            if arg_count >= $args.args.len() {
                // TODO: Report the number of expected arguments
                return Err($vm.new_type_error(format!(
                    "Expected more arguments (got: {})",
                    $args.args.len()
                )));
            }
            expected_args.push((arg_count, stringify!($arg_name), $arg_type));
            let $arg_name = &$args.args[arg_count];
            #[allow(unused_assignments)]
            {
                arg_count += 1;
            }
        )*

        let minimum_arg_count = arg_count;

        $(
            let $optional_arg_name = if arg_count < $args.args.len() {
                expected_args.push((arg_count, stringify!($optional_arg_name), $optional_arg_type));
                let ret = Some(&$args.args[arg_count]);
                #[allow(unused_assignments)]
                {
                    arg_count += 1;
                }
                ret
            } else {
                None
            };
        )*

        if $args.args.len() < minimum_arg_count || $args.args.len() > expected_args.len() {
            let expected_str = if minimum_arg_count == arg_count {
                format!("{}", arg_count)
            } else {
                format!("{}-{}", minimum_arg_count, arg_count)
            };
            return Err($vm.new_type_error(format!(
                "Expected {} arguments (got: {})",
                expected_str,
                $args.args.len()
            )));
        };

        for (arg, (arg_position, arg_name, expected_type)) in
            $args.args.iter().zip(expected_args.iter())
        {
            match expected_type {
                Some(expected_type) => {
                    if !objtype::isinstance(arg, &expected_type) {
                        let arg_typ = arg.typ();
                        let expected_type_name = $vm.to_pystr(expected_type)?;
                        let actual_type = $vm.to_pystr(&arg_typ)?;
                        return Err($vm.new_type_error(format!(
                            "argument of type {} is required for parameter {} ({}) (got: {})",
                            expected_type_name,
                            arg_position + 1,
                            arg_name,
                            actual_type
                        )));
                    }
                }
                // None indicates that we have no type requirement (i.e. we accept any type)
                None => {}
            }
        }
    };
}

macro_rules! no_kwargs {
    ( $vm: ident, $args:ident ) => {
        // Zero-arg case
        if $args.kwargs.len() != 0 {
            return Err($vm.new_type_error(format!(
                "Expected no keyword arguments (got: {})",
                $args.kwargs.len()
            )));
        }
    };
}

/// Attempts to get the chain of attributes, returning an option that contains the value of
/// the last one.
///
/// ```rust,ignore
/// py_get_item!(($val).$attr1.$attr2.$...)
/// ```
///
/// # Examples
///
/// ```
/// # #[macro_use] extern crate rustpython_vm;
/// # fn main() {
/// # let mut vm = rustpython_vm::VirtualMachine::new();
/// let abs_func = py_get_item!((vm.sys_module).modules.__builtins__.abs);
/// # }
/// ```
#[macro_export]
macro_rules! py_get_item {
    ($val:ident.$($attr:ident).*) => {
        py_get_item!(($val).$($attr).*)
    };
    (($val:expr).$attr:ident.$($rest:ident).*) => {{
        use $crate::pyobject::DictProtocol;
        match $val.get_item(stringify!($attr)) {
            Some(val) => {
                py_get_item!((val).$($rest).*)
            },
            None => None,
        }
    }};
    (($val:expr).$attr:ident) => {
        py_get_item!(($val).$attr.)
    };
    (($val:expr).) => {
        Some($val)
    };
}
