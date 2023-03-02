//! Parsing and processing for this form:
//! ```ignore
//! py_compile!(
//!     // either:
//!     source = "python_source_code",
//!     // or
//!     file = "file/path/relative/to/$CARGO_MANIFEST_DIR",
//!
//!     // the mode to compile the code in
//!     mode = "exec", // or "eval" or "single"
//!     // the path put into the CodeObject, defaults to "frozen"
//!     module_name = "frozen",
//! )
//! ```

use crate::Diagnostic;
use once_cell::sync::Lazy;
use proc_macro2::{Span, TokenStream};
use quote::quote;
use rustpython_compiler_core::{frozen_lib, CodeObject, Mode};
use std::{
    collections::HashMap,
    env, fs,
    path::{Path, PathBuf},
};
use syn::{
    self,
    parse::{Parse, ParseStream, Result as ParseResult},
    parse2, LitByteStr, LitStr, Token,
};

static CARGO_MANIFEST_DIR: Lazy<PathBuf> = Lazy::new(|| {
    PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR is not present"))
});

enum CompilationSourceKind {
    /// Source is a File (Path)
    File(PathBuf),
    /// Direct Raw sourcecode
    SourceCode(String),
    /// Source is a directory
    Dir(PathBuf),
}

struct CompiledModule {
    code: CodeObject,
    package: bool,
}

struct CompilationSource {
    kind: CompilationSourceKind,
    span: (Span, Span),
}

pub trait Compiler {
    fn compile(
        &self,
        source: &str,
        mode: Mode,
        module_name: String,
    ) -> Result<CodeObject, Box<dyn std::error::Error>>;
}

impl CompilationSource {
    fn compile_string<D: std::fmt::Display, F: FnOnce() -> D>(
        &self,
        source: &str,
        mode: Mode,
        module_name: String,
        compiler: &dyn Compiler,
        origin: F,
    ) -> Result<CodeObject, Diagnostic> {
        compiler.compile(source, mode, module_name).map_err(|err| {
            Diagnostic::spans_error(
                self.span,
                format!("Python compile error from {}: {}", origin(), err),
            )
        })
    }

    fn compile(
        &self,
        mode: Mode,
        module_name: String,
        compiler: &dyn Compiler,
    ) -> Result<HashMap<String, CompiledModule>, Diagnostic> {
        match &self.kind {
            CompilationSourceKind::Dir(rel_path) => self.compile_dir(
                &CARGO_MANIFEST_DIR.join(rel_path),
                String::new(),
                mode,
                compiler,
            ),
            _ => Ok(hashmap! {
                module_name.clone() => CompiledModule {
                    code: self.compile_single(mode, module_name, compiler)?,
                    package: false,
                },
            }),
        }
    }

    fn compile_single(
        &self,
        mode: Mode,
        module_name: String,
        compiler: &dyn Compiler,
    ) -> Result<CodeObject, Diagnostic> {
        match &self.kind {
            CompilationSourceKind::File(rel_path) => {
                let path = CARGO_MANIFEST_DIR.join(rel_path);
                let source = fs::read_to_string(&path).map_err(|err| {
                    Diagnostic::spans_error(
                        self.span,
                        format!("Error reading file {path:?}: {err}"),
                    )
                })?;
                self.compile_string(&source, mode, module_name, compiler, || rel_path.display())
            }
            CompilationSourceKind::SourceCode(code) => {
                self.compile_string(&textwrap::dedent(code), mode, module_name, compiler, || {
                    "string literal"
                })
            }
            CompilationSourceKind::Dir(_) => {
                unreachable!("Can't use compile_single with directory source")
            }
        }
    }

    fn compile_dir(
        &self,
        path: &Path,
        parent: String,
        mode: Mode,
        compiler: &dyn Compiler,
    ) -> Result<HashMap<String, CompiledModule>, Diagnostic> {
        let mut code_map = HashMap::new();
        let paths = fs::read_dir(path)
            .or_else(|e| {
                if cfg!(windows) {
                    if let Ok(real_path) = fs::read_to_string(path.canonicalize().unwrap()) {
                        return fs::read_dir(real_path.trim());
                    }
                }
                Err(e)
            })
            .map_err(|err| {
                Diagnostic::spans_error(self.span, format!("Error listing dir {path:?}: {err}"))
            })?;
        for path in paths {
            let path = path.map_err(|err| {
                Diagnostic::spans_error(self.span, format!("Failed to list file: {err}"))
            })?;
            let path = path.path();
            let file_name = path.file_name().unwrap().to_str().ok_or_else(|| {
                Diagnostic::spans_error(self.span, format!("Invalid UTF-8 in file name {path:?}"))
            })?;
            if path.is_dir() {
                code_map.extend(self.compile_dir(
                    &path,
                    if parent.is_empty() {
                        file_name.to_string()
                    } else {
                        format!("{parent}.{file_name}")
                    },
                    mode,
                    compiler,
                )?);
            } else if file_name.ends_with(".py") {
                let stem = path.file_stem().unwrap().to_str().unwrap();
                let is_init = stem == "__init__";
                let module_name = if is_init {
                    parent.clone()
                } else if parent.is_empty() {
                    stem.to_owned()
                } else {
                    format!("{parent}.{stem}")
                };

                let compile_path = |src_path: &Path| {
                    let source = fs::read_to_string(src_path).map_err(|err| {
                        Diagnostic::spans_error(
                            self.span,
                            format!("Error reading file {path:?}: {err}"),
                        )
                    })?;
                    self.compile_string(&source, mode, module_name.clone(), compiler, || {
                        path.strip_prefix(&*CARGO_MANIFEST_DIR)
                            .ok()
                            .unwrap_or(&path)
                            .display()
                    })
                };
                let code = compile_path(&path).or_else(|e| {
                    if cfg!(windows) {
                        if let Ok(real_path) = fs::read_to_string(path.canonicalize().unwrap()) {
                            let joined = path.parent().unwrap().join(real_path.trim());
                            if joined.exists() {
                                return compile_path(&joined);
                            } else {
                                return Err(e);
                            }
                        }
                    }
                    Err(e)
                });

                let code = match code {
                    Ok(code) => code,
                    Err(_)
                        if stem.starts_with("badsyntax_")
                            | parent.ends_with(".encoded_modules") =>
                    {
                        // TODO: handle with macro arg rather than hard-coded path
                        continue;
                    }
                    Err(e) => return Err(e),
                };

                code_map.insert(
                    module_name,
                    CompiledModule {
                        code,
                        package: is_init,
                    },
                );
            }
        }
        Ok(code_map)
    }
}

mod kw {
    syn::custom_keyword!(stringify);
    syn::custom_keyword!(mode);
    syn::custom_keyword!(module_name);
    syn::custom_keyword!(source);
    syn::custom_keyword!(file);
    syn::custom_keyword!(dir);
    syn::custom_keyword!(crate_name);
}

fn check_duplicate<T>(x: &Option<T>, span: Span) -> syn::Result<()> {
    if x.is_none() {
        Ok(())
    } else {
        Err(syn::Error::new(span, "duplicate option"))
    }
}

impl Parse for PyCompileArgs {
    fn parse(input: ParseStream) -> ParseResult<Self> {
        let mut module_name = None;
        let mut mode = None;
        let mut source: Option<CompilationSource> = None;
        let mut crate_name = None;

        loop {
            if input.is_empty() {
                break;
            }
            match_tok!(match input {
                tok @ kw::mode => {
                    check_duplicate(&mode, tok.span)?;
                    input.parse::<Token![=]>()?;
                    let s = input.call(parse_litstr)?;
                    let mode_val = s
                        .value()
                        .parse()
                        .map_err(|e| syn::Error::new(s.span(), e))?;
                    mode = Some(mode_val);
                }
                tok @ kw::module_name => {
                    check_duplicate(&module_name, tok.span)?;
                    input.parse::<Token![=]>()?;
                    module_name = Some(input.call(parse_litstr)?.value())
                }
                tok @ kw::source => {
                    check_duplicate(&source, tok.span)?;
                    input.parse::<Token![=]>()?;
                    let code = input.call(parse_litstr)?;
                    source = Some(CompilationSource {
                        kind: CompilationSourceKind::SourceCode(code.value()),
                        span: (tok.span, code.span()),
                    });
                }
                tok @ kw::file => {
                    check_duplicate(&source, tok.span)?;
                    input.parse::<Token![=]>()?;
                    let path = input.call(parse_litstr)?;
                    source = Some(CompilationSource {
                        kind: CompilationSourceKind::File(path.value().into()),
                        span: (tok.span, path.span()),
                    });
                }
                tok @ kw::dir => {
                    check_duplicate(&source, tok.span)?;
                    input.parse::<Token![=]>()?;
                    let path = input.call(parse_litstr)?;
                    source = Some(CompilationSource {
                        kind: CompilationSourceKind::Dir(path.value().into()),
                        span: (tok.span, path.span()),
                    });
                }
                tok @ kw::crate_name => {
                    check_duplicate(&crate_name, tok.span)?;
                    input.parse::<Token![=]>()?;
                    crate_name = Some(input.call(parse_litstr)?.parse()?);
                }
            });

            if input.is_empty() {
                break;
            }
            input.parse::<Token![,]>()?;
        }

        let source = source.ok_or_else(|| {
            syn::Error::new(
                Span::call_site(),
                "Must have either file or source in py_compile!()/py_freeze!()",
            )
        })?;

        Ok(PyCompileArgs {
            source,
            mode: mode.unwrap_or(Mode::Exec),
            module_name: module_name.unwrap_or_else(|| "frozen".to_owned()),
            crate_name: crate_name.unwrap_or_else(|| syn::parse_quote!(::rustpython_vm::bytecode)),
        })
    }
}

fn parse_litstr(input: ParseStream) -> ParseResult<LitStr> {
    if input.peek(LitStr) {
        input.parse()
    } else if input.peek(kw::stringify) {
        input.parse::<kw::stringify>()?;
        input.parse::<Token![!]>()?;
        let stringify_arg = input.step(|cursor| {
            if let Some((proc_macro2::TokenTree::Group(g), next)) = cursor.token_tree() {
                if g.delimiter() != proc_macro2::Delimiter::None {
                    return Ok((g, next));
                }
            }
            Err(cursor.error("expected delimiter"))
        })?;
        Ok(LitStr::new(
            &stringify_arg.stream().to_string(),
            stringify_arg.span(),
        ))
    } else {
        Err(input.error("expected string literal or stringify macro"))
    }
}

struct PyCompileArgs {
    source: CompilationSource,
    mode: Mode,
    module_name: String,
    crate_name: syn::Path,
}

pub fn impl_py_compile(
    input: TokenStream,
    compiler: &dyn Compiler,
) -> Result<TokenStream, Diagnostic> {
    let args: PyCompileArgs = parse2(input)?;

    if matches!(args.source.kind, CompilationSourceKind::Dir(_)) {
        return Err(Diagnostic::spans_error(
            args.source.span,
            "py_compile doesn't accept dir",
        ));
    }

    let crate_name = args.crate_name;
    let code = args
        .source
        .compile_single(args.mode, args.module_name, compiler)?;

    let frozen = frozen_lib::FrozenCodeObject::encode(&code);
    let bytes = LitByteStr::new(&frozen.bytes, Span::call_site());

    let output = quote! {
        #crate_name::frozen_lib::FrozenCodeObject { bytes: &#bytes[..] }
    };

    Ok(output)
}

pub fn impl_py_freeze(
    input: TokenStream,
    compiler: &dyn Compiler,
) -> Result<TokenStream, Diagnostic> {
    let args: PyCompileArgs = parse2(input)?;

    let crate_name = args.crate_name;
    let code_map = args.source.compile(args.mode, args.module_name, compiler)?;

    let data = frozen_lib::FrozenLib::encode(code_map.iter().map(|(k, v)| {
        let v = frozen_lib::FrozenModule {
            code: frozen_lib::FrozenCodeObject::encode(&v.code),
            package: v.package,
        };
        (&**k, v)
    }));
    let bytes = LitByteStr::new(&data.bytes, Span::call_site());

    let output = quote! {
        #crate_name::frozen_lib::FrozenLib::from_ref(#bytes)
    };

    Ok(output)
}
