#![cfg_attr(docsrs, feature(doc_cfg, doc_auto_cfg))]
#![deny(elided_lifetimes_in_paths)]
#![deny(unreachable_pub)]

extern crate proc_macro;

mod ascii_str;
mod config;
mod filter_fn;
mod generator;
mod heritage;
mod html;
mod input;
mod integration;
#[cfg(test)]
mod tests;

#[doc(hidden)]
#[cfg(feature = "proc-macro")]
pub mod __macro_support {
    pub use proc_macro::TokenStream as TokenStream1;
    pub use proc_macro2::TokenStream as TokenStream2;
    pub use quote::quote;
}

use std::borrow::{Borrow, Cow};
use std::collections::hash_map::Entry;
use std::fmt;
use std::hash::{BuildHasher, Hash};
use std::ops::ControlFlow;
use std::path::Path;
use std::sync::Mutex;

use parser::{Parsed, is_rust_keyword, strip_common};
use proc_macro2::{Literal, Span, TokenStream};
use quote::{ToTokens, quote, quote_spanned};
use rustc_hash::FxBuildHasher;
use syn::parse::Parse;
use syn::spanned::Spanned;
use syn::{Ident, parse2};

use crate::config::{Config, read_config_file};
pub use crate::filter_fn::derive_filter_fn;
use crate::generator::{TmplKind, template_to_string};
use crate::heritage::{Context, Heritage};
use crate::input::{AnyTemplateArgs, Print, TemplateArgs, TemplateInput};
use crate::integration::{Buffer, build_template_enum};

/// [`true`] if and only if [`crate`] is compiled with feature `"external-sources"`.
pub const CAN_USE_EXTERNAL_SOURCES: bool = cfg!(feature = "external-sources");

#[macro_export]
#[cfg(feature = "proc-macro")]
macro_rules! make_derive_template {
    (
        $(#[$meta:meta])*
        $vis:vis fn $name:ident() {
            $($import:stmt)+
        }
    ) => {
        /// The `Template` derive macro and its `template()` attribute.
        ///
        /// Askama works by generating one or more trait implementations for any
        /// `struct` type decorated with the `#[derive(Template)]` attribute. The
        /// code generation process takes some options that can be specified through
        /// the `template()` attribute.
        ///
        /// ## Attributes
        ///
        /// The following sub-attributes are currently recognized:
        ///
        /// ### path
        ///
        /// E.g. `path = "foo.html"`
        ///
        /// Sets the path to the template file.
        /// The path is interpreted as relative to the configured template directories
        /// (by default, this is a `templates` directory next to your `Cargo.toml`).
        /// The file name extension is used to infer an escape mode (see below). In
        /// web framework integrations, the path's extension may also be used to
        /// infer the content type of the resulting response.
        /// Cannot be used together with `source`.
        ///
        /// ### source
        ///
        /// E.g. `source = "{{ foo }}"`
        ///
        /// Directly sets the template source.
        /// This can be useful for test cases or short templates. The generated path
        /// is undefined, which generally makes it impossible to refer to this
        /// template from other templates. If `source` is specified, `ext` must also
        /// be specified (see below). Cannot be used together with `path`.
        /// `ext` (e.g. `ext = "txt"`): lets you specify the content type as a file
        /// extension. This is used to infer an escape mode (see below), and some
        /// web framework integrations use it to determine the content type.
        /// Cannot be used together with `path`.
        ///
        /// ### `in_doc`
        ///
        /// E.g. `in_doc = true`
        ///
        /// As an alternative to supplying the code template code in an external file (as `path` argument),
        /// or as a string (as `source` argument), you can also enable the `"code-in-doc"` feature.
        /// With this feature, you can specify the template code directly in the documentation
        /// of the template `struct`.
        ///
        /// Instead of `path = "…"` or `source = "…"`, specify `in_doc = true` in the `#[template]`
        /// attribute, and in the struct's documentation add a `askama` code block:
        ///
        /// ```rust,ignore
        /// /// ```askama
        /// /// <div>{{ lines|linebreaksbr }}</div>
        /// /// ```
        /// #[derive(Template)]
        /// #[template(ext = "html", in_doc = true)]
        /// struct Example<'a> {
        ///     lines: &'a str,
        /// }
        /// ```
        ///
        /// ### print
        ///
        /// E.g. `print = "code"`
        ///
        /// Enable debugging by printing nothing (`none`), the parsed syntax tree (`ast`),
        /// the generated code (`code`) or `all` for both.
        /// The requested data will be printed to stdout at compile time.
        ///
        /// ### block
        ///
        /// E.g. `block = "block_name"`
        ///
        /// Renders the block by itself.
        /// Expressions outside of the block are not required by the struct, and
        /// inheritance is also supported. This can be useful when you need to
        /// decompose your template for partial rendering, without needing to
        /// extract the partial into a separate template or macro.
        ///
        /// ```rust,ignore
        /// #[derive(Template)]
        /// #[template(path = "hello.html", block = "hello")]
        /// struct HelloTemplate<'a> { ... }
        /// ```
        ///
        /// ### blocks
        ///
        /// E.g. `blocks = ["title", "content"]`
        ///
        /// Automatically generates (a number of) sub-templates that act as if they had a
        /// `block = "..."` attribute. You can access the sub-templates with the method
        /// <code>my_template.as_<em>block_name</em>()</code>, where *`block_name`* is the
        /// name of the block:
        ///
        /// ```rust,ignore
        /// # use askama::Template;
        /// #[derive(Template)]
        /// #[template(
        ///     ext = "txt",
        ///     source = "
        ///         {% block title -%} <h1>{{title}}</h1> {%- endblock %}
        ///         {% block content -%} <p>{{message</p> {%- endblock %}
        ///     ",
        ///     blocks = ["title", "content"]
        /// )]
        /// struct News<'a> {
        ///     title: &'a str,
        ///     message: &'a str,
        /// }
        ///
        /// let news = News {
        ///     title: "Announcing Rust 1.84.1",
        ///     message: "The Rust team has published a new point release of Rust, 1.84.1.",
        /// };
        /// assert_eq!(
        ///     news.as_title().render().unwrap(),
        ///     "<h1>Announcing Rust 1.84.1</h1>"
        /// );
        /// ```
        ///
        /// ### escape
        ///
        /// E.g. `escape = "none"`
        ///
        /// Override the template's extension used for the purpose of determining the escaper for
        /// this template. See the section on configuring custom escapers for more information.
        ///
        /// ### syntax
        ///
        /// E.g. `syntax = "foo"`
        ///
        /// Set the syntax name for a parser defined in the configuration file.
        /// The default syntax, `"default"`,  is the one provided by Askama.
        ///
        /// ### askama
        ///
        /// E.g. `askama = askama`
        ///
        /// If you are using askama in a subproject, a library or a [macro][book-macro], it might be
        /// necessary to specify the [path][book-tree] where to find the module `askama`:
        ///
        /// [book-macro]: https://doc.rust-lang.org/book/ch19-06-macros.html
        /// [book-tree]: https://doc.rust-lang.org/book/ch07-03-paths-for-referring-to-an-item-in-the-module-tree.html
        ///
        /// ```rust,ignore
        /// #[doc(hidden)]
        /// pub use askama as __askama;
        ///
        /// #[macro_export]
        /// macro_rules! new_greeter {
        ///     ($name:ident) => {
        ///         #[derive(Debug, $crate::__askama::Template)]
        ///         #[template(
        ///             ext = "txt",
        ///             source = "Hello, world!",
        ///             askama = $crate::__askama
        ///         )]
        ///         struct $name;
        ///     }
        /// }
        ///
        /// new_greeter!(HelloWorld);
        /// assert_eq!(HelloWorld.to_string(), "Hello, world!");
        /// ```
        $(#[$meta])*
        $vis fn $name(
            input: $crate::__macro_support::TokenStream1,
        ) -> $crate::__macro_support::TokenStream1 {
            fn import_askama() -> $crate::__macro_support::TokenStream2 {
                $crate::__macro_support::quote!($($import)*)
            }

            $crate::derive_template(input.into(), import_askama).into()
        }
    };
}

#[macro_export]
#[cfg(feature = "proc-macro")]
macro_rules! make_filter_fn {
    (
        $(#[$meta:meta])*
        $vis:vis fn $name:ident() {
            $($import:stmt)+
        }
    ) => {
        $(#[$meta])*
        $vis fn $name(
            attr: $crate::__macro_support::TokenStream1,
            item: $crate::__macro_support::TokenStream1,
        ) -> $crate::__macro_support::TokenStream1 {
            fn import_askama() -> $crate::__macro_support::TokenStream2 {
                $crate::__macro_support::quote!($($import)*)
            }

            $crate::derive_filter_fn(attr.into(), item.into(), import_askama).into()
        }
    }
}

pub fn derive_template(input: TokenStream, import_askama: fn() -> TokenStream) -> TokenStream {
    let ast = match parse_ts_or_compile_error(input, import_askama) {
        ControlFlow::Continue(ast) => ast,
        ControlFlow::Break(err) => return err,
    };

    let mut buf = Buffer::new();
    let mut args = AnyTemplateArgs::new(&ast);
    let crate_name = args
        .as_mut()
        .map(|a| a.take_crate_name())
        .unwrap_or_default();

    let ts = match args.and_then(|args| build_template(&mut buf, &ast, args)) {
        Ok(_) => buf.into_token_stream(),
        Err(CompileError { msg, span }) => {
            let mut ts = quote::quote_spanned! {
                span.unwrap_or(ast.ident.span()) =>
                askama::helpers::core::compile_error!(#msg);
            };
            buf.clear();
            if build_skeleton(&mut buf, &ast).is_ok() {
                let source: TokenStream = buf.into_token_stream();
                ts.extend(source);
            }
            ts
        }
    };
    let import_askama = match crate_name {
        Some(crate_name) => quote!(use #crate_name as askama;),
        None => import_askama(),
    };
    quote_spanned! {
        ast.ident.span() =>
        #[allow(
            // We use `Struct { 0: arg0, 1: arg1 }` in enum specialization.
            clippy::init_numbered_fields, non_shorthand_field_patterns,
            // The generated code is not indented at all.
            clippy::suspicious_else_formatting,
            // We don't care if the user does not use `Template`, `FastWritable`, etc.
            dead_code,
            // We intentionally add extraneous underscores in type and variable names.
            non_camel_case_types, non_snake_case,
        )]
        const _: () = {
            #import_askama
            #ts
        };
    }
}

fn parse_ts_or_compile_error<T: Parse>(
    input: TokenStream,
    import_askama: fn() -> TokenStream,
) -> ControlFlow<TokenStream, T> {
    match parse2(input) {
        Ok(ast) => ControlFlow::Continue(ast),
        Err(err) => {
            let import_askama = import_askama();
            let msgs = err.into_iter().map(|err| err.to_string());
            ControlFlow::Break(quote! {
                const _: () = {
                    #import_askama
                    #(core::compile_error!(#msgs);)*
                };
            })
        }
    }
}

fn build_skeleton(buf: &mut Buffer, ast: &syn::DeriveInput) -> Result<usize, CompileError> {
    let template_args = TemplateArgs::fallback();
    let config = Config::new("", None, None, None, None)?;
    let input = TemplateInput::new(ast, None, config, &template_args)?;
    let mut contexts = HashMap::default();
    let parsed = parser::Parsed::default();
    contexts.insert(&input.path, Context::empty(&parsed, ast.span()));
    template_to_string(buf, &input, &contexts, None, TmplKind::Struct)
}

/// Takes a `syn::DeriveInput` and generates source code for it
///
/// Reads the metadata from the `template()` attribute to get the template
/// metadata, then fetches the source from the filesystem. The source is
/// parsed, and the parse tree is fed to the code generator. Will print
/// the parse tree and/or generated source according to the `print` key's
/// value as passed to the `template()` attribute.
pub(crate) fn build_template(
    buf: &mut Buffer,
    ast: &syn::DeriveInput,
    args: AnyTemplateArgs,
) -> Result<usize, CompileError> {
    let err_span;
    let mut result = match args {
        AnyTemplateArgs::Struct(item) => {
            err_span = item
                .source
                .1
                .as_ref()
                .and_then(|l| l.span())
                .or(item.template_span);
            build_template_item(buf, ast, None, &item, TmplKind::Struct)
        }
        AnyTemplateArgs::Enum {
            enum_args,
            vars_args,
            has_default_impl,
        } => {
            err_span = enum_args
                .as_ref()
                .and_then(|v| v.source.as_ref())
                .map(|s| s.span())
                .or_else(|| enum_args.as_ref().map(|v| v.template.span()));
            build_template_enum(buf, ast, enum_args, vars_args, has_default_impl)
        }
    };
    if let Err(err) = &mut result
        && err.span.is_none()
    {
        err.span = err_span;
    }
    result
}

fn build_template_item(
    buf: &mut Buffer,
    ast: &syn::DeriveInput,
    enum_ast: Option<&syn::DeriveInput>,
    template_args: &TemplateArgs,
    tmpl_kind: TmplKind<'_>,
) -> Result<usize, CompileError> {
    let config_path = template_args.config_path();
    let (s, full_config_path) = read_config_file(config_path, template_args.config_span)?;
    let config = Config::new(
        &s,
        config_path,
        template_args.whitespace,
        template_args.config_span,
        full_config_path,
    )?;
    let input = TemplateInput::new(ast, enum_ast, config, template_args)?;

    let mut templates = HashMap::default();
    input.find_used_templates(&mut templates)?;

    let mut contexts = HashMap::default();
    for (path, parsed) in &templates {
        contexts.insert(
            path,
            Context::new(
                input.config,
                path,
                parsed,
                input.source_span.clone(),
                ast.span(),
            )?,
        );
    }

    let ctx = &contexts[&input.path];
    let heritage = if !ctx.blocks.is_empty() || ctx.extends.is_some() {
        Some(Heritage::new(ctx, &contexts))
    } else {
        None
    };

    if let Some((block_name, block_span)) = input.block {
        let has_block = match &heritage {
            Some(heritage) => heritage.blocks.contains_key(block_name),
            None => ctx.blocks.contains_key(block_name),
        };
        if !has_block {
            return Err(CompileError::no_file_info(
                format_args!("cannot find block `{block_name}`"),
                Some(block_span),
            ));
        }
    }

    if input.print == Print::Ast || input.print == Print::All {
        eprintln!("{:?}", templates[&input.path].nodes());
    }

    let size_hint = template_to_string(buf, &input, &contexts, heritage.as_ref(), tmpl_kind)?;
    Ok(size_hint)
}

#[derive(Debug, Clone)]
struct CompileError {
    msg: String,
    span: Option<Span>,
}

impl CompileError {
    fn new<S: fmt::Display>(msg: S, file_info: Option<FileInfo<'_>>) -> Self {
        Self::new_with_span_stable(msg, file_info, None)
    }

    fn new_with_span<S: fmt::Display>(
        msg: S,
        file_info: Option<FileInfo<'_>>,
        span: Option<Span>,
    ) -> Self {
        // `Span::join` always return `None` if not on nightly. We use it to prevent not showing a
        // nice error message when not on nightly.
        let span = if let Some(span) = span
            && span.join(proc_macro2::Span::call_site()).is_none()
        {
            None
        } else {
            span
        };
        Self::new_with_span_stable(msg, file_info, span)
    }

    fn new_with_span_stable<S: fmt::Display>(
        msg: S,
        file_info: Option<FileInfo<'_>>,
        span: Option<Span>,
    ) -> Self {
        let msg = match (span, file_info) {
            (None, Some(file_info)) => format!("{msg}{file_info}"),
            _ => msg.to_string(),
        };
        Self { msg, span }
    }

    fn no_file_info<S: ToString>(msg: S, span: Option<Span>) -> Self {
        Self {
            msg: msg.to_string(),
            span,
        }
    }
}

impl std::error::Error for CompileError {}

impl fmt::Display for CompileError {
    #[inline]
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.write_str(&self.msg)
    }
}

#[derive(Debug, Clone, Copy)]
struct FileInfo<'a> {
    path: &'a Path,
    source: Option<&'a str>,
    node_source: Option<&'a str>,
}

impl<'a> FileInfo<'a> {
    fn new(path: &'a Path, source: Option<&'a str>, node_source: Option<&'a str>) -> Self {
        Self {
            path,
            source,
            node_source,
        }
    }

    fn of(node: parser::Span<'a>, path: &'a Path, parsed: &'a Parsed) -> Self {
        let source = parsed.source();
        Self {
            path,
            source: Some(source),
            node_source: node.as_suffix_of(source),
        }
    }
}

impl fmt::Display for FileInfo<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let (Some(source), Some(node_source)) = (self.source, self.node_source) {
            let (error_info, file_path) = generate_error_info(source, node_source, self.path);
            write!(
                f,
                "\n  --> {file_path}:{row}:{column}\n{source_after}",
                row = error_info.row,
                column = error_info.column,
                source_after = error_info.source_after,
            )
        } else {
            write!(
                f,
                "\n --> {}",
                match std::env::current_dir() {
                    Ok(cwd) => fmt_left!(move "{}", strip_common(&cwd, self.path)),
                    Err(_) => fmt_right!("{}", self.path.display()),
                }
            )
        }
    }
}

struct ErrorInfo {
    row: usize,
    column: usize,
    source_after: String,
}

fn generate_row_and_column(src: &str, input: &str) -> ErrorInfo {
    const MAX_LINE_LEN: usize = 80;

    let offset = src.len() - input.len();
    let (source_before, source_after) = src.split_at(offset);

    let source_after = match source_after
        .char_indices()
        .enumerate()
        .take(MAX_LINE_LEN + 1)
        .last()
    {
        Some((MAX_LINE_LEN, (i, _))) => format!("{:?}...", &source_after[..i]),
        _ => format!("{source_after:?}"),
    };

    let (row, last_line) = source_before.lines().enumerate().last().unwrap_or_default();
    let column = last_line.chars().count();
    ErrorInfo {
        row: row + 1,
        column,
        source_after,
    }
}

/// Return the error related information and its display file path.
fn generate_error_info(src: &str, input: &str, file_path: &Path) -> (ErrorInfo, String) {
    let file_path = match std::env::current_dir() {
        Ok(cwd) => strip_common(&cwd, file_path),
        Err(_) => file_path.display().to_string(),
    };
    let error_info = generate_row_and_column(src, input);
    (error_info, file_path)
}

struct MsgValidEscapers<'a>(&'a [(Vec<Cow<'a, str>>, Cow<'a, str>)]);

impl fmt::Display for MsgValidEscapers<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut exts = self
            .0
            .iter()
            .flat_map(|(exts, _)| exts)
            .map(|x| format!("{x:?}"))
            .collect::<Vec<_>>();
        exts.sort();
        write!(f, "The available extensions are: {}", exts.join(", "))
    }
}

fn field_new(name: &str, span: proc_macro2::Span) -> TokenStream {
    if name.starts_with(|c: char| c.is_ascii_digit()) {
        let mut literal: Literal = name.parse().unwrap();
        literal.set_span(span);
        literal.into_token_stream()
    } else if is_rust_keyword(name) && !matches!(name, "self" | "Self" | "crate" | "super") {
        Ident::new_raw(name, span).into_token_stream()
    } else {
        Ident::new(name, span).into_token_stream()
    }
}

fn var_writer() -> Ident {
    syn::Ident::new("__askama_writer", proc_macro2::Span::call_site())
}

fn var_filter_source() -> Ident {
    syn::Ident::new("__askama_filter_block", proc_macro2::Span::call_site())
}

fn var_values() -> Ident {
    syn::Ident::new("__askama_values", proc_macro2::Span::call_site())
}

fn var_arg() -> Ident {
    syn::Ident::new("__askama_arg", proc_macro2::Span::call_site())
}

fn var_item() -> Ident {
    syn::Ident::new("__askama_item", proc_macro2::Span::call_site())
}

fn var_len() -> Ident {
    syn::Ident::new("__askama_len", proc_macro2::Span::call_site())
}

fn var_iter() -> Ident {
    syn::Ident::new("__askama_iter", proc_macro2::Span::call_site())
}

fn var_cycle() -> Ident {
    syn::Ident::new("__askama_cycle", proc_macro2::Span::call_site())
}

fn var_did_loop() -> Ident {
    syn::Ident::new("__askama_did_loop", proc_macro2::Span::call_site())
}

fn var_expr_n(n: usize, span: proc_macro2::Span) -> Ident {
    syn::Ident::new(&format!("__askama_expr{n}"), span)
}

#[derive(Debug)]
struct OnceMap<K, V>([Mutex<HashMap<K, V>>; 8]);

impl<K, V> Default for OnceMap<K, V> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<K: Hash + Eq, V> OnceMap<K, V> {
    // The API of this function was copied, and adapted from the `once_map` crate
    // <https://crates.io/crates/once_map/0.4.18>.
    fn get_or_try_insert<T, Q, E>(
        &self,
        key: &Q,
        make_key_value: impl FnOnce(&Q) -> Result<(K, V), E>,
        to_value: impl FnOnce(&V) -> T,
    ) -> Result<T, E>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let shard_idx = (FxBuildHasher.hash_one(key) % self.0.len() as u64) as usize;
        let mut shard = self.0[shard_idx].lock().unwrap();
        Ok(to_value(if let Some(v) = shard.get(key) {
            v
        } else {
            let (k, v) = make_key_value(key)?;
            match shard.entry(k) {
                Entry::Vacant(entry) => entry.insert(v),
                Entry::Occupied(_) => unreachable!("key in map when it should not have been"),
            }
        }))
    }
}

enum EitherFormat<L, R>
where
    L: for<'a, 'b> Fn(&'a mut fmt::Formatter<'b>) -> fmt::Result,
    R: for<'a, 'b> Fn(&'a mut fmt::Formatter<'b>) -> fmt::Result,
{
    Left(L),
    Right(R),
}

impl<L, R> fmt::Display for EitherFormat<L, R>
where
    L: for<'a, 'b> Fn(&'a mut fmt::Formatter<'b>) -> fmt::Result,
    R: for<'a, 'b> Fn(&'a mut fmt::Formatter<'b>) -> fmt::Result,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Left(v) => v(f),
            Self::Right(v) => v(f),
        }
    }
}

macro_rules! fmt_left {
    (move $fmt:literal $($tt:tt)*) => {
        $crate::EitherFormat::Left(move |f: &mut std::fmt::Formatter<'_>| {
            write!(f, $fmt $($tt)*)
        })
    };
    ($fmt:literal $($tt:tt)*) => {
        $crate::EitherFormat::Left(|f: &mut std::fmt::Formatter<'_>| {
            write!(f, $fmt $($tt)*)
        })
    };
}

macro_rules! fmt_right {
    (move $fmt:literal $($tt:tt)*) => {
        $crate::EitherFormat::Right(move |f: &mut std::fmt::Formatter<'_>| {
            write!(f, $fmt $($tt)*)
        })
    };
    ($fmt:literal $($tt:tt)*) => {
        $crate::EitherFormat::Right(|f: &mut std::fmt::Formatter<'_>| {
            write!(f, $fmt $($tt)*)
        })
    };
}

macro_rules! quote_into {
    ($buffer:expr, $span:expr, { $($x:tt)+ } $(,)?) => {{
        let buffer: &mut $crate::integration::Buffer = $buffer;
        if !buffer.is_discard() {
            let span: ::proc_macro2::Span = $span;
            buffer.write_tokens(::quote::quote_spanned!(span => $($x)+));
        }
    }};
}

pub(crate) use {fmt_left, fmt_right, quote_into};

type HashMap<K, V> = std::collections::hash_map::HashMap<K, V, FxBuildHasher>;
type HashSet<T> = std::collections::hash_set::HashSet<T, FxBuildHasher>;
