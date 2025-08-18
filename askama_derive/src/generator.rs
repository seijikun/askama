mod expr;
mod filter;
mod helpers;
mod node;

use std::borrow::Cow;
use std::env::current_dir;
use std::ops::Deref;
use std::path::{Path, PathBuf};
use std::str;
use std::sync::Arc;

use parser::node::{Call, Macro, Whitespace};
use parser::{CharLit, Expr, FloatKind, IntKind, Num, StrLit, WithSpan};
use proc_macro2::TokenStream;
use quote::{ToTokens, quote_spanned};
use syn::Token;

use crate::generator::helpers::{clean_path, diff_paths};
use crate::heritage::{Context, Heritage};
use crate::html::write_escaped_str;
use crate::input::{Source, TemplateInput};
use crate::integration::{Buffer, impl_everything, write_header};
use crate::{CompileError, FileInfo, HashMap, field_new, quote_into};

pub(crate) fn template_to_string(
    buf: &mut Buffer,
    input: &TemplateInput<'_>,
    contexts: &HashMap<&Arc<Path>, Context<'_>>,
    heritage: Option<&Heritage<'_, '_>>,
    tmpl_kind: TmplKind<'_>,
) -> Result<usize, CompileError> {
    let generator = Generator::new(
        input,
        contexts,
        heritage,
        MapChain::default(),
        input.block.is_some(),
        0,
    );
    let size_hint = match generator.impl_template(buf, tmpl_kind) {
        Err(mut err) if err.span.is_none() => {
            err.span = input.source_span.as_ref().and_then(|l| l.span());
            Err(err)
        }
        result => result,
    }?;

    if tmpl_kind == TmplKind::Struct {
        impl_everything(input.ast, buf);
    }
    Ok(size_hint)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TmplKind<'a> {
    /// [`askama::Template`]
    Struct,
    /// [`askama::helpers::EnumVariantTemplate`]
    Variant,
    /// Used in `blocks` implementation
    Block(&'a str),
}

struct Generator<'a, 'h> {
    /// The template input state: original struct AST and attributes
    input: &'a TemplateInput<'a>,
    /// All contexts, keyed by the package-relative template path
    contexts: &'a HashMap<&'a Arc<Path>, Context<'a>>,
    /// The heritage contains references to blocks and their ancestry
    heritage: Option<&'h Heritage<'a, 'h>>,
    /// Variables accessible directly from the current scope (not redirected to context)
    locals: MapChain<'a>,
    /// Suffix whitespace from the previous literal. Will be flushed to the
    /// output buffer unless suppressed by whitespace suppression on the next
    /// non-literal.
    next_ws: Option<&'a str>,
    /// Whitespace suppression from the previous non-literal. Will be used to
    /// determine whether to flush prefix whitespace from the next literal.
    skip_ws: Whitespace,
    /// If currently in a block, this will contain the name of a potential parent block
    super_block: Option<(&'a str, usize)>,
    /// Buffer for writable
    buf_writable: WritableBuffer<'a>,
    /// Used in blocks to check if we are inside a filter block.
    is_in_filter_block: usize,
    /// Set of called macros we are currently in. Used to prevent (indirect) recursions.
    seen_callers: Vec<(&'a Macro<'a>, Option<FileInfo<'a>>)>,
    /// The directory path of the calling file.
    caller_dir: CallerDir,
}

enum CallerDir {
    Valid(PathBuf),
    Invalid,
    Unresolved,
}

impl<'a, 'h> Generator<'a, 'h> {
    fn new(
        input: &'a TemplateInput<'a>,
        contexts: &'a HashMap<&'a Arc<Path>, Context<'a>>,
        heritage: Option<&'h Heritage<'a, 'h>>,
        locals: MapChain<'a>,
        buf_writable_discard: bool,
        is_in_filter_block: usize,
    ) -> Self {
        Self {
            input,
            contexts,
            heritage,
            locals,
            next_ws: None,
            skip_ws: Whitespace::Preserve,
            super_block: None,
            buf_writable: WritableBuffer {
                discard: buf_writable_discard,
                ..Default::default()
            },
            is_in_filter_block,
            seen_callers: Vec::new(),
            caller_dir: CallerDir::Unresolved,
        }
    }

    fn rel_path<'p>(&mut self, path: &'p Path) -> Cow<'p, Path> {
        self.caller_dir()
            .and_then(|caller_dir| diff_paths(path, caller_dir))
            .map_or(Cow::Borrowed(path), Cow::Owned)
    }

    fn caller_dir(&mut self) -> Option<&Path> {
        match self.caller_dir {
            CallerDir::Valid(ref caller_dir) => return Some(caller_dir.as_path()),
            CallerDir::Invalid => return None,
            CallerDir::Unresolved => {}
        }

        if proc_macro::is_available()
            && let Some(mut local_file) = proc_macro::Span::call_site().local_file()
        {
            local_file.pop();
            if !local_file.is_absolute() {
                local_file = current_dir()
                    .as_deref()
                    .unwrap_or(Path::new("."))
                    .join(local_file);
            }

            self.caller_dir = CallerDir::Valid(clean_path(&local_file));
            match &self.caller_dir {
                CallerDir::Valid(caller_dir) => Some(caller_dir.as_path()),
                _ => None, // unreachable
            }
        } else {
            self.caller_dir = CallerDir::Invalid;
            None
        }
    }

    // Implement `Template` for the given context struct.
    fn impl_template(
        mut self,
        buf: &mut Buffer,
        tmpl_kind: TmplKind<'a>,
    ) -> Result<usize, CompileError> {
        let ctx = &self.contexts[&self.input.path];

        let span = self.input.ast.ident.span();
        let target = match tmpl_kind {
            TmplKind::Struct => quote_spanned!(span=> askama::Template),
            TmplKind::Variant => quote_spanned!(span=> askama::helpers::EnumVariantTemplate),
            TmplKind::Block(trait_name) => field_new(trait_name, span),
        };

        let mut full_paths = TokenStream::new();
        if let Some(full_config_path) = &self.input.config.full_config_path {
            let full_config_path = self.rel_path(full_config_path).display().to_string();
            full_paths = quote_spanned!(span=>
                const _: &[askama::helpers::core::primitive::u8] =
                 askama::helpers::core::include_bytes!(#full_config_path);
            );
        }

        // Make sure the compiler understands that the generated code depends on the template files.
        let mut paths = self
            .contexts
            .keys()
            .map(|path| -> &Path { path })
            .collect::<Vec<_>>();
        paths.sort();
        let paths = paths
            .into_iter()
            .filter(|path| {
                // Skip the fake path of templates defined in rust source.
                match self.input.source {
                    #[cfg(feature = "external-sources")]
                    Source::Path(_) => true,
                    Source::Source(_) => **path != *self.input.path,
                }
            })
            .fold(TokenStream::new(), |mut acc, path| {
                let path = self.rel_path(path).display().to_string();
                acc.extend(quote_spanned!(span=>
                    const _: &[askama::helpers::core::primitive::u8] =
                        askama::helpers::core::include_bytes!(#path);
                ));
                acc
            });

        let mut content = Buffer::new();
        let size_hint = self.impl_template_inner(ctx, &mut content)?;
        let content = content.into_token_stream();

        let mut size_hint_s = TokenStream::new();
        if tmpl_kind == TmplKind::Struct {
            size_hint_s = quote_spanned!(span=>
                const SIZE_HINT: askama::helpers::core::primitive::usize = #size_hint;
            );
        }

        write_header(self.input.ast, buf, target, span);
        let var_writer = crate::var_writer();
        let var_values = crate::var_values();
        quote_into!(buf, span, { {
            fn render_into_with_values<AskamaW>(
                &self,
                #var_writer: &mut AskamaW,
                #var_values: &dyn askama::Values,
            ) -> askama::Result<()>
            where
                AskamaW: askama::helpers::core::fmt::Write + ?askama::helpers::core::marker::Sized,
            {
                #[allow(unused_imports)]
                use askama::{
                    filters::{AutoEscape as _, WriteWritable as _},
                    helpers::{ResultConverter as _, core::fmt::Write as _},
                };

                #full_paths
                #paths
                #content
                askama::Result::Ok(())
            }
            #size_hint_s
        } });

        for block in self.input.blocks {
            self.impl_block(buf, block)?;
        }

        Ok(size_hint)
    }

    fn impl_block(
        &self,
        buf: &mut Buffer,
        block: &crate::input::Block,
    ) -> Result<(), CompileError> {
        // RATIONALE: `*self` must be the input type, implementation details should not leak:
        // - impl Self { fn as_block(self) } ->
        // - struct __Askama__Self__as__block__Wrapper { this: self } ->
        // - impl Template for __Askama__Self__as__block__Wrapper { fn render_into_with_values() } ->
        // - impl __Askama__Self__as__block for Self { render_into_with_values() }

        use syn::{GenericParam, Ident, Lifetime, LifetimeParam, Token};

        let span = block.span;
        let ident = &self.input.ast.ident;

        let doc = format!(
            "A sub-template that renders only the block `{}` of [`{ident}`].",
            block.name
        );
        let method_name = format!("as_{}", block.name);
        let trait_name = format!("__Askama__{ident}__as__{}", block.name);
        let wrapper_name = format!("__Askama__{ident}__as__{}__Wrapper", block.name);
        let self_lt_name = format!("'__Askama__{ident}__as__{}__self", block.name);

        let method_id = Ident::new(&method_name, span);
        let trait_id = Ident::new(&trait_name, span);
        let wrapper_id = Ident::new(&wrapper_name, span);
        let self_lt = Lifetime::new(&self_lt_name, span);

        // generics of the input with an additional lifetime to capture `self`
        let mut wrapper_generics = self.input.ast.generics.clone();
        if wrapper_generics.lt_token.is_none() {
            wrapper_generics.lt_token = Some(Token![<](span));
            wrapper_generics.gt_token = Some(Token![>](span));
        }
        wrapper_generics.params.insert(
            0,
            GenericParam::Lifetime(LifetimeParam::new(self_lt.clone())),
        );

        let (impl_generics, ty_generics, where_clause) = self.input.ast.generics.split_for_impl();
        let (wrapper_impl_generics, wrapper_ty_generics, wrapper_where_clause) =
            wrapper_generics.split_for_impl();

        let input = TemplateInput {
            block: Some((&block.name, span)),
            blocks: &[],
            ..self.input.clone()
        };
        let mut template_buf = Buffer::new();
        let size_hint = template_to_string(
            &mut template_buf,
            &input,
            self.contexts,
            self.heritage,
            TmplKind::Block(&trait_name),
        )?;

        let template_buf = template_buf.into_token_stream();
        quote_into!(buf, span, {
            #[allow(missing_docs, non_camel_case_types, non_snake_case, unreachable_pub)]
            const _: () = {
                #template_buf

                pub trait #trait_id {
                    fn render_into_with_values<AskamaW>(
                        &self,
                        writer: &mut AskamaW,
                        values: &dyn askama::Values,
                    ) -> askama::Result<()>
                    where
                        AskamaW:
                            askama::helpers::core::fmt::Write + ?askama::helpers::core::marker::Sized;
                }

                impl #impl_generics #ident #ty_generics #where_clause {
                    #[inline]
                    #[doc = #doc]
                    pub fn #method_id(&self) -> impl askama::Template + '_ {
                        #wrapper_id {
                            this: self,
                        }
                    }
                }

                #[askama::helpers::core::prelude::rust_2021::derive(
                    askama::helpers::core::prelude::rust_2021::Clone,
                    askama::helpers::core::prelude::rust_2021::Copy
                )]
                pub struct #wrapper_id #wrapper_generics #wrapper_where_clause {
                    this: &#self_lt #ident #ty_generics,
                }

                impl #wrapper_impl_generics askama::Template
                for #wrapper_id #wrapper_ty_generics #wrapper_where_clause {
                    #[inline]
                    fn render_into_with_values<AskamaW>(
                        &self,
                        writer: &mut AskamaW,
                        values: &dyn askama::Values
                    ) -> askama::Result<()>
                    where
                        AskamaW: askama::helpers::core::fmt::Write + ?askama::helpers::core::marker::Sized
                    {
                        <_ as #trait_id>::render_into_with_values(self.this, writer, values)
                    }

                    const SIZE_HINT: askama::helpers::core::primitive::usize = #size_hint;
                }

                // cannot use `crate::integrations::impl_fast_writable()` w/o cloning the struct
                impl #wrapper_impl_generics askama::FastWritable
                for #wrapper_id #wrapper_ty_generics #wrapper_where_clause {
                    #[inline]
                    fn write_into<AskamaW>(
                        &self,
                        dest: &mut AskamaW,
                        values: &dyn askama::Values,
                    ) -> askama::Result<()>
                    where
                        AskamaW: askama::helpers::core::fmt::Write + ?askama::helpers::core::marker::Sized
                    {
                        <_ as askama::Template>::render_into_with_values(self, dest, values)
                    }
                }

                // cannot use `crate::integrations::impl_display()` w/o cloning the struct
                impl #wrapper_impl_generics askama::helpers::core::fmt::Display
                for #wrapper_id #wrapper_ty_generics #wrapper_where_clause {
                    #[inline]
                    fn fmt(
                        &self,
                        f: &mut askama::helpers::core::fmt::Formatter<'_>
                    ) -> askama::helpers::core::fmt::Result {
                        <_ as askama::Template>::render_into(self, f)
                            .map_err(|_| askama::helpers::core::fmt::Error)
                    }
                }
            };
        });

        Ok(())
    }

    fn is_var_defined(&self, var_name: &str) -> bool {
        self.locals.get_any(var_name).is_some() || self.input.fields.iter().any(|f| f == var_name)
    }

    /// Like [`is_var_defined()`], but not true for a forward declaration `{% let var %}`.
    fn is_var_assigned(&self, var_name: &str) -> bool {
        if let Some(meta) = self.locals.get(var_name) {
            meta.initialized
        } else {
            self.input.fields.iter().any(|f| f == var_name)
        }
    }
}

#[cfg(target_pointer_width = "16")]
type TargetIsize = i16;
#[cfg(target_pointer_width = "32")]
type TargetIsize = i32;
#[cfg(target_pointer_width = "64")]
type TargetIsize = i64;

#[cfg(target_pointer_width = "16")]
type TargetUsize = u16;
#[cfg(target_pointer_width = "32")]
type TargetUsize = u32;
#[cfg(target_pointer_width = "64")]
type TargetUsize = u64;

#[cfg(not(any(
    target_pointer_width = "16",
    target_pointer_width = "32",
    target_pointer_width = "64"
)))]
const _: () = {
    panic!("unknown cfg!(target_pointer_width)");
};

/// In here, we inspect in the expression if it is a literal, and if it is, whether it
/// can be escaped at compile time.
fn compile_time_escape<'a>(
    expr: &WithSpan<'a, Box<Expr<'a>>>,
    escaper: &str,
) -> Option<Writable<'a>> {
    // we only optimize for known escapers
    enum OutputKind {
        Html,
        Text,
    }

    // we only optimize for known escapers
    let output = match escaper.strip_prefix("askama::filters::")? {
        "Html" => OutputKind::Html,
        "Text" => OutputKind::Text,
        _ => return None,
    };

    // for now, we only escape strings, chars, numbers, and bools at compile time
    let value = match ***expr {
        Expr::StrLit(StrLit {
            prefix: None,
            content,
            ..
        }) => {
            if content.find('\\').is_none() {
                // if the literal does not contain any backslashes, then it does not need unescaping
                Cow::Borrowed(content)
            } else {
                // the input could be string escaped if it contains any backslashes
                let input = format!(r#""{content}""#);
                let input = input.parse().ok()?;
                let input = syn::parse2::<syn::LitStr>(input).ok()?;
                Cow::Owned(input.value())
            }
        }
        Expr::CharLit(CharLit {
            prefix: None,
            content,
        }) => {
            if content.find('\\').is_none() {
                // if the literal does not contain any backslashes, then it does not need unescaping
                Cow::Borrowed(content)
            } else {
                // the input could be string escaped if it contains any backslashes
                let input = format!(r#"'{content}'"#);
                let input = input.parse().ok()?;
                let input = syn::parse2::<syn::LitChar>(input).ok()?;
                Cow::Owned(input.value().to_string())
            }
        }
        Expr::NumLit(_, value) => {
            enum NumKind {
                Int(Option<IntKind>),
                Float(Option<FloatKind>),
            }

            let (orig_value, kind) = match value {
                Num::Int(value, kind) => (value, NumKind::Int(kind)),
                Num::Float(value, kind) => (value, NumKind::Float(kind)),
            };
            let value = match orig_value.chars().any(|c| c == '_') {
                true => Cow::Owned(orig_value.chars().filter(|&c| c != '_').collect()),
                false => Cow::Borrowed(orig_value),
            };

            fn int<T: ToString, E>(
                from_str_radix: impl Fn(&str, u32) -> Result<T, E>,
                value: &str,
            ) -> Option<String> {
                Some(from_str_radix(value, 10).ok()?.to_string())
            }

            let value = match kind {
                NumKind::Int(Some(IntKind::I8)) => int(i8::from_str_radix, &value)?,
                NumKind::Int(Some(IntKind::I16)) => int(i16::from_str_radix, &value)?,
                NumKind::Int(Some(IntKind::I32)) => int(i32::from_str_radix, &value)?,
                NumKind::Int(Some(IntKind::I64)) => int(i64::from_str_radix, &value)?,
                NumKind::Int(Some(IntKind::I128)) => int(i128::from_str_radix, &value)?,
                NumKind::Int(Some(IntKind::Isize)) => int(TargetIsize::from_str_radix, &value)?,
                NumKind::Int(Some(IntKind::U8)) => int(u8::from_str_radix, &value)?,
                NumKind::Int(Some(IntKind::U16)) => int(u16::from_str_radix, &value)?,
                NumKind::Int(Some(IntKind::U32)) => int(u32::from_str_radix, &value)?,
                NumKind::Int(Some(IntKind::U64)) => int(u64::from_str_radix, &value)?,
                NumKind::Int(Some(IntKind::U128)) => int(u128::from_str_radix, &value)?,
                NumKind::Int(Some(IntKind::Usize)) => int(TargetUsize::from_str_radix, &value)?,
                NumKind::Int(None) => match value.starts_with('-') {
                    true => int(i128::from_str_radix, &value)?,
                    false => int(u128::from_str_radix, &value)?,
                },
                NumKind::Float(Some(FloatKind::F32)) => value.parse::<f32>().ok()?.to_string(),
                NumKind::Float(Some(FloatKind::F64) | None) => {
                    value.parse::<f64>().ok()?.to_string()
                }
                // FIXME: implement once `f16` and `f128` are available
                NumKind::Float(Some(FloatKind::F16 | FloatKind::F128)) => return None,
            };
            match value == orig_value {
                true => Cow::Borrowed(orig_value),
                false => Cow::Owned(value),
            }
        }
        Expr::BoolLit(true) => Cow::Borrowed("true"),
        Expr::BoolLit(false) => Cow::Borrowed("false"),
        _ => return None,
    };

    // escape the un-string-escaped input using the selected escaper
    Some(Writable::Lit(match output {
        OutputKind::Text => WithSpan::new_with_full(value, expr.span()),
        OutputKind::Html => {
            let mut escaped = String::with_capacity(value.len() + 20);
            write_escaped_str(&mut escaped, &value).ok()?;
            match escaped == value {
                true => WithSpan::new_with_full(value, expr.span()),
                false => WithSpan::new_with_full(Cow::Owned(escaped), expr.span()),
            }
        }
    }))
}

#[derive(Clone, Default)]
struct LocalVariableMeta {
    refs: Option<String>,
    initialized: bool,
}

#[derive(Clone)]
struct LocalCallerMeta<'a> {
    def: &'a Call<'a>,
    call_ctx: Context<'a>,
}

#[derive(Clone)]
enum LocalMeta<'a> {
    /// Normal variable
    Variable(LocalVariableMeta),

    /// This special variable is a caller alias. It's another name for caller().
    CallerAlias(LocalCallerMeta<'a>),

    /// Represents a "negative" local variable. Meaning: When the resolve methods
    /// encounters a negative on its path down the stack of scopes, it will immediately
    /// return without result. This is required to "block out" variables outside of a certain scope
    Negative,
}

impl<'a> LocalMeta<'a> {
    /// Variable declaration only - no value yet.
    const fn var_decl() -> Self {
        Self::Variable(LocalVariableMeta {
            refs: None,
            initialized: false,
        })
    }

    /// Variable definition - fully initialized.
    const fn var_def() -> Self {
        Self::Variable(LocalVariableMeta {
            refs: None,
            initialized: true,
        })
    }

    /// Variable referencing another
    const fn var_with_ref(refs: String) -> Self {
        Self::Variable(LocalVariableMeta {
            refs: Some(refs),
            initialized: true,
        })
    }

    /// Special variable aliasing a `caller()`
    const fn caller(def: &'a Call<'a>, call_ctx: Context<'a>) -> Self {
        Self::CallerAlias(LocalCallerMeta { def, call_ctx })
    }
}

struct MapChain<'a> {
    scopes: Vec<HashMap<Cow<'a, str>, LocalMeta<'a>>>,
}

impl<'a> MapChain<'a> {
    fn new_empty() -> Self {
        Self { scopes: vec![] }
    }

    /// Iterates the scopes in reverse and searches for a local variable (of any kind) with the given key.
    ///
    /// # Returns
    /// - `Some(LocalMeta)` if any kind of local entry (except negative) with the key was found.
    /// - `None` otherwise
    fn get_any<'b>(&'b self, key: &str) -> Option<&'b LocalMeta<'a>> {
        match self.scopes.iter().rev().find_map(|set| set.get(key)) {
            Some(LocalMeta::Negative) => None,
            Some(local) => Some(local),
            _ => None,
        }
    }

    /// Iterates the scopes in reverse and searches for a local variable with the given key.
    ///
    /// # Returns
    /// - `Some(LocalVariableMeta)` if the first encountered entry for key was a variable
    /// - `None` otherwise
    fn get<'b>(&'b self, key: &str) -> Option<&'b LocalVariableMeta> {
        match self.scopes.iter().rev().find_map(|set| set.get(key)) {
            Some(LocalMeta::Variable(var)) => Some(var),
            _ => None,
        }
    }

    /// Iterates the scopes in reverse and searches for a `CallerAlias`
    ///
    /// # Returns
    /// - `Some(LocalCallerMeta)` if the first encountered entry for key was a caller alias
    /// - `None` otherwise
    fn get_caller<'b>(&'b self, key: &str) -> Option<&'b LocalCallerMeta<'a>> {
        match self.scopes.iter().rev().find_map(|set| set.get(key)) {
            Some(LocalMeta::CallerAlias(caller)) => Some(caller),
            _ => None,
        }
    }

    fn is_current_empty(&self) -> bool {
        self.scopes.last().unwrap().is_empty()
    }

    fn insert(&mut self, key: Cow<'a, str>, val: LocalMeta<'a>) {
        self.scopes.last_mut().unwrap().insert(key, val);

        // Note that if `insert` returns `Some` then it implies
        // an identifier is reused. For e.g. `{% macro f(a, a) %}`
        // and `{% let (a, a) = ... %}` then this results in a
        // generated template, which when compiled fails with the
        // compile error "identifier `a` used more than once".
    }

    fn insert_with_default(&mut self, key: Cow<'a, str>) {
        self.insert(key, LocalMeta::var_decl());
    }

    fn resolve(&self, name: &str) -> Option<String> {
        self.get(&Cow::Borrowed(name)).map(|meta| match &meta.refs {
            Some(expr) => expr.clone(),
            None => name.to_string(),
        })
    }

    fn resolve_or_self(&self, name: &str) -> String {
        self.resolve(name).unwrap_or_else(|| format!("self.{name}"))
    }

    fn stack_push(&mut self) {
        self.scopes.push(HashMap::default());
    }

    fn stack_pop(&mut self) {
        self.scopes.pop().unwrap();
    }
}

impl Default for MapChain<'_> {
    fn default() -> Self {
        Self {
            scopes: vec![HashMap::default()],
        }
    }
}

/// Returns `true` if enough assumptions can be made,
/// to determine that `self` is copyable.
fn is_copyable(expr: &Expr<'_>) -> bool {
    is_copyable_within_op(expr, false)
}

fn is_copyable_within_op(expr: &Expr<'_>, within_op: bool) -> bool {
    match expr {
        Expr::BoolLit(_)
        | Expr::NumLit(_, _)
        | Expr::StrLit(_)
        | Expr::CharLit(_)
        | Expr::BinOp(_)
        | Expr::Range(..) => true,
        Expr::Unary(.., expr) => is_copyable_within_op(expr, true),
        // The result of a call likely doesn't need to be borrowed,
        // as in that case the call is more likely to return a
        // reference in the first place then.
        Expr::Call { .. } | Expr::Path(..) | Expr::Filter(..) | Expr::RustMacro(..) => true,
        // If the `expr` is within a `Unary` or `BinOp` then
        // an assumption can be made that the operand is copy.
        // If not, then the value is moved and adding `.clone()`
        // will solve that issue. However, if the operand is
        // implicitly borrowed, then it's likely not even possible
        // to get the template to compile.
        _ => within_op && is_associated_item_self(expr),
    }
}

/// Returns `true` if this is an `AssociatedItem` where the `obj` is `"self"`.
fn is_associated_item_self(mut expr: &Expr<'_>) -> bool {
    loop {
        match expr {
            Expr::AssociatedItem(obj, _) if matches!(***obj, Expr::Var("self")) => return true,
            Expr::AssociatedItem(obj, _) if matches!(***obj, Expr::AssociatedItem(..)) => {
                expr = obj
            }
            _ => return false,
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum DisplayWrap {
    Wrapped,
    Unwrapped,
}

#[derive(Default, Debug)]
struct WritableBuffer<'a> {
    buf: Vec<Writable<'a>>,
    discard: bool,
}

impl<'a> WritableBuffer<'a> {
    fn push(&mut self, writable: Writable<'a>) {
        if !self.discard {
            self.buf.push(writable);
        }
    }
}

impl<'a> Deref for WritableBuffer<'a> {
    type Target = [Writable<'a>];

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.buf.as_slice()
    }
}

#[derive(Debug)]
enum Writable<'a> {
    Lit(WithSpan<'a, Cow<'a, str>>),
    Expr(&'a WithSpan<'a, Box<Expr<'a>>>),
}

macro_rules! make_token_match {
    ($op:ident @ $span:ident => $($tt:tt)+) => {
        match $op {
            $(stringify!($tt) => Token![$tt]($span).into_token_stream(),)+
            _ => unreachable!(),
        }
    };
}

#[inline]
#[track_caller]
fn logic_op(op: &str, span: proc_macro2::Span) -> TokenStream {
    make_token_match!(op @ span => && || ^)
}

#[inline]
#[track_caller]
fn unary_op(op: &str, span: proc_macro2::Span) -> TokenStream {
    make_token_match!(op @ span => - ! * &)
}

#[inline]
#[track_caller]
fn range_op(op: &str, span: proc_macro2::Span) -> TokenStream {
    make_token_match!(op @ span => .. ..=)
}

#[inline]
#[track_caller]
fn binary_op(op: &str, span: proc_macro2::Span) -> TokenStream {
    make_token_match!(op @ span => * / % + - << >> & ^ | == != < > <= >= && || .. ..=)
}
