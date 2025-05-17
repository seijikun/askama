use std::fmt;

use arbitrary::{Arbitrary, Unstructured};
use askama_derive::derive_template;
use prettyplease::unparse;
use proc_macro2::{Ident, Literal, Span, TokenStream};
use quote::{ToTokens, TokenStreamExt, quote};
use syn::token::Comma;
use syn::{File, parse2};
use unicode_ident::{is_xid_continue, is_xid_start};

const _: () = {
    assert!(
        !askama_derive::CAN_USE_EXTERNAL_SOURCES,
        "`askama_derive` can use external sources. Denying to fuzz for safety reasons.",
    );
};

impl<'a> super::Scenario<'a> for Scenario<'a> {
    type RunError = syn::Error;

    fn new(data: &'a [u8]) -> Result<Self, arbitrary::Error> {
        Self::arbitrary_take_rest(Unstructured::new(data))
    }

    fn run(&self) -> Result<(), Self::RunError> {
        let input = self.item.to_token_stream();
        // Any input AST should be parsable by the generator, maybe returning a `compile_error!`.
        let output = derive_template(input, import_askama);
        // The generated code should be parsable as rust source.
        let _: File = parse2(output)?;
        Ok(())
    }
}

fn import_askama() -> TokenStream {
    quote! {
        extern crate askama;
    }
}

#[derive(Debug, Arbitrary)]
pub struct Scenario<'a> {
    item: DeriveItem<'a>,
}

impl fmt::Display for Scenario<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { item } = self;
        let ts = quote! {
            use askama_derive::Ast;
            use quote::quote;

            #[test]
            fn test() -> Result<(), syn::Error> {
                let input = quote! {
                    #item
                };
                let output = derive_template(input, import_askama);
                let _: syn::File = syn::parse2(output)?;
                Ok(())
            }

            fn import_askama() -> TokenStream {
                quote! {
                    extern crate askama;
                }
            }
        };
        f.write_str(&unparse(&parse2(ts).map_err(|_| fmt::Error)?))
    }
}

#[derive(Debug, Arbitrary)]
pub struct DeriveItem<'a> {
    params: Option<MetaTemplate<'a>>,
    item: Item<'a>,
}

impl ToTokens for DeriveItem<'_> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let Self { params, item } = self;
        tokens.extend(quote! {
            #params
            #item
        });
    }
}

#[derive(Debug, Clone, Arbitrary)]
enum Item<'a> {
    StructItem(StructItem<'a>),
    Enum(Enum<'a>),
}

impl ToTokens for Item<'_> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            Item::StructItem(s) => tokens.extend(quote! {
                struct #s
            }),
            Item::Enum(s) => s.to_tokens(tokens),
        }
    }
}

#[derive(Debug, Clone, Arbitrary)]
enum StructItem<'a> {
    Empty(Empty<'a>),
    Struct(Struct<'a>),
    Tuple(Tuple<'a>),
}

impl ToTokens for StructItem<'_> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            StructItem::Empty(s) => s.to_tokens(tokens),
            StructItem::Struct(s) => s.to_tokens(tokens),
            StructItem::Tuple(s) => s.to_tokens(tokens),
        }
    }
}

#[derive(Debug, Clone, Arbitrary)]
struct Empty<'a> {
    name: Name<'a>,
}

impl ToTokens for Empty<'_> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.name.to_tokens(tokens);
    }
}

#[derive(Debug, Clone, Arbitrary)]
struct Struct<'a> {
    name: Name<'a>,
    fields: Vec<Field<'a>>,
}

impl ToTokens for Struct<'_> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let Self { name, fields } = self;
        tokens.extend(quote! {
            #name {
                #(#fields,)*
            }
        });
    }
}

#[derive(Debug, Clone, Arbitrary)]
struct Field<'a> {
    name: Name<'a>,
    type_: Name<'a>,
}

impl ToTokens for Field<'_> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let Self { name, type_ } = self;
        tokens.extend(quote! {
            #name: #type_
        });
    }
}

#[derive(Debug, Clone, Arbitrary)]
struct Tuple<'a> {
    name: Name<'a>,
    fields: Vec<Name<'a>>,
}

impl ToTokens for Tuple<'_> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let Self { name, fields } = self;
        tokens.extend(quote! {
            #name(#(#fields),*)
        });
    }
}

#[derive(Debug, Clone, Arbitrary)]
struct Enum<'a> {
    name: Name<'a>,
    variants: Vec<Variant<'a>>,
}

impl ToTokens for Enum<'_> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let Self { name, variants } = self;
        tokens.extend(quote! {
            enum #name {
                #(#variants),*
            }
        });
    }
}

#[derive(Debug, Clone, Arbitrary)]
struct Variant<'a> {
    params: Option<MetaTemplate<'a>>,
    item: StructItem<'a>,
}

impl ToTokens for Variant<'_> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let Self { params, item } = self;
        tokens.extend(quote! {
            #params
            #item
        });
    }
}

#[derive(Debug, Clone, Arbitrary)]
struct MetaTemplate<'a> {
    ext: Option<Ext<'a>>,
    source: Option<Source<'a>>,
}

impl ToTokens for MetaTemplate<'_> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let Self { ext, source } = self;
        let comma = (ext.is_some() && source.is_some()).then(Comma::default);
        tokens.extend(quote! {
            #[template(#ext #comma #source)]
        });
    }
}

#[derive(Debug, Clone, Arbitrary)]
struct Ext<'a>(LiteralString<'a>);

impl ToTokens for Ext<'_> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let Self(ext) = self;
        tokens.extend(quote!(ext = #ext));
    }
}

#[derive(Debug, Clone, Arbitrary)]
struct Source<'a>(LiteralString<'a>);

impl ToTokens for Source<'_> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let Self(source) = self;
        tokens.extend(quote!(source = #source));
    }
}

#[derive(Debug, Clone)]
struct Name<'a>(&'a str);

impl<'a> Arbitrary<'a> for Name<'a> {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let ident = <&str>::arbitrary(u)?;
        let mut chars = ident.chars();
        if chars.next().is_some_and(is_xid_start) && chars.all(is_xid_continue) {
            Ok(Self(ident))
        } else {
            Err(arbitrary::Error::IncorrectFormat)
        }
    }
}

impl ToTokens for Name<'_> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.append(Ident::new(self.0, Span::call_site()));
    }
}

#[derive(Debug, Clone, Arbitrary)]
struct LiteralString<'a>(&'a str);

impl ToTokens for LiteralString<'_> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.append(Literal::string(self.0));
    }
}
