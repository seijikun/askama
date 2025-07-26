#![cfg_attr(docsrs, feature(doc_cfg, doc_auto_cfg))]
#![deny(elided_lifetimes_in_paths)]
#![deny(unreachable_pub)]

mod filter_fn;
mod helpers;

use proc_macro::TokenStream;
use syn::{ItemFn, parse_macro_input};

use crate::filter_fn::filter_fn_impl;

askama_derive::make_derive_template! {
    #[proc_macro_derive(Template, attributes(template))]
    pub fn derive_template() {
        extern crate askama;
    }
}

#[proc_macro_attribute]
pub fn filter_fn(_args: TokenStream, item: TokenStream) -> TokenStream {
    let ffn = parse_macro_input!(item as ItemFn);
    match filter_fn_impl(ffn) {
        Ok(tt) => tt.into(),
        Err(err) => err.into_compile_error().into(),
    }
}
