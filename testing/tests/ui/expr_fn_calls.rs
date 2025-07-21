#![allow(unused_variables)]

use askama::Template;

pub fn static_fn(arg: &str) -> &str { arg }
pub fn static_fn2(arg: &str) -> Option<&str> { Some(arg) }


#[derive(Template)]
#[template(source = "{{ test_fn(arg = 5) }}", ext = "html")]
struct NamedArgsInRustExprMemberFn;

impl NamedArgsInRustExprMemberFn {
    pub fn test_fn(&self, arg: u64) -> &'static str {
        "This is a test"
    }
}


#[derive(Template)]
#[template(source = r#"{{ self::static_fn(arg = "test") }}"#, ext = "html")]
struct NamedArgsInRustExprStaticCall;


#[derive(Template)]
#[template(source = r#"{{ self::static_fn2("test").unwrap(arg = "test") }}"#, ext = "html")]
struct NamedArgsInRustExprStaticCall2;


#[derive(Template)]
#[template(source = r#"{% let test = self::static_fn(arg = "test") %}"#, ext = "html")]
struct NamedArgsInRustExprStaticCall3;


fn main() {}
