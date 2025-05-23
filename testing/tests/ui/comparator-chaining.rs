// Comparison operators cannot be chained, so our parser must reject chained comparisons.

use askama::Template;

#[derive(Template)]
#[template(ext = "txt", source = "{{ a == b != c }}")]
struct EqNe {
    a: usize,
    b: usize,
    c: usize,
}

#[derive(Template)]
#[template(ext = "txt", source = "{{ a <= b < c }}")]
struct Between {
    a: usize,
    b: usize,
    c: usize,
}

#[derive(Template)]
#[template(ext = "txt", source = "{{ ((a == b) == c) == d == e }}")]
struct ThreeTimesOk {
    a: usize,
    b: usize,
    c: usize,
    d: usize,
    e: usize,
}

#[derive(Template)]
#[template(ext = "txt", source = "{{ a == (b == (c == d == e)) }}")]
struct ThreeTimesOk2 {
    a: usize,
    b: usize,
    c: usize,
    d: usize,
    e: usize,
}

// Regression test for <https://github.com/askama-rs/askama/issues/454>
#[derive(Template)]
#[template(
    ext = "",
    source = "\u{c}{{vu7218/63e3666663-666/3330e633/63e3666663666/3333<c\"}\u{1}2}\0\"<c7}}2\"\"\"\"\0\0\0\0"
)]
struct Regression {}

fn main() {}
