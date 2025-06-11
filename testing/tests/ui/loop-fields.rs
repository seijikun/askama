use askama::Template;

// Fail on unknown `loop` fields

#[derive(Template)]
#[template(
    source = "{% for _ in 0..10 %} {{ loop.index1 }} {% endfor %}",
    ext = "txt"
)]
struct UnknownLoopField;

fn main() {}
