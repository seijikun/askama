use askama::Template;

mod filters {
    use askama::Values;

    pub fn do_nothing<'a>(s: &'a str, _: &dyn Values) -> askama::Result<&'a str> {
        Ok(s)
    }
}

#[derive(Template)]
#[template(source = r#"{{ a | do_nothing(absolutely = "nothing") }}"#, ext = "txt")]
struct CustomFiltersCannotTakeNamedArguments<'a> {
    a: &'a str,
}

fn main() {}
