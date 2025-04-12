// This example contains a custom filter `|cased`.
// Depending on the runtime value `"case"`, the input is either turned
// into lower case, upper case, or left alone, if the runtime value is undefined.

use std::any::Any;
use std::fmt::{self, Write};

use askama::filters::FastWritable;
use askama::{Template, Values};

mod filters {
    use super::*;

    // This filter does not transform its input directly.
    // It is captured instead, so we can provide it with runtime values.
    pub fn cased<S>(source: S) -> askama::Result<Cased<S>> {
        Ok(Cased { source })
    }

    pub struct Cased<S> {
        source: S,
    }

    // This trait implementation has access to runtime values.
    impl<S: FastWritable> FastWritable for Cased<S> {
        fn write_into<W: fmt::Write + ?Sized>(
            &self,
            dest: &mut W,
            values: &dyn Values,
        ) -> askama::Result<()> {
            let case = askama::get_value(values, "case").ok();

            let mut buffer = String::new();
            self.source.write_into(&mut buffer, values)?;

            write_with_case(dest, buffer, case.copied())?;
            Ok(())
        }
    }

    // A fallback `fmt::Display` implementation must always be implemented
    // for filters. This implementation does not have access to runtime values.
    impl<S: fmt::Display> fmt::Display for Cased<S> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
            // Instead of providing a default implementation,
            // returning an error is a valid option, too.
            let mut buffer = String::new();
            write!(buffer, "{}", &self.source)?;
            write_with_case(f, buffer, None)
        }
    }

    fn write_with_case<W: fmt::Write + ?Sized>(
        dest: &mut W,
        source: String,
        case: Option<Case>,
    ) -> fmt::Result {
        dest.write_str(&match case {
            Some(Case::Lower) => source.to_lowercase(),
            Some(Case::Upper) => source.to_uppercase(),
            None => source,
        })
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Case {
    Lower,
    Upper,
}

#[test]
fn test_runtime_values_in_custom_filters() {
    #[derive(Template)]
    #[template(ext = "txt", source = "Hello, {{ user | cased }}!")]
    struct MyStruct<'a> {
        user: &'a str,
    }

    // The filter source ("wOrLd") should be written in lower case.
    let values: (&str, &dyn Any) = ("case", &Case::Lower);
    assert_eq!(
        MyStruct { user: "wOrLd" }
            .render_with_values(&values)
            .unwrap(),
        "Hello, world!"
    );

    // The filter source ("wOrLd") should be written in upper case.
    let values: (&str, &dyn Any) = ("case", &Case::Upper);
    assert_eq!(
        MyStruct { user: "wOrLd" }
            .render_with_values(&values)
            .unwrap(),
        "Hello, WORLD!"
    );

    // The filter source ("wOrLd") should be written as is.
    assert_eq!(
        MyStruct { user: "wOrLd" }.render().unwrap(),
        "Hello, wOrLd!"
    );
}
