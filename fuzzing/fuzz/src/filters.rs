use std::fmt::{self, Write};

use arbitrary::{Arbitrary, Unstructured};
use askama::filters::{self, AsIndent};

// ADD NEW ENTRIES AT THE BOTTOM!
#[derive(Arbitrary, Debug, Clone)]
pub enum Scenario<'a> {
    Text(Text<'a>),
    Join(Vec<&'a str>, &'a str),
    Unique(Vec<&'a str>),
    Wordcount(&'a str),
    // TODO: fmt
    // TODO: format
}

impl<'a> super::Scenario<'a> for Scenario<'a> {
    type RunError = askama::Error;

    fn new(data: &'a [u8]) -> Result<Self, arbitrary::Error> {
        Self::arbitrary_take_rest(Unstructured::new(data))
    }

    fn run(&self) -> Result<(), Self::RunError> {
        match self {
            &Scenario::Text(text) => run_text(text)?,
            Scenario::Join(input, separator) => {
                let _ = filters::join(input, separator)?.to_dev_null();
            }
            Scenario::Unique(items) => {
                let _ = filters::unique(items)?.collect::<Vec<_>>();
            }
            Scenario::Wordcount(input) => {
                let c = filters::wordcount(input);
                let _ = c.to_dev_null();
                let _ = c.into_count();
                return Ok(());
            }
        }
        Ok(())
    }
}

fn run_text(filter: Text<'_>) -> Result<(), askama::Error> {
    let Text { input, filter } = filter;
    let _ = match filter {
        TextFilter::Capitalize => filters::capitalize(input)?.to_dev_null(),
        TextFilter::Center(a) => filters::center(input, a)?.to_dev_null(),
        TextFilter::Indent {
            prefix,
            first,
            blank,
        } => filters::indent(input, prefix, first, blank)?.to_dev_null(),
        TextFilter::Linebreaks => filters::linebreaks(input)?.to_dev_null(),
        TextFilter::LinebreaksBr => filters::linebreaksbr(input)?.to_dev_null(),
        TextFilter::Lowercase => filters::lowercase(input)?.to_dev_null(),
        TextFilter::ParagraphBreaks => filters::paragraphbreaks(input)?.to_dev_null(),
        TextFilter::Safe(e) => filters::safe(input, e)?.to_dev_null(),
        TextFilter::Title => filters::title(input)?.to_dev_null(),
        TextFilter::Trim => filters::trim(input)?.to_dev_null(),
        TextFilter::Truncate(a) => filters::truncate(input, a)?.to_dev_null(),
        TextFilter::Uppercase => filters::uppercase(input)?.to_dev_null(),
        TextFilter::Urlencode => filters::urlencode(input)?.to_dev_null(),
        TextFilter::UrlencodeStrict => filters::urlencode_strict(input)?.to_dev_null(),
        TextFilter::Escape(escaper) => filters::escape(input, escaper)?.to_dev_null(),
        TextFilter::Filesizeformat(size) => filters::filesizeformat(size)?.to_dev_null(),
        TextFilter::Json => filters::json(input)?.to_dev_null(),
        TextFilter::JsonPretty(prefix) => filters::json_pretty(input, prefix)?.to_dev_null(),
    };
    Ok(())
}

impl fmt::Display for Text<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Text { input, filter } = *self;
        let content = match filter {
            TextFilter::Capitalize => format!("capitalize({input:?})"),
            TextFilter::Center(a) => format!("center({input:?}, {a:?})"),
            TextFilter::Indent {
                prefix,
                first,
                blank,
            } => {
                format!("indent({input:?}, {prefix}, {first:?}, {blank:?})")
            }
            TextFilter::Linebreaks => format!("linebreaks({input:?})"),
            TextFilter::LinebreaksBr => format!("linebreaksbr({input:?})"),
            TextFilter::Lowercase => format!("lowercase({input:?})"),
            TextFilter::ParagraphBreaks => format!("paragraphbreaks({input:?})"),
            TextFilter::Safe(e) => format!("safe({input:?}, {e})"),
            TextFilter::Title => format!("title({input:?})"),
            TextFilter::Trim => format!("trim({input:?})"),
            TextFilter::Truncate(a) => format!("truncate({input:?}, {a:?})"),
            TextFilter::Uppercase => format!("uppercase({input:?})"),
            TextFilter::Urlencode => format!("urlencode({input:?})"),
            TextFilter::UrlencodeStrict => format!("urlencode_strict({input:?})"),
            TextFilter::Escape(e) => format!("escape({input:?}, {e})"),
            TextFilter::Filesizeformat(size) => format!("filesizeformat({size:?})"),
            TextFilter::Json => format!("json({input:?})"),
            TextFilter::JsonPretty(prefix) => format!("json_pretty({input:?}, {prefix})"),
        };
        write!(
            f,
            "\
use askama::filters;

#[test]
fn test() -> askama::Result<()> {{
    let _: String = filters::{content}?.to_string();
    Ok(())
}}\
            ",
        )
    }
}

impl fmt::Display for Scenario<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let content = match self {
            Scenario::Text(text) => return text.fmt(f),
            Scenario::Join(items, separator) => {
                format!("    let _: String = filters::join({items:?}, {separator:?})?.to_string();")
            }
            Scenario::Unique(items) => {
                format!("    let _: Vec<_> = filters::unique({items:?})?.count();")
            }
            &Scenario::Wordcount(input) => format!(
                "\
    let mut c = filters::wordcount({input:?});
    let _: String = c.to_string();
    let _: usize = c.into_count();\
                ",
            ),
        };
        write!(
            f,
            "\
use askama::filters;

#[test]
fn test() -> askama::Result<()> {{
    {content}
    Ok(())
}}\
            ",
        )
    }
}

#[derive(Arbitrary, Debug, Clone, Copy)]
pub struct Text<'a> {
    input: &'a str,
    filter: TextFilter<'a>,
}

// ADD NEW ENTRIES AT THE BOTTOM!
#[derive(Arbitrary, Debug, Clone, Copy)]
enum TextFilter<'a> {
    Capitalize,
    Center(usize),
    Indent {
        prefix: Prefix<'a>,
        first: bool,
        blank: bool,
    },
    Linebreaks,
    LinebreaksBr,
    Lowercase,
    ParagraphBreaks,
    Safe(Escaper),
    Title,
    Trim,
    Truncate(usize),
    Uppercase,
    Urlencode,
    UrlencodeStrict,
    Escape(Escaper),
    Filesizeformat(f32),
    Json,
    JsonPretty(Prefix<'a>),
}

#[derive(Arbitrary, Debug, Clone, Copy)]
enum Prefix<'a> {
    Width(usize),
    Prefix(&'a str),
}

impl std::fmt::Display for Prefix<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Prefix::Width(v) => write!(f, "{v:?}"),
            Prefix::Prefix(v) => write!(f, "{v:?}"),
        }
    }
}

impl AsIndent for Prefix<'_> {
    fn as_indent(&self) -> &str {
        match self {
            Prefix::Width(v) => v.as_indent(),
            Prefix::Prefix(v) => v.as_indent(),
        }
    }
}

#[derive(Arbitrary, Debug, Clone, Copy)]
enum Escaper {
    Html,
    Text,
}

impl fmt::Display for Escaper {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Html => "Html",
            Self::Text => "Text",
        })
    }
}

impl filters::Escaper for Escaper {
    fn write_escaped_str<W: fmt::Write>(&self, dest: W, string: &str) -> fmt::Result {
        match self {
            Escaper::Html => filters::Html.write_escaped_str(dest, string),
            Escaper::Text => filters::Text.write_escaped_str(dest, string),
        }
    }

    fn write_escaped_char<W: fmt::Write>(&self, dest: W, c: char) -> fmt::Result {
        match self {
            Escaper::Html => filters::Html.write_escaped_char(dest, c),
            Escaper::Text => filters::Text.write_escaped_char(dest, c),
        }
    }
}

struct DevNull;

impl fmt::Write for DevNull {
    fn write_str(&mut self, _: &str) -> fmt::Result {
        Ok(())
    }

    fn write_char(&mut self, _: char) -> fmt::Result {
        Ok(())
    }

    // Must not implement `write_fmt()`, because that's where the recursive calls happen.
}

trait ToDevNull {
    fn to_dev_null(&self) -> fmt::Result;
}

impl<T: fmt::Display> ToDevNull for T {
    fn to_dev_null(&self) -> fmt::Result {
        write!(DevNull, "{self}")
    }
}
