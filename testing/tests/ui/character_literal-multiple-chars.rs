use askama::Template;

#[derive(Template)]
#[template(source = r#"{{ 'ab' }}"#, ext = "html")]
struct Multiple1;

#[derive(Template)]
#[template(source = r#"{{ '\0b' }}"#, ext = "html")]
struct Multiple2;

#[derive(Template)]
#[template(source = r#"{{ 'b\0' }}"#, ext = "html")]
struct Multiple3;

#[derive(Template)]
#[template(source = r#"{{ '\\0' }}"#, ext = "html")]
struct Multiple4;

#[derive(Template)]
#[template(source = r#"{{ '\u{1234}b' }}"#, ext = "html")]
struct Multiple5;

#[derive(Template)]
#[template(source = r#"{{ '\u{1234}b' }}"#, ext = "html")]
struct Multiple6;

#[derive(Template)]
#[template(source = r#"{{ '\u{1234}\u{1234}' }}"#, ext = "html")]
struct Multiple7;

#[derive(Template)]
#[template(source = r#"{{ b'ab' }}"#, ext = "html")]
struct ByteMultiple1;

#[derive(Template)]
#[template(source = r#"{{ b'\0b' }}"#, ext = "html")]
struct ByteMultiple2;

#[derive(Template)]
#[template(source = r#"{{ b'b\0' }}"#, ext = "html")]
struct ByteMultiple3;

#[derive(Template)]
#[template(source = r#"{{ b'\\0' }}"#, ext = "html")]
struct ByteMultiple4;

#[derive(Template)]
#[template(source = r#"{{ b'\u{1234}b' }}"#, ext = "html")]
struct ByteMultiple5;

#[derive(Template)]
#[template(source = r#"{{ b'\u{1234}b' }}"#, ext = "html")]
struct ByteMultiple6;

#[derive(Template)]
#[template(source = r#"{{ b'\u{1234}\u{1234}' }}"#, ext = "html")]
struct ByteMultiple7;

#[derive(Template)]
#[template(source = r#"{{ x!('ab') }}"#, ext = "html")]
struct Multiple1InMacro;

#[derive(Template)]
#[template(source = r#"{{ x!('\0b') }}"#, ext = "html")]
struct Multiple2InMacro;

#[derive(Template)]
#[template(source = r#"{{ x!('b\0') }}"#, ext = "html")]
struct Multiple3InMacro;

#[derive(Template)]
#[template(source = r#"{{ x!('\\0') }}"#, ext = "html")]
struct Multiple4InMacro;

#[derive(Template)]
#[template(source = r#"{{ x!('\u{1234}b') }}"#, ext = "html")]
struct Multiple5InMacro;

#[derive(Template)]
#[template(source = r#"{{ x!('\u{1234}b') }}"#, ext = "html")]
struct Multiple6InMacro;

#[derive(Template)]
#[template(source = r#"{{ x!('\u{1234}\u{1234}') }}"#, ext = "html")]
struct Multiple7InMacro;

#[derive(Template)]
#[template(source = r#"{{ x!(b'ab') }}"#, ext = "html")]
struct ByteMultiple1InMacro;

#[derive(Template)]
#[template(source = r#"{{ x!(b'\0b') }}"#, ext = "html")]
struct ByteMultiple2InMacro;

#[derive(Template)]
#[template(source = r#"{{ x!(b'b\0') }}"#, ext = "html")]
struct ByteMultiple3InMacro;

#[derive(Template)]
#[template(source = r#"{{ x!(b'\\0') }}"#, ext = "html")]
struct ByteMultiple4InMacro;

#[derive(Template)]
#[template(source = r#"{{ x!(b'\u{1234}b') }}"#, ext = "html")]
struct ByteMultiple5InMacro;

#[derive(Template)]
#[template(source = r#"{{ x!(b'\u{1234}b') }}"#, ext = "html")]
struct ByteMultiple6InMacro;

#[derive(Template)]
#[template(source = r#"{{ x!(b'\u{1234}\u{1234}') }}"#, ext = "html")]
struct ByteMultiple7InMacro;

fn main() {}
