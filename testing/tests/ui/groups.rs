use askama::Template;

#[derive(Template)]
#[template(source = r#"{% let test = ( %}"#, ext = "html")]
struct TruncatedInput;

#[derive(Template)]
#[template(source = r#"{% let test = (a, %}"#, ext = "html")]
struct TruncatedInput2;

#[derive(Template)]
#[template(source = r#"{% let test = (a, b %}"#, ext = "html")]
struct TruncatedInput3;

#[derive(Template)]
#[template(source = r#"{% let test = (a, b, %}"#, ext = "html")]
struct TruncatedInput4;

#[derive(Template)]
#[template(source = r#"{% let test = (() %}"#, ext = "html")]
struct MoreOpenThanClose;

#[derive(Template)]
#[template(source = r#"{% let test = ((()) %}"#, ext = "html")]
struct MoreOpenThanClose2;

#[derive(Template)]
#[template(source = r#"{% let test = (,) %}"#, ext = "html")]
struct ExtraneousComma;

#[derive(Template)]
#[template(source = r#"{% let test = (,,) %}"#, ext = "html")]
struct ExtraneousComma2;

#[derive(Template)]
#[template(source = r#"{% let test = (a,,) %}"#, ext = "html")]
struct ExtraneousComma3;

#[derive(Template)]
#[template(source = r#"{% let test = (a, b,,) %}"#, ext = "html")]
struct ExtraneousComma4;

#[derive(Template)]
#[template(source = r#"{% let test = (, %}"#, ext = "html")]
struct NoCloseAndExtraneousComma;

#[derive(Template)]
#[template(source = r#"{% let test = (,, %}"#, ext = "html")]
struct NoCloseAndExtraneousComma2;

#[derive(Template)]
#[template(source = r#"{% let test = (a,, %}"#, ext = "html")]
struct NoCloseAndExtraneousComma3;

#[derive(Template)]
#[template(source = r#"{% let test = (a, b,, %}"#, ext = "html")]
struct NoCloseAndExtraneousComma4;

#[derive(Template)]
#[template(source = r#"{% let test = (a b) %}"#, ext = "html")]
struct MissingComma;

#[derive(Template)]
#[template(source = r#"{% let test = (a b c) %}"#, ext = "html")]
struct MissingComma2;

#[derive(Template)]
#[template(source = r#"{% let test = (a b %}"#, ext = "html")]
struct NoCloseAndMissingComma;

#[derive(Template)]
#[template(source = r#"{% let test = (a b c %}"#, ext = "html")]
struct NoCloseAndMissingComma2;

fn main() {}
