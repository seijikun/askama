// Regression test for <https://github.com/askama-rs/askama/issues/478>.

use askama::Template;

// Cstring literals must not contain NULs.

#[derive(Template)]
#[template(
    source = "{{ z!(cr#\"\0\"#) }}",
    ext = "txt"
)]
struct MacroCallRawCstring1;

#[derive(Template)]
#[template(
    source = "{{ z!(cr##\"\0\"##) }}",
    ext = "txt"
)]
struct MacroCallRawCstring2;

#[derive(Template)]
#[template(
    source = "{{ z!(cr###\"\0\"###) }}",
    ext = "txt"
)]
struct MacroCallRawCstring3;

// Binary string literals must not contain NULs.

#[derive(Template)]
#[template(
    source = "{{ z!(br#\"😶‍🌫️\"#) }}",
    ext = "txt"
)]
struct MacroCallRawBinaryString1;

#[derive(Template)]
#[template(
    source = "{{ z!(br##\"😶‍🌫️\"##) }}",
    ext = "txt"
)]
struct MacroCallRawBinaryString2;

#[derive(Template)]
#[template(
    source = "{{ z!(br###\"😶‍🌫️\"###) }}",
    ext = "txt"
)]
struct MacroCallRawBinaryString3;

// Only `r#` is allowed as prefix idenfiers

#[derive(Template)]
#[template(
    source = "{{ z!(br#async) }}",
    ext = "txt"
)]
struct MacroCallIllegalPrefix1;

#[derive(Template)]
#[template(
    source = "{{ z!(cr#async) }}",
    ext = "txt"
)]
struct MacroCallIllegalPrefix2;

#[derive(Template)]
#[template(
    source = "{{ z!(r##async) }}",
    ext = "txt"
)]
struct MacroCallIllegalPrefix3;

#[derive(Template)]
#[template(
    source = "{{ z!(br##async) }}",
    ext = "txt"
)]
struct MacroCallIllegalPrefix4;

#[derive(Template)]
#[template(
    source = "{{ z!(cr##async) }}",
    ext = "txt"
)]
struct MacroCallIllegalPrefix5;

#[derive(Template)]
#[template(
    source = "{{ z!(hello#world) }}",
    ext = "txt"
)]
struct MacroCallReservedPrefix1;

#[derive(Template)]
#[template(
    source = "{{ z!(hello##world) }}",
    ext = "txt"
)]
struct MacroCallReservedPrefix2;

// No more than 255 hashes

#[derive(Template)]
#[template(path = "macro-call-raw-string-many-hashes.html")]
struct MacroCallManyHashes;

fn main() {}
