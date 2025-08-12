use askama::Template;

// Ensure that paths starting with `::` are supported correctly.
#[test]
fn test_path_starting_with_colon() {
    #[derive(Template)]
    #[template(source = r#"���{{::std::format!("")}}�  �t�"#, ext = "txt")]
    struct X;

    assert_eq!(X.render().unwrap(), "����  �t�");
}
