fn main() {
    use ves_error::VesFileDatabase;
    use ves_parser::{Lexer, Parser};

    // A sample source code file
    let source = r#"print("hello, world!")"#;

    // Add the file to the database and get its ID
    let mut db = VesFileDatabase::default();
    let id = db.add_snippet(source.into());

    // Create a parser for the given file ID, and run it
    let ast = match Parser::new(Lexer::new(&source), id, &db).parse() {
        Ok(ast) => ast,
        Err(ex) => return db.report(&ex).unwrap(),
    };
    // The AST contains the imports, exports, globals, and every statement in the body
    println!("{:?}", ast);
}
