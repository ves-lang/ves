# ves-error
This crate contains the primitives used for diagnostic collection and reporting.


## Example Usage
```rust
use ves_error::{VesFileDatabase, ErrCtx, VesError};

// A sample source code file
let source = r#"
fn test() {
    mut unused = 75
}
"#;

// Add the file to the database and get its ID
let mut db = VesFileDatabase::default();
let id = db.add_snippet(source.into());

// Create an error using the obtained file id and a span.
let error =
    VesError::resolution_wildcard("Variable `unused` is never used", 21..27, id)
        .with_function("test");


// Report the error to STDERR.
db.report_one(&error).unwrap();


// Alternatively, create a context for errors and record our error.
let mut ex = ErrCtx::new();
ex.record(error);

// Report all errors in the context to STDERR.
db.report(&ex).unwrap();
```
