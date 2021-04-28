# ves-frontend
This crate contains the implementations of the front-end passes that operate on the AST.


## TODOs
1. [ ] Resolver
    1. [x] unused / used variable checking
    2. [x] mut / let semantics checking
    3. [ ] shadowing support
    4. [x] break / continue checking
    5. [x] loop label checking
    6. [x] `self` usage checking
    7. [x] TCO detection
2. [x] Constant Folder
    1. [x] Fold expressions
    2. [x] Propagate constant `let` variables
    3. [x] Fold if expressions
    4. [x] Eliminate dead `let` stores where possible
3. [ ] Simple escape analysis???
