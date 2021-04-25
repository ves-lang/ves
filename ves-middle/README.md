# ves-frontend
This crate contains the implementations of the front-end passes that operate on the AST.


## TODOs
1. [ ] Resolver
    1. [ ] unused / used variable checking
    2. [ ] mut / let semantics checking
    3. [ ] shadowing support
    4. [ ] break / continue checking
    5. [ ] loop label checking
    6. [ ] `self` usage checking
    7. [ ] TCO detection
2. [ ] Simple Escape Analysis ???
3. [ ] Constant Folder