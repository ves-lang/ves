
### Literals
```rust
// special value equivalent to 'nil' or 'null' in other languages
none

// number
1
1.2
100_000.2
100_000.2e2

// boolean
true
false

// string
"asdf"
'asdf'
"unicode is fine too 😂"

// f-string
f"1 + 1 is {1 + 1}"

// dictionary
{ "key0": value0, "key1": value1 }
// 
{ expression(): value }
// duplicate (constant) keys are a compile-time error
// { "key": value, "key": value }

// array
[0, 1, 2, expr(), "asdf"]

// result
ok "success"
err "failure"
```

### Variables
```rust
// not re-assignable
let x = 10;
x = "test"; // error

// re-assignable
mut x = 10;
x = "test"; // valid

// valid identifiers are ASCII with underscores, with digits anywhere but the first character
// TODO: unicode identifiers
valid_identifier0
0invalid_identifier

// variable shadowing
let x = 10;
// let x = 5; // error
{ let x = x; } // valid
```

### Operators
```rust
- 1
! 1
1 + 1
1 - 1
1 * 1
1 / 1
1 ** 1
1 % 1
1 == 1
1 != 1
1 <= 1
1 >= 1
1 < 1
1 > 1
"test" in thing // property existence check
"test" is Type // with built-ins 'dict', 'list', 'num', 'str', 'bool', 'none', 'some'
("grouping")
index[10]
index["test"]
index[dynamic]
call()
dot.access
optional?.access // returns `none` if anything in the chain is `none`
...spread
```

### Control flow
```rust
// if/else if/else is an expression
// it evaluates to the result of the chosen branch block
let v = if condition { ... }
else if condition { ... }
else { ... }
// the last expression in an if expression block is 'none' if there is no other expression
let v = if condition {
    if condition2 {
        expression()
    }
    none // this is implicit
}

// infinite loop
loop { ... }
// for loop
for initializer; condition; increment { ... }
// for..in loop
for item in rangeStart..rangeEnd { ... }
for item in rangeStart..=rangeEnd { ... }
for item in iterable { ... }
// while loop
while condition { ... }
// loop controls
break;
continue;
// may only appear inside functions
return;
return expression();

// a `do` block evaluates to the last expression in the block
// the last expression is 'none' if there is no other expression
let v = do { expression() };

// a `try` expression simplifies error propagation
// sugar for:
// let v = do {
//     let temp = fallible();
//     if temp is err { return temp }
//     temp.unwrap()
// }
let v = try fallible()
```

### Functions
```rust
fn name() {
    /* ... */
}
fn name(arg) {
    /* ... */
}
fn name(a, b, c) {
    /* ... */
}
// varargs
fn name(a, b, ...args) {
    /* ... */
}
// default parameter - must not be followed by non-defaulted parameter
fn name(a, b, c = none) {

}

// shorthand syntax
fn name() => "expression"
print name(); // expression

// anonymous function
let f = fn() => 0
print f(); // 0

// closure semantics:
fn make_closure(mut value) {
    // closures capture *values*
    return {
        get: fn() => value,
        set: fn(v) => value = v
    }
}
let closure = make_closure(100);
print closure.get(); // 100
closure.set(150);
print closure.get(); // still 100

// you can wrap your value in an object to imitate capture by variable semantics:
fn wrap(value) {
    return { "value": value }
}
fn make_closure2(value) {
    let wrapper = wrap(value)
    return {
        get: fn() => wrapper.value
        set: fn(v) => wrapper.value = v
    }
}
let closure = make_closure2(100);
print closure.get(); // 100
closure.set(150);
print closure.get(); // 150
```

### Structs
```rust
struct Type(field, defaulted = none) {
    init { /* initializer */ }
    method() { print self.field }
    shorthand() => self.field
    static field = none
    static static_method() { print Type.field }
}
let v = Type("test")
v.method() // "test"
v.field = 50
print v.shorthand() // 50
print Type.field // none
Type.field = 10
Type.static_method() // 10

// struct fields cannot be added or removed
// v.nonexistent = "test"; // error
print v.nonexistent; // none
```
