
### Literals
```js
// special value equivalent to 'nil' or 'null' in other languages
none

// numbers
// integer literals
1
1i
10000
// float literals
1f
1.0
1.2e2
// bigint literals
10000000000000000000000000000000000000000000n

// boolean
true
false

// string
"asdf"
'asdf'
"unicode is fine too 😂"

// f-string
f"1 + 1 is {1 + 1}"

// map
{ key0: value0, key1: value1 }
{ [expression()]: value }

// array
[0, 1, 2, expr(), "asdf"]

// error values
error "failure"
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
valid_identifier0
// 0invalid_identifier

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
"test" is Type // type comparison
// indexing
index[10]
index["test"]
index[dynamic]
// calls
call()
// property access
dot.access
optional?.a?.b?.access // returns `none` if anything in the chain is equal to `none`
...spread
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

// closures
fn make_counter(start, step) {
    return fn() {
        start = start + step;
        return start - step;
    }
}
let c = make_counter(5, 10);
print(c()); // 5
print(c()); // 15
print(c()); // 25
```

### Structs
```rust
// structs are 
struct Type(field, defaulted = none) {
    init { /* initializer */ }
    method(self) { print self.field }
    shorthand(self) => self.field
}
let v = Type("test")
v.method() // "test"
v.field = 50
print v.shorthand() // 50
print Type.field // none

// struct fields cannot be added or removed
// v.nonexistent = "test"; // error
print v.nonexistent; // none

struct List(head, tail) {
    // builtins are special methods which are marked with the `@` symbol
    // they allow overloading various operators and implementing protocols, 
    // such as the iterator protocol
    @iter(self) => ListIterator(self.head)
}
struct Vec3(x, y, z) {
    // overloading arithmetic operators
    @add(self, other) => (
        self.x += other.x,
        self.y += other.y,
        self.z += other.z,
        self
    )
    // three-way comparison
    @cmp(self, other) {
        if (self.x == other.x && self.y == other.y && self.z == other.z) {
            0
        } else {
            -1
        }
    } 
}
let v = Vec3(1, 1, 1) + Vec3(2, 2, 0);
print(v == Vec3(3, 3, 1)); // true
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
for i in 0..10 { print(i) }

// `iterable` must have the `@iter` builtin defined,
// and it must return an object which has the 
// `@next` and `@done` builtins defined
for item in iterable { ... }
// while loop
while condition {
    // loop controls
    break;
    continue;
}
// labeled loops
@a: loop {
    @b: loop {
        @c: loop {
            break @a
        }
        continue @a
    }
}

// returns are allowed at the top level
return;
return expression();

// a `do` block evaluates to the last expression in the block
// the last expression is 'none' if there is no other expression,
// or if the last expression is terminated by a semicolon
(do { 0 } == 0)
(do { 0; } == none)

// `defer` accepts either a function call or a block, which
// will be executed at the end of the current block's scope
{
    let file = File.open("something.txt")
    defer file.close()
    file.write("something")
    // file.close() called here
}
// a `defer` block is syntax sugar for a deferred closure:
{
    let file = File.open("something.txt")
    defer file.close()
    defer { if some_condition(file) { file.write("something else") } }
    // the line above is equivalent to:
    // defer (fn() { if some_condition(file) { file.write("something else") } })()
    file.write("something")
    // defer { if ... { ... } } executed here
    // defer file.close() called here
}
// defers are executed in reverse order of evaluation
{
    defer { print("a") }
    defer { print("b") }
    defer { print("c") }
    // print c
    // prints b
    // prints a
}
// defers are *guaranteed* to execute even in the case of a panic:
{ // prints "we're fine!" followed by the panic message and stack trace
    defer { print("we're fine!") }
    panic("something went wrong, unwinding stack")
}
// note that a `return` inside of a defer block will simply exit
// out of the block, and not the function in which it appears
// as explained a bit above, deferred blocks implicitly create closures,
// so it's the same as returning from the closure
fn test() {
    { defer { return; } }
    // the above is equivalent to:
    // { defer (fn(){ return; })() }
    print("reachable");
}

// even though you may execute arbitrary code from within a defer block,
// there is still no way to catch a panic.
// to create recoverable errors, use the built-in `ok`, `err` and `try` facilities:
fn validate(value) {
    if value > 10 {
        return err "value too large"
    } else {
        return ok value + 5
    }
}
let value = 10
if let ok(valid) = validate(value) {
    print(valid);
} else {
    print(f"invalid value: {value}");
}

// a `try` expression simplifies error propagation
// it is syntax sugar for:
// let v = do {
//     let temp = fallible();
//     if temp is err { return temp }
//     temp.unwrap()
// }
let v = try fallible()
```
