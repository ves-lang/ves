
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
// TODO: this is not enforced
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
"test" is Type // with built-ins 'Map', 'Array', 'Int', 'Float', 'String', 'Bool', 'None'
("grouping")
index[10]
index["test"]
index[dynamic]
call()
dot.access
optional?.access // returns `none` if anything in the chain is equal to `none`
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

// you can wrap your value in a map to imitate capture by variable semantics:
fn wrap(value) {
    return { "value": value }
}
fn make_closure2(value) {
    let wrapper = wrap(value)
    return {
        // these closures will capture `wrapper`, 
        // which is a reference to the map containing `value`
        // meaning it can be modified as such:
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
    // instance methods
    // declared with `self` as first parameter
    method(self) { print self.field }
    shorthand(self) => self.field
    // static fields
    field = none
    // static methods (= without `self`)
    static_method() { print Type.field }
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

struct List(head, tail) {
    // builtins are special methods which are marked with the `@` symbol
    // they allow overloading various operators and implementing protocols, 
    // such as the iterator protocol
    @iter(self) => ListIterator(self.head)
}
struct Vec3(x, y, z) {
    // overloading arithmetic operators example
    @add(self, other) => (
        self.x += other.x,
        self.y += other.y,
        self.z += other.z,
        self
    )
    @sub(self, other) => (
        self.x -= other.x,
        self.y -= other.y,
        self.z -= other.z,
        self
    )
    @eq(self, other) => (
        self.x == other.x &&
        self.y == other.y &&
        self.z == other.z
    )
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
    // none // this is implicit
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
