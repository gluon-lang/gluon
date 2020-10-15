# Syntax and semantics

Gluon is a functional language at heart, basing its syntax on languages such as F#, OCaml and Haskell.
The syntax may thus look strange if you are coming from C-like languages but don't be discouraged!
There is actually very little syntax to learn.

If, on the other hand, you are familiar with functional languages you will be right at home. Roughly speaking, Gluon takes the expression syntax from F# and OCaml and uses the type syntax of Haskell.

### Identifiers and Literals

The simplest syntactical elements in Gluon are identifiers and literals and none of them should be especially surprising if you are experienced in programming.

Identifiers are a sequence of alphanumeric characters including underscore ("\_") which are required to start with either a letter or an underscore. Literals come in four different forms - integer, float, string and character literals.

```f#
// An identifier
abc123_

// An integer literal

42
// A float literal
3.14

// A string literal
"Hello world"

// A raw string literal
r"Can contain newlines
world"
r#"With # as delimiters raw strings can also contain quotes without escaping `"` "#
r###" "## "###

// A character literal
'e'
```

### Comments

Comments should be immediately familiar if you are accustomed to C-like languages.

`//` starts a line comment which is ended by a newline

`/*` starts a block comment which is ended by `*/`

### Functions

```f#
f x "argument" 3
```

Being a functional language, functions are everywhere. Because of this, calling functions have an intentionally minimalistic syntax where there is no need to enclose arguments as a parenthesized list of arguments. Instead, arguments are separated by whitespace.

Another way of calling a function is through infix notation since gluon implements all operators as just functions.

```f#,rust
1 + 2 // Calls the + function on 1 and 2
```
```f#,rust
(+) 1 2 // Parenthesizing an operator makes it possible to use in a normal function call
```

It is important to note that function application binds harder than any binary operator.

```f#,rust
(+) 0 1 - (+) 2 3 // Equivalent to (0 + 1) - (2 + 3)
```

### Variable bindings

Any language more complex than Hello world is bound to require variable bindings which serve to bind some value to a name
allowing it to be used later.

```f#,rust
let x = 1 + 2 in x // Returns 3
```

You may rightly be wondering about the `in x` part. gluon takes a strong stance against statements in an effort to keep things consistent. Thus only writing `let x = 1 + 2` will be met with a syntax error about a missing `in` keyword which is what defines the actual value returned from the `let` expression.

Let bindings also allow functions to be defined which is done by listing the arguments between the bound identifier and `=`

```f#,rust
// Defines the `id` function which takes a single argument and returns it.
let id x = x in id 1 // Returns 1
```

Mutually recursive values can be defined using `rec ... in` to enclose the `let` bindings.

```f#
rec
let f x = g x
let g x = f x
in f 1 // Never returns
```

This is not limited to functions but works with any value that is capable of recursion (records, variants and functions).

```f#
/// An infinite list of `1`
rec let ones = Cons 1 ones
in

/// A recursive set of records
rec
let value1 =
    let f x = value2.f x + 1
    { f }
let value2 =
    let f x = value1.f x + 2
    { f }
in ()
```

### If expressions

The simplest control flow expression is the `if` expression. It evaluates a boolean expression, taking the first branch if the boolean evaluates to `True`, and taking the second if it evaluates to `False`

```f#,rust
if True then 1 else 0
```

### Record expressions

To create more complex data types, Gluon has first class records. Records can be used to couple data that is logically grouped into a single type.

```f#,rust
{ pi = 3.14, add1 = (+) 1.0 }
```

To access the fields of a record, `.` is used.

```f#,rust
let record = { pi = 3.14, add1 = (+) 1.0 }
in record.pi // Returns 3.14
```

Field assignments can be omitted if there is a variable in scope with the same name as the field.

```f#,rust
let id x = x
in { id }
```

The `..` operator can be used at the end of a record expression to take all fields of one record and fill the constructed record. Explicitly defined fields that also exist in the base record will be in the same order as they are in the base record while all other fields will be prepended in the order that they are written.

```f#, rust
let base_record = { x = 1, y = 2, name = "gluon" }
in
// Results in a record with type
// { field : Bool, x : Int, y : Int, name : String }
{
    field = True,
    ..
    base_record
}
```

### Array expressions

Arrays can be constructed with array literals.

```f#,rust
// Results in an `Array Int`
[1, 2, 3, 4]
```

Since Gluon is statically typed all values must be of the same type. This allows the Gluon interpreter to avoid tagging each value individually which makes types such as `Array Byte` be convertible into Rust's `&[u8]` type without any allocations.

```f#
// ERROR:
// Types do not match:
//        Expected: Int
//        Found: String
[1, ""]
```

Functions to operate on arrays can be found on the `array` module.

```f#
array.len [1, 2, 3]
```

### Variants

While records are great for grouping related data together, there is often a need to have data which can be one of several variants. Unlike records, variants need to be defined before they can be used.

```f#,rust
type MyOption a = | Some a | None
Some 1
```

### Match expressions

To allow variants to be unpacked so their contents can be retrieved, Gluon has the `match` expression.

```f#,rust
match None with
| Some x -> x
| None -> 0
```

Here, we write out a pattern for each of the variant's constructors and the value we pass in (`None` in this case) is matched to each of these patterns. When a matching pattern is found, the expression on the right of `->` is evaluated with each of the constructor's arguments bound to variables.

`match` expressions can also be used to unpack records.

```f#,rust
match { x = 1.0, pi = 3.14 } with
| { x = y, pi } -> y + pi
```

```f#,rust
// Patterns can be nested as well
match { x = Some (Some 123) } with
| { x = Some None } -> 0
| { x = Some (Some x) } -> x
| { x = None } -> -1
```

`let` bindings can also match and unpack on data but only with irrefutable patterns. In other words, only with patterns which cannot fail.

```f#,ignore
// Matching on records will always succeed since they are the only variant
let { x = y, pi } = { x = 1.0, pi = 3.14 }
in y + pi

// These will be rejected however as `let` can only handle one variant (`Some` in this example)
let Some x = None
let Some y = Some 123
x + y
```

### Tuple expressions

Gluon also have tuple expressions for when you don't have sensible names for your fields.

```f#,rust
(1, "", 3.14) // (Int, String, 3.14)
```

Similarily to records they can be unpacked with `match` and `let`.

```f#
match (1, None) with
| (x, Some y) -> x + y
| (x, None) -> x

let (a, b) = (1.0, 2.14)
a + b
```

Infact, tuples are only syntax sugar over records with fields named after numbers (`_0`, `_1`, ...) which makes the above equivalent to the following code.

```f#
match { _0 = 1, _1 = None } with
| { _0 = x, _1 = Some y } -> x + y
| { _0 = x, _1 = None } -> x

let { _0 = a, _1 = b } = { _0 = 1.0, _1 = 2.14 }
a + b
```

While that example is obviously less readable the tuple syntax, the important thing to note is that tuples equivalency with records allows one to access the fields of a tuple directly without unpacking.

```f#,rust
(0, 3.14)._1 // 3.14
```

### Lambda expressions

While we have seen that functions can be defined in let expressions it is often valuable to define a function without giving it an explicit name.

```f#,rust
// \(<identifier)* -> <expr>
\x y -> x + y - 10
```

```f#,rust
// Equivalent to
let f x y = x + y - 10 in f
```

### Type expressions

Gluon allows new types to be defined through the `type` expression which, just like `let`, requires `in <expression>` to be written at the end to ensure it returns a value.

```f#,rust
// type <identifier> <identifier>* = <type> in <expression>
type MyOption a = | None | Some a
let divide x y : Int -> Int -> MyOption Int =
    if (x / y) * y == x then
        Some (x / y)
    else
        None
in divide 10 4
```

An important difference from many languages however is that `type` only defines aliases. This means that all types in the example below are actually equivalent to each other.

```f#,rust
type Type1 = { x: Int }
type Type2 = Type1
type Type3 = { x: Int }
let r1 : Type1 = { x = 0 }
let r2 : Type2 = r1
let r3 : Type3 = r2
in r1
```

Mutually recursive types can be defined by writing a `rec` block.

```f#,rust
rec
type SExpr_ = | Atom String | Cons SExpr SExpr
type SExpr = { location: Int, expr: SExpr_ }
in Atom "name"
```

### Do expressions

`do` expressions are syntax sugar over the commonly used `Monad` type which is used to encapsulate side-effects. By using `do` instead of `>>=` or `flat_map` we can write our code in a sequential manner instead of the closures necessary for sugar free versions. Note `do` still requires a `flat_map` binding to be in scope with the correct type or else you will get an error during typechecking.

```f#
Some 1 >>= (\x -> Some (x + 2))
// or
flat_map (\x -> Some (x + 2)) (Some 1)

// are equivalent to

do x = Some 1
Some (x + 2)

// The binding can also be a (irrefutable) pattern
do { y } = Some { y = "" }
Some y
```

### Sequence expressions

Sequence expressions work just like `do` expressions, only they do not have a binding.

```f#,rust
let io @ { ? } = import! std.io
seq io.print "Hello"
seq io.print " "
io.println "world!"
```

The `seq` keyword can also be omitted.

```f#,rust
let io @ { ? } = import! std.io
io.print "Hello"
io.print " "
io.println "world!"
```

(In the future one of these ways are likely to be deprecated with only one way remaining, the formatter will be able to update the code in any case).

### Indentation

If you have been following along this far, you may be think that the syntax so far is pretty limiting. In particular, you wouldn't be wrong in thinking that the `let` and `type` syntax are clunky due to their need to be closed by the `in` keyword. Luckily, Gluon offers a more convenient way of writing bindings by relying on indentation.

When a token starts on the same column as an unclosed `let` or `type` expression, the lexer implicitly inserts an `in` token which closes the declaration part and makes the following expression into the body.

```f#,rust
let add1 x = x + 1
add1 11 // `in` will be inserted automatically since `add1 11` starts on the same line as the opening `let`
```

If a token starts on the same column as an earlier expression, but there is not an unclosed `type` or `let` expression, Gluon treats the code as a block expression, meaning each expression is run sequentially, returning the value of the last expression.

```f#
do_something1 ()
do_something2 () // `do_something1 ()` is run, then `do_something_2`. The result of `type ...` is the result of the expression
type PrivateType = | Private Int
let x = Private (do_something3 ())
do_something3 ()
match x with
| Private y -> do_something4 x
```

Indented blocks can be used to limit the scope of some variables.

```f#,rust
let module =
    let id x = x
    type MyInt = Int
    { MyInt, id, pi = 3.14 }

module.id module.pi
```
Which is equivalent to:
```f#,rust
let module =
    let id x = x
    in
    type MyInt = Int
    in { MyInt, id, pi = 3.14 }
in
module.id module.pi
```

## Typesystem

In gluon, identifiers starting with an uppercase letter is a type whereas identifiers starting with a lowercase letter are type variables.

### Function types

```
<type> -> <type>
```

Function types are written using the `(->)` operator, which is right associative. This means that the function type `Int -> (Int -> Int)` (A function taking one argument of Int and returning a function of `Int -> Int`) can be written as `Int -> Int -> Int`.

### Record type

```
type_identifier := [A-Z][A-Za-z_0-9]*
variable_identifier := [a-z][A-Za-z_0-9]*

field := <type_identifier> <variable_identifier>* = <type>
       | <type_identifier>
       | <variable_identifier> : <type>

record_type := { (field,)* }

// Example
{
    Float,
    BinaryOp = Float -> Float -> Float,
    pi : Float,
    sin : Float -> Float
}
```

Records are Gluon's main way of creating associating related data and they should look quite familiar if you are familiar with dynamic languages such as javascript. Looks can be deceiving however as gluon's records are more similar to a struct in Rust or C as the order of the fields are significant, `{ x : Int, y : String } != { y : String, x : Int }`. Furthermore, records are immutable, meaning fields cannot be added nor removed and the values within cannot be modified.

In addition to storing values, records also have a secondary function of storing types which is Gluon's way of exporting types. If you have used modules in an ML language, this may look rather familiar. Looks can be deceiving however as 'type fields' must match exactly in gluon which means there is no subtyping relationship between records (`{ Test = { x : Int } }` is not a subtype of `{ Test = Float }`). This may change in the future.

```f#
{ Test = { x : Int } }
```

#### Polymorphic records

Records in gluon can also be polymorphic, that is, just like a function can be polymorphic over it's arguments or return type records can be polymorphic over the fields they contain (see also [Row type][].

```f#
// `f` only requires that the record holds an `x` and `y` field
let f record : { x : Int, y : Int | r } -> Int = record.x + record.y

let z = f { x = 1, y = 2 }
f { x = 1, y = 2, other = "abc" } // The record we pass can hold more fields than the type specifies
```

[Row type]:./syntax-and-semantics.html#row-type

### Variant type

```
( | <identifier> (<type>)* )*

| Err e | Ok t
```

Gluon also has a second way of grouping data which is the enumeration type which allows you to represent a value being one of several variants. In the example above is the representation of Gluon's standard `Result` type. It represents either the value having been successfully computed (`Ok t`) or that an error occurred (`Err e`).

#### Generalized algebraic data type

Variants also have an alternate syntax which allows [Generalized Algebraic Data Type][GADT] (GADT) to be specified.

```
type <identifier> (<identifier>)* = ( | <identifier> :  (<type>)* )*

type Result e t =
    | Err : e -> Result e t
    | Ok : t -> Result e t
```

This encodes the same type as the variant in the previous (with the restriction that the variant must be specified as the top of the type definition).
While this simple example doesn't do anything that a normal variant could not define it is possible to encode much more information about what a variant contains through such as the canonical expression example.

```f#,rust
type Expr a =
    | Int : Int -> Expr Int
    | Bool : Bool -> Expr Bool
    | Add : Expr Int -> Expr Int -> Expr Int
    | If : Expr Bool -> Expr a -> Expr a -> Expr a

let eval e : Expr a -> a =
    match e with
    | Int x -> x
    | Bool x -> x
    | Add l r -> eval l + eval r
    | If p t f -> if eval p then eval t else eval f

let int : Int = eval (If (Bool True) (Add (Int 1) (Int 2)) (Int 0))
let bool : Bool = eval (Bool True)
()
```

Through specifying a more specific type in the return type of a GADT variant we enforce that the variant can only contain that specific type
in the argument. We can then exploit it when matching to refine the argument.

[GADT]:https://en.wikipedia.org/wiki/Generalized_algebraic_data_type

### Alias type

```
<identifier> (<type>)*
Int
Float
Option Int
Ref String
```

The last kind of type which Gluon has is the alias type. An alias type explicitly names some underlying type which can either be one of the three types mentioned above or an abstract type which is the case for the `Int`, `String` and `Ref` types. If the underlying type is abstract, then the type is only considered equivalent to itself (ie if you define an abstract type of `MyInt` which happens to have the same representation as `Int` the typechecker will consider these two types as being distinct).


### Higher-kinded types

Higher-kinded types are a fairly abstract concept in Gluon and you may create entire programs without any knowledge about them. Sometimes they are a very valuable tool to have, as they can be used to create very powerful abstractions.

Just as all values such as `0 : Int`, `"Hello World!" : String` and `Some 4.0 : Option Float` each have a type, these types themselves have their own 'type' or the 'kind' as it is called. For the types of concrete values the `Kind` is always `Type` so for the earlier examples `Int : Type`, `String : Type` and `Option Float : Type`. That is not very useful on its own but it becomes more interesting when we consider the kind of `Option : Type -> Type`. `Type -> Type` looks rather like the type of a function such as `show_int : Int -> String` but, instead of taking a value, it takes a type and produces a new type. In effect, this lets us abstract over types instead of just over values. This abstraction facility can be seen in the `Functor : (Type -> Type) -> Type` type which takes a type with kind `Type -> Type` as argument which is exactly the kind of `Option` (or `List`, `Result a`).

### Row type

A `Row` is defined as a set of `(identifier, Type)` pairs and are used to describe the contents of records, variants and effects. A `Row` type has it's own special `Row` kind (instead of the normal `Type`) and has special treatment during typechecking if it is marked as extensible. If two extensible rows are unified (checking if they are equivalent) then they do not need to exactly match, but if one of the rows has more fields than the other (or vice-versa) then the other record is simply constrained to also have those fields.


```f#
// Unifying
{ x : Int | r } <=>  { y : String | s }
// Results in
{ x : Int, y : String | t }
// The same goes for effects and variants
```

Rows are currently a bit of an implementation detail and are thus only indirectly exposed to users through records, variants and effects. (In the future direct manipulation and definitions of rows may be added).

### Universal quantification

*First draft*

Universal quantification is what Gluon's "generic types" are called. Consider the identity function in Rust.

```rust,ignore
fn id<T>(x: T) -> T {
    x
}
```

In Gluon the same function would be written in the following way if it were fully annotated.

```f#
let id x : forall a . a -> a = x
```

```f#
// Types can of course be omitted in which the same type as above will be inferred
let id x = x
// Unbound type variables (`a` in this example) are allowed, in which case a `forall` will be
// inserted at the at the "top" of the type (same place as the type above)
let id x : a -> a = x
```

So in simple case, `forall` is no different from declaring type parameters to a function in Rust. But `forall` also serves more advanced use cases and is at the center when it comes to making Gluon's records work as modules.

```f#
let module =
    let id x = x

    { id }

module.id 0
module.id ""
```

If we were to emulate the above code in Rust we would probably end up with something like this code.

```rust,ignore
struct Module<T> {
    id : Box<Fn(T) -> T>,
}

let module = Module {
    id: Box::new(|x| x),
};
(module.id)(0);
(module.id)("");
```

Alas, this does not work in Rust since `module` will be inferred to the type `Module<i32>` which makes the second call to `id` a type error. In gluon it works as the type of `module` is actually `{ id : forall a . a -> a }` and not `forall a . { id : a -> a }` which is the closest analogue to the Rust example.

Intuitively, we can say that since gluon lets `forall` be specified inside types we can avoid specializing the type (in this case `forall a . a -> a`) which lets us specialize `module.id` once for each call to `id` instead of specializing the entire module at once.

While all of this looks quite complex, it should for the most part not matter when writing code and common idioms will just work as expected!

### Implicit arguments

Sometimes, there is a need to overload a name with multiple differing implementations and let the compiler chose the correct implementation. If you have written any amount of Gluon code so far, you are likely to have already encountered this with numeric operators such as `(+)` or comparison operators such as `(==)`. If you inspect the types of these functions you will find that the first argument of these functions look a little bit different from normal functions.

```gluon
(==): : forall a . [std.prelude.Eq a] -> a -> a -> std.types.Bool
(+): forall a . [std.prelude.Num a] -> a -> a -> a
```

This different looking argument is an implicit argument which means that you do not need to pass a value for this argument, instead, the compiler will try to find a value with a type that matches the type signature. So if you were to call `1 == 2` the compiler will see that the type variable `a` has been unified to `Int`. Then when the implicit argument is resolved it will look for a value with the type `Eq Int`.

Since searching all possible bindings currently in scope would introduce to many ambiguity errors the compiler does not search all bindings when trying to determine an implicit argument. Instead, whether a binding is considered for implicit resolution is controlled by the `#[implicit]` attribute. When marking a `let` binding as `#[implicit]` and this binding is in scope it will be considered as a candidate for all implicit arguments. The `#[implicit]` attribute can also be set on a `type` binding in which case it applied to all `let` bindings which has the type declared by the `type` binding.

```f#,rust
#[implicit]
type Test = | Test ()
let f y: [a] -> a -> a = y
let i = Test ()
// `i` gets selected as the implicit argument since `#[implicit]` is marked on the type and `i : Test`
()
```

Since importing each individual binding used as an implicit argument quickly becomes tedious there is a short-hand to bring all implicit bindings from a record into scope.

```f#,ignore
let { eq, ord } = import! std.int
1 == 1 && 1 < 2
```

```f#,ignore
// Also brings in `show`, `num` ...
let { ? } = import! std.int
1 == 1 && 1 < 2
```

For standard types such as `Int`, `Float`, `String`, `Bool` and `Option` this gets injected through the implicit prelude that is inserted before all code which lets `==`, `<` etc to work out of the box.

#### Passing implicit arguments explicitly

If you only use implicit functions as explained above then it might just seem like a different name for traits (Rust) or type classes (Haskell). While it is true that the main reason for implicit arguments is to emulate traits/type classes implicit arguments is more powerful than those approaches as it is also possible to override the implicit resolution and instead give the argument explicitly by prefixing the argument with `?`.

```f#,rust
let list @ { List } = import! std.list
// Make a custom equality function which returns true regardless of the elements of the list
#[infix(left, 4)]
let (===) = (list.eq ?{ (==) = \x y -> True }).(==)
Cons 1 (Cons 2 Nil) === Cons 3 (Cons 4 Nil)
```

The inverse also works when defining a function with implicit arguments. By prefixing an argument by `?` an implicit arguments will be given a name inside the function (if `?` is not given in a function definition the argument will only be available for implicit resolution).

```f#,rust
let eq ?a : [Eq a] -> Eq (Option a) = {
    (==) = \l r ->
        match (l, r) with
        | (Some l_val, Some r_val) -> a.(==) l_val r_val
        | (None, None) -> True
        | _ -> False,
}
()
```


## Importing modules

As is often the case, it is convenient to separate code into multiple files which can later be imported and used from multiple other files. To do this, we can use the `import!` macro which takes a single string literal as argument and loads and compiles that file at compile time before the importing module is compiled.

For example, say that we need the `assert` function from the `test` module which can be found at `std/test.glu`. We might write something like this:

```f#,rust
let { assert } = import! std.test
assert (1 == 1)
```

## Writing modules

Importing standard modules is all well and good but it is also necessary to write your own once a program starts getting too big for a single file. As it turns out, if you have been following along so far, you already know everything about writing a module! Creating and loading a module in gluon entails creating a file containing an expression which is then loaded and evaluated using `import!`. `import!` is then just the value of the evaluated expression.

```f#
// module.glu
type Named a = { name: String, value: a }
let twice f x = f (f x)
{ twice, Named }

//main.glu
let { twice, Named }  = import! "module.glu"
let addTwice = twice (\x -> x + 1)
let namedFloat : Named Float = { name = "pi", value = 3.14 }
addTwice 10
```

Though modules are most commonly a record, this does not have to be the case. If you wanted, you could write a module returning any other value as well.

```f#
// pi.glu
3.14

//main.glu
let pi  = import! "pi.glu"
2 * pi * 10
```
