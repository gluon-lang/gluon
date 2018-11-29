extern crate env_logger;

extern crate gluon;

#[macro_use]
mod support;

test_expr! { array,
r#"
let array = import! std.array.prim
let arr = [1,2,3]

array.index arr 0 #Int== 1
    && array.len arr #Int== 3
    && array.len (array.append arr arr) #Int== array.len arr #Int* 2"#,
true
}

test_expr! { array_byte,
r#"
let array = import! std.array.prim
let arr = [1b,2b,3b]

let b = array.index arr 2 #Byte== 3b && array.len arr #Int== 3
let arr2 = array.append arr arr
b && array.len arr2 #Int== array.len arr #Int* 2
  && array.index arr2 1 #Byte== array.index arr2 4
"#,
true
}

test_expr! { array_float,
r#"
let array = import! std.array.prim
let arr = [1.0,2.0,3.0]

let b = array.index arr 2 #Float== 3.0 && array.len arr #Int== 3
let arr2 = array.append arr arr
b && array.len arr2 #Int== array.len arr #Int* 2
  && array.index arr2 1 #Float== array.index arr2 4
"#,
true
}

test_expr! { array_data,
r#"
let array = import! std.array.prim
let arr = [{x = 1, y = "a" }, { x = 2, y = "b" }]

let b = (array.index arr 1).x #Int== 2 && array.len arr #Int== 2
let arr2 = array.append arr arr
b && array.len arr2 #Int== array.len arr #Int* 2
"#,
true
}

test_expr! { array_array,
r#"
let array = import! std.array.prim
let arr = [[], [1], [2, 3]]

let b = array.len (array.index arr 1) #Int== 1 && array.len arr #Int== 3
let arr2 = array.append arr arr
b && array.len arr2 #Int== array.len arr #Int* 2
"#,
true
}

// Test that empty variants are handled correctly in arrays
test_expr! { array_empty_variant,
r#"
let array = import! std.array.prim
type Test = | Empty | Some Int
let arr = [Empty, Some 1]
match array.index arr 0 with
| Empty -> 0
| Some x -> x
"#,
0i32
}

// Test that array append handles array types correctly
test_expr! { array_empty_append,
r#"
let array = import! std.array.prim
type Test = | Empty | Some Int
let arr = array.append [] [Empty, Some 1]
match array.index arr 0 with
| Empty -> 0
| Some x -> x
"#,
0i32
}

test_expr! { array_load,
r#"
let array = import! std.array
0
"#,
0i32
}

test_expr! { array_fold,
r#"
let array = import! std.array
array.foldable.foldl (\x y -> y.x) 0 [{ x = 4 }]
"#,
4
}
