extern crate gluon;

use gluon::{new_vm, Compiler};
use gluon::check::metadata::metadata;
use gluon::doc;

#[test]
fn basic() {
    let vm = new_vm();
    let module = r#"
/// This is the test function
let test x = x
{ test }
"#;
    let (expr, typ) = Compiler::new()
        .typecheck_str(&vm, "basic", module, None)
        .unwrap();
    let (meta, _) = metadata(&*vm.get_env(), &expr);

    let mut out = String::new();
    doc::generate(&mut out, &typ, &meta).unwrap();
    assert_eq!(
        out,
        r#"## test
```gluon
forall a . a -> a
```
This is the test function
"#
    );
}
