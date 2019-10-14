use gluon::{new_vm, vm::api::FunctionRef, ThreadExt};

fn fib(n: u64) -> u64 {
    if n <= 1 {
        1
    } else {
        fib(n - 1) + fib(n - 2)
    }
}

fn main() {
    const N: u64 = 46;
    if std::env::args().nth(1).as_ref().map(|s| &s[..]) == Some("rust") {
        println!("{}", fib(N));
    } else {
        let vm = new_vm();
        let text = r#"
            let fib n =
                if n #Int< 2
                then 1
                else fib (n #Int- 1) #Int+ fib (n #Int- 2)
            fib
            "#;
        vm.load_script("fib", text)
            .unwrap_or_else(|err| panic!("{}", err));
        let mut fib: FunctionRef<fn(u64) -> u64> =
            vm.get_global("fib").unwrap_or_else(|err| panic!("{}", err));
        let result = fib.call(N).unwrap_or_else(|err| panic!("{}", err));
        println!("{}", result);
    }
}
