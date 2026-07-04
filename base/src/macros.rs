#[macro_export]
macro_rules! ice {
    () => ({
        panic!("ICE: Please report an issue at https://github.com/gluon-lang/gluon/issues")
    });
    ($msg:expr_2021) => ({
        panic!(concat!($msg, ". Please report an issue at https://github.com/gluon-lang/gluon/issues"))
    });
    ($fmt:expr_2021, $($arg:tt)+) => ({
        panic!(concat!($fmt, ". Please report an issue at https://github.com/gluon-lang/gluon/issues"), $($arg)+)
    });
}
