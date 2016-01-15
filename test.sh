cargo test -p base &&
    cargo test -p parser &&
    cargo test -p check --features test &&
    cargo test -p vm &&
    cargo test &&
    (cd vm && cargo test --no-default-features)
