cargo test -p base --features test &&
    cargo test -p parser --features test &&
    cargo test -p check --features test &&
    cargo test -p vm --features test &&
    cargo test --features test &&
    (cd vm && cargo test --no-default-features)
