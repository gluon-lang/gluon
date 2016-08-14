cargo test -p gluon_base --features test &&
    cargo test -p gluon_parser --features test &&
    cargo test -p gluon_check --features test &&
    cargo test -p gluon_vm --features test &&
    cargo test --features "test nightly" &&
    (cd c-api && cargo test --features test)
