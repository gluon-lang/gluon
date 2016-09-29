(cd c-api &&
    cargo test -p gluon_base &&
    cargo test -p gluon_parser --features test &&
    cargo test -p gluon_check --features test &&
    cargo test -p gluon_vm --features test &&
    cargo test -p gluon --features "test skeptic" &&
    cargo test --features "test skeptic")
