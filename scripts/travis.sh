#!/bin/sh

(
  export TRAVIS_CARGO_NIGHTLY_FEATURE="nightly";
  export RUST_BACKTRACE=1;
  cargo test --features test --all &&
  travis-cargo --only nightly test -- --features "test nightly" -p gluon compile_test &&
  cargo check --benches --features test &&
  travis-cargo --only stable build -- --all --no-default-features
)
