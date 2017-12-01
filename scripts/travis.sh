#!/bin/bash

(
  export TRAVIS_CARGO_NIGHTLY_FEATURE="nightly";
  export RUST_BACKTRACE=1;
  cargo test --features test --all &&
  cargo check --benches --features test &&
  travis-cargo --only nightly test -- --features "test nightly" -p gluon compile_test &&
  travis-cargo --only stable build -- --all --no-default-features
)
