#!/bin/sh
RUST_BACKTRACE=1 cargo test --features test --all &&
  travis-cargo --only nightly test -- --features "test nightly" -p gluon compile_test &&
  travis-cargo --only nightly bench &&
  travis-cargo --only stable build -- --all --no-default-features
