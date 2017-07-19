#!/bin/bash

(
  export TRAVIS_CARGO_NIGHTLY_FEATURE="nightly";
  export RUST_BACKTRACE=1;
  cargo test --features test --package gluon_base &&
  cargo test --features test --package gluon_parser &&
  cargo test --features test --package gluon_check &&
  cargo test --features test --package gluon_vm &&
  cargo test --features test --package gluon &&
  cargo test --features test --package gluon_repl &&
  cargo test --features test --package gluon_c-api &&
  travis-cargo --only nightly test -- --features "test nightly" -p gluon compile_test &&
  cargo check --bench check --features test &&
  cargo check --bench function_call --features test &&
  cargo check --bench parser --features test &&
  cargo check --bench precompiled --features test &&
  travis-cargo --only stable build -- --all --no-default-features
)
