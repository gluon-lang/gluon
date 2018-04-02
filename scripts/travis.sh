#!/bin/bash
set -ex

export RUST_BACKTRACE=1

cargo test --features "test test_skeptic" --all "$@"
echo "" | cargo run --features "test" --example 24
cargo check --benches --features test "$@"
cargo check --all --no-default-features "$@"

echo "TRAVIS_RUST_VERSION=$TRAVIS_RUST_VERSION"
[ "$TRAVIS_RUST_VERSION" != "nightly" ] || cargo test --features "test nightly" -p gluon compile_test "$@"
