#!/bin/bash
set -ex

export RUST_BACKTRACE=1

# Split the tests into two on travis so to avoid timing out

if [ -z $NO_NORMAL_TEST ]; then
    cargo test --features "test" --all --examples "$@"
    cargo test --features "test" --benches "$@" -- --test
    echo "" | cargo run --features "test" --example 24
    cargo run --features "test" --example marshalling

    echo "TRAVIS_RUST_VERSION=$TRAVIS_RUST_VERSION"
    (echo $TRAVIS_RUST_VERSION | grep nightly) && cargo test --features "test nightly" -p gluon --test compiletest "$@"

    cargo check --all --no-default-features "$@"
fi
