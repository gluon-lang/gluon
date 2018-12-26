#!/bin/bash
set -ex

export RUST_BACKTRACE=1

du -sh $HOME/*
du -sh $HOME/.cargo/*

# Split the tests into two on travis so to avoid timing out

if [ -z $NO_NORMAL_TEST ]; then
    cargo test --features "test" --all "$@"
    cargo test --features "test" --examples
    echo "" | cargo run --features "test" --example 24
    cargo run --features "test" --example marshalling

    echo "TRAVIS_RUST_VERSION=$TRAVIS_RUST_VERSION"
    (echo $TRAVIS_RUST_VERSION | grep nightly) && cargo test --features "test nightly" -p gluon --test compiletest "$@"
fi

if [ ! -z $BENCH_DEFAULT_FEATURES_CHECK ] || [ -z CI ]; then
    cargo bench --benches --features test "$@"
    cargo check --all --no-default-features "$@"
fi
