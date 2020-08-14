#!/bin/bash
set -ex

export RUST_BACKTRACE=1

# Split the tests into two on travis so to avoid timing out

declare -a PROJECTS=(
    gluon_codegen
    gluon_base
    gluon_parser
    gluon_check
    gluon_completion
    gluon_vm
    gluon_format
    gluon
    gluon_c-api
    gluon_doc
    gluon_repl
)

if [ -z $NO_NORMAL_TEST ]; then
    cargo test --features "test" --all "$@"
    cargo test --features "test" --all --bins "$@"
    cargo test --features "test" --all --examples "$@"
    cargo test --features "test" --all --benches "$@"
    cargo test --features "test" -p gluon_parser --benches "$@"
    echo "" | cargo run --features "test" --example 24
    cargo run --features "test" --example marshalling

    echo "TRAVIS_RUST_VERSION=$TRAVIS_RUST_VERSION"
    (echo $TRAVIS_RUST_VERSION | grep nightly) && cargo test --features "test nightly" -p gluon --test compiletest "$@"

    # Check each crate individually so that features from one do not affect another which would break publish
    for PROJECT in "${PROJECTS[@]}"
    do
        cargo check --package "${PROJECT}" --no-default-features "$@"
    done
fi
