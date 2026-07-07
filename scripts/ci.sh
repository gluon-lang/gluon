#!/bin/bash
set -ex

export RUST_BACKTRACE=1

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
    cargo test --all-features --all --all-targets "$@"
    cargo test --all-features --all --doc "$@"
    echo "" | cargo run --features "test" --example 24
    cargo run --features "test" --example marshalling

    echo "RUST_VERSION=$RUST_VERSION"
    (echo $RUST_VERSION | grep nightly) && cargo test --features "test nightly" -p gluon --test compiletest "$@"

    # Check each crate individually so that features from one do not affect another which would break publish
    for PROJECT in "${PROJECTS[@]}"
    do
        cargo check --package "${PROJECT}" --no-default-features "$@"
    done
fi
