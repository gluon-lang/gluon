#!/bin/bash
set -ex

declare -a PROJECTS=(
    codegen
    base
    codegen
    parser
    check
    completion
    vm
    .
    format
    c-api
    doc
    repl
)

for PROJECT in "${PROJECTS[@]}"
do
    (cd $PROJECT && cargo check && cargo publish $@)
done
