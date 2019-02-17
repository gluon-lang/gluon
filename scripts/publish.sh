#!/bin/bash
set -ex

declare -a PROJECTS=(
    codegen
    base
    parser
    check
    completion
    vm
    format
    .
    c-api
    doc
    repl
)

for PROJECT in "${PROJECTS[@]}"
do
    (cd $PROJECT && cargo publish $@)
done
