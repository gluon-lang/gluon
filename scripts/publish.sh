#!/bin/bash
set -ex

declare -a PROJECTS=(
    base
    codegen
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
    sleep 4
    (cd $PROJECT && cargo publish $@)
done
