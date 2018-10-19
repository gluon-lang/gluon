#!/bin/sh
set -ex

declare -a PROJECTS=(
    base
    parser
    check
    completion
    codegen
    vm
    .
    format
    c-api
    doc
    repl
)

for PROJECT in "${PROJECTS[@]}"
do
    (cd $PROJECT && cargo publish $@)
done
