#!/bin/sh
set -ex

PROJECTS=(
    base
    parser
    check
    completion
    vm
    format
    codegen
    .
    c-api
    repl
)

for PROJECT in "$PROJECTS"
do
    (cd $PROJECT && cargo publish $@)
done
