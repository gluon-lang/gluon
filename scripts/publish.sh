#!/bin/bash
set -ex

declare -a PROJECTS=(
    repl
)

for PROJECT in "${PROJECTS[@]}"
do
    (cd $PROJECT && cargo check && cargo publish $@)
done
