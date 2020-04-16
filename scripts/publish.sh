#!/bin/bash

VERSION=$(echo $1 | sed 's/v//')
shift

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

for PROJECT in "${PROJECTS[@]}"
do
    PROJECT_PATH=$(echo "$PROJECT" | sed 's/gluon_//' | sed 's/gluon/./')

    if ! (cd "${PROJECT_PATH}" && cargo publish "$@"); then
        exit 1
    fi
    echo "Waiting for ${PROJECT} to publish"
    sleep 15
done
