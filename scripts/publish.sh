#!/bin/bash

VERSION=$(echo $1 | sed 's/v//')
shift

function retry {
    for i in {0..10}; do
        $@
        if [ $? -eq 0 ]; then
            exit 0
        fi
        sleep 3
    done
    exit 1
}


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

    if ! (sync_publish "${PROJECT_PATH}" -f "$@"); then
        exit 1
    fi
done
