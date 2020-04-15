#!/bin/bash

VERSION=$(echo $1 | sed 's/v//')
shift

declare -a PROJECTS=(
    gluon
    gluon_c-api
    gluon_doc
    gluon_repl
)

for PROJECT in "${PROJECTS[@]}"
do
    PROJECT_PATH=$(echo "$PROJECT" | sed 's/gluon_//' | sed 's/gluon/./')
    echo $PROJECT_PATH
    (cd "${PROJECT_PATH}" && cargo publish "$@")
    if [[ $? ]]; then
        exit 1
    fi
    echo "Waiting for ${PROJECT} to publish"
    N=0
    while ! cargo search "${PROJECT}" | head -1 | grep "${VERSION}"; do
        printf '.'
        sleep 3
        N=$((N+1))
        if [[ $N -gt 10 ]]; then
            echo "${PROJECT} did not get published!"
            exit 1
        fi
    done
done
