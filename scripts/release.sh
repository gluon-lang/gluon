#!/bin/bash
set -ex

LEVEL=$1
VERSION=$2
if [ -z "$LEVEL" ]; then
    echo "Expected patch, minor or major"
    exit 1
fi

clog --$LEVEL
if [[ -z $(head -1 CHANGELOG.md | grep $VERSION) ]]; then
    git checkout CHANGELOG.md
    echo "Wrong version specified"
    exit 1
fi

git add CHANGELOG.md

./scripts/version.sh $VERSION
