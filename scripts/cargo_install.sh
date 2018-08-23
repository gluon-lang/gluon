#!/bin/bash
#
# This script runs on travis to prep the CI as needed.

if [ -z "$1" ] || [ -z "$2" ]
then
    echo "Expected a package name and its version"
    exit 1
fi


PACKAGE=$1
VERSION=$2

if command -v $PACKAGE >/dev/null 2>&1; then
    echo "$PACKAGE already installed at $(command -v $PACKAGE)"
else
    echo "installing $PACKAGE"
    cargo install $PACKAGE --vers $VERSION
fi
