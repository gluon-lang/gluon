#!/bin/bash

# Usage: sync_publish /path/to/crate -f
#
# Publish a crate and wait for it to become available.
#
# https://gist.github.com/Riateche/a1c500fe760a2b9190beb0a7134db82d

set -e
set -o pipefail

TMP_DIR=/tmp/test1

DIR="$1"
FORCE="$2"
shift
shift

NAME=$(grep '^name' "$DIR/Cargo.toml" | head -n 1 | sed 's/name = "\([^"]*\)"/\1/')
cd "$DIR"

VERSION=$(cargo metadata --format-version 1 2>/dev/null | jq -r '.packages[] | select(.name=="'$NAME'").version')

rm -rf "$TMP_DIR"
cargo new "$TMP_DIR" > /dev/null 2>&1
cd "$TMP_DIR"
if cargo add "$NAME@$VERSION" > /dev/null 2>&1; then
    echo "$NAME=$VERSION already exists, skipping."
    exit 0
fi

echo "Publishing $NAME=$VERSION"
if [ "$FORCE" != "-f" ]; then
    echo "This is a dry run. Run with -f to publish."
    exit 0
fi

cd "$DIR"
cargo publish $@

cd "$TMP_DIR"
while ! cargo add "$NAME@$VERSION" > /dev/null 2>&1; do
    echo "Waiting for crate to be published..."
    sleep 1
done
