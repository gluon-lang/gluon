#!/bin/bash

set -ex


if [[ $1 == *"apple"* ]]; then
    exit 0
else
    TARGET='x86_64-unknown-linux-musl'
fi

MDBOOK_VERSION="v0.5.4"
curl -L "https://github.com/rust-lang/mdBook/releases/download/${MDBOOK_VERSION}/mdbook-${MDBOOK_VERSION}-${TARGET}.tar.gz" | tar -xvz
chmod +x ./mdbook
mv ./mdbook $HOME/bin/
