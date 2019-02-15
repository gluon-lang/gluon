#!/bin/bash

set -ex

if [[ $1 == *"apple"* ]]; then
    exit 0
else
    TARGET='x86_64-unknown-linux-musl'
fi

MDBOOK_VERSION="mdbook-v0.2.1-${TARGET}"
curl -L "https://github.com/rust-lang-nursery/mdBook/releases/download/v0.2.1/$MDBOOK_VERSION.tar.gz" | tar -xvz
chmod +x ./mdbook
mv ./mdbook $HOME/bin/ 
