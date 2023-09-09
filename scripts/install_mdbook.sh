#!/bin/bash

set -ex

#Getting issue error: unrecognized subcommand '/home/travis/.rustup/toolchains/nightly-2023-09-05-x86_64-unknown-linux-gnu/bin/rustc'
ls /home/travis/.rustup/toolchains/nightly-2023-09-05-x86_64-unknown-linux-gnu/bin/*
/home/travis/.rustup/toolchains/nightly-2023-09-05-x86_64-unknown-linux-gnu/bin/rustc --version

if [[ $1 == *"apple"* ]]; then
    exit 0
else
    TARGET='x86_64-unknown-linux-musl'
fi

MDBOOK_VERSION="mdbook-v0.2.1-${TARGET}"
curl -L "https://github.com/rust-lang-nursery/mdBook/releases/download/v0.2.1/$MDBOOK_VERSION.tar.gz" | tar -xvz
chmod +x ./mdbook
mv ./mdbook $HOME/bin/ 
