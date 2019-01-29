#!/bin/bash

set -ex

MDBOOK_VERSION='mdbook-v0.2.1-x86_64-unknown-linux-musl'
curl -L "https://github.com/rust-lang-nursery/mdBook/releases/download/v0.2.1/$MDBOOK_VERSION.tar.gz" | tar -xvz
chmod +x ./mdbook
mv ./mdbook $HOME/bin/ 
