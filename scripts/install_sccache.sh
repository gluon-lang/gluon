#!/bin/bash

set -ex

if [[ $1 == *"apple"* ]]; then
    TARGET=$1
else
    TARGET='x86_64-unknown-linux-musl'
fi

SCCACHE_VERSION="sccache-0.2.8-${TARGET}"
curl -L "https://github.com/mozilla/sccache/releases/download/0.2.8/$SCCACHE_VERSION.tar.gz" | tar -xvz
mv $SCCACHE_VERSION/sccache .
chmod +x ./sccache
mv ./sccache $HOME/bin/ 
