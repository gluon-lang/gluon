#!/bin/bash

set -ex

if [[ $1 == *"apple"* ]]; then
    TARGET=$1
else
    TARGET='x86_64-unknown-linux-musl'
fi

VERSION="0.2.10"
SCCACHE_VERSION="sccache-${VERSION}-${TARGET}"
curl -L "https://github.com/mozilla/sccache/releases/download/${VERSION}/$SCCACHE_VERSION.tar.gz" | tar -xvz
mv $SCCACHE_VERSION/sccache .
chmod +x ./sccache
mv ./sccache $HOME/bin/ 
