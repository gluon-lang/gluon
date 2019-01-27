#!/bin/bash

set -ex

SCCACHE_VERSION='sccache-0.2.8-x86_64-unknown-linux-musl'
curl -L "https://github.com/mozilla/sccache/releases/download/0.2.8/$SCCACHE_VERSION.tar.gz" | tar -xvz
mv $SCCACHE_VERSION/sccache .
chmod +x ./sccache
mv ./sccache $HOME/bin/ 
