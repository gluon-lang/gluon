#!/bin/bash

set -ex

# https://stackoverflow.com/a/34676160/2489366
# the directory of the script
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

# the temp directory used, within $DIR
# omit the -p parameter to create a temporal directory in the default location
WORK_DIR=`mktemp -d "$DIR.XXXXXXXX"`

# check if tmp dir was created
if [[ ! "$WORK_DIR" || ! -d "$WORK_DIR" ]]; then
  echo "Could not create temp dir"
  exit 1
fi

# deletes the temp directory
function cleanup {
  rm -rf "$WORK_DIR"
  echo "Deleted temp working directory $WORK_DIR"
}

# register the cleanup function to be called on the EXIT signal
trap cleanup EXIT

# Sample links
# https://github.com/mozilla/sccache/releases/download/v0.5.4/sccache-dist-v0.5.4-x86_64-unknown-linux-musl.tar.gz
# https://github.com/mozilla/sccache/releases/download/v0.5.4/sccache-v0.5.4-aarch64-apple-darwin.tar.gz

VERSION="v0.5.4"

if [[ $1 == *"apple"* ]]; then
    TARGET=$1
    SCCACHE_VERSION="sccache-${VERSION}-aarch64-${TARGET}-darwin"
else
    TARGET='x86_64-unknown-linux-musl'
    SCCACHE_VERSION="sccache-dist-${VERSION}-${TARGET}"
fi

pushd ${WORK_DIR}

curl -L "https://github.com/mozilla/sccache/releases/download/${VERSION}/$SCCACHE_VERSION.tar.gz" | tar -xvz
mv $SCCACHE_VERSION/sccache* ./sccache
# it is sccache-dist on linux and sccache on mac
chmod +x ./sccache
mv ./sccache $HOME/bin/

popd
