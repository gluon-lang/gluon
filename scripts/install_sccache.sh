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


if [[ $1 == *"apple"* ]]; then
    TARGET=$1
else
    TARGET='x86_64-unknown-linux-musl'
fi

VERSION="0.2.10"
SCCACHE_VERSION="sccache-${VERSION}-${TARGET}"
pushd ${WORK_DIR}

curl -L "https://github.com/mozilla/sccache/releases/download/${VERSION}/$SCCACHE_VERSION.tar.gz" | tar -xvz
mv $SCCACHE_VERSION/sccache .
chmod +x ./sccache
mv ./sccache $HOME/bin/

popd
