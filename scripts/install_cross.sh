set -ex

main() {
    # Sample link
    # https://github.com/cross-rs/cross/releases/download/v0.2.5/cross-x86_64-unknown-linux-musl.tar.gz

    VERSION="v0.2.5"

    CROSS_VERSION='cross-x86_64-unknown-linux-musl'

    pushd ${WORK_DIR}

    curl -L "https://github.com/cross-rs/cross/releases/download/${VERSION}/$CROSS_VERSION.tar.gz" | tar -xvz
    mv $CROSS_VERSION/cross .
    mv $CROSS_VERSION/cross-util .
    
    # it is sccache-dist on linux and sccache on mac
    chmod +x ./cross
    mv ./cross $HOME/bin/
    chmod +x ./cross-util
    mv ./cross-util $HOME/bin/
}

main
