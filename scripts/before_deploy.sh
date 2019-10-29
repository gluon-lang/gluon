# This script takes care of building your crate and packaging it for release

set -ex

main() {
    local src=$(pwd) \
          stage=

    case $TRAVIS_OS_NAME in
        linux)
            stage=$(mktemp -d)
            ;;
        osx)
            stage=$(mktemp -d -t tmp)
            ;;
    esac

    test -f Cargo.lock || cargo generate-lockfile

    cross build -p gluon_repl --target $TARGET --release

    # Copy the files that are needed in the distribution
    if [ -f target/$TARGET/release/gluon ]; then
        cp target/$TARGET/release/gluon $stage/
    elif [ -f target/$TARGET/release/gluon.exe ]; then
        cp target/$TARGET/release/gluon.exe $stage/
    else
        echo "Could not find gluon executable"
        exit 1
    fi
    mkdir $stage/std
    cp -r std/* $stage/std/

    cd $stage
    tar czf $src/$CRATE_NAME-$TRAVIS_TAG-$TARGET.tar.gz *
    cd $src

    rm -rf $stage

    mv $src/$CRATE_NAME-$TRAVIS_TAG-$TARGET.tar.gz target/
}

main
