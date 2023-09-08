set -ex

main() {
    # clean tmp of any stored artifacts
    rm -r /tmp/*
    # clean cargo of any stored artifacts
    cargo clean
    # At this point cargo should be installed
    cargo install cross
}

main
