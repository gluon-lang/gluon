set -ex

main() {
    # clean cargo of any stored artifacts
    cargo clean
    # At this point cargo should be installed
    cargo install cross
}

main
