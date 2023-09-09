set -ex

main() {
    local target=x86_64-unknown-linux-musl
    # https://github.com/cross-rs/cross/releases/download/v0.2.5/cross-x86_64-unknown-linux-musl.tar.gz
    # This fetches latest stable release
    local tag=$(git ls-remote --tags --refs --exit-code https://github.com/cross-rs/cross \
                       | cut -d/ -f3 \
                       | grep -E '^v[0.1.0-9.]+$' \
                       | sort --version-sort \
                       | tail -n1)
    sh ./scripts/install.sh -- \
        --force \
        --git cross-rs/cross \
        --tag $tag \
        --target $target
}

main
