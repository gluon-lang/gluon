set -ex

main() {
    # This is necessary as shown in https://github.com/rust-lang/rust/issues/61925
    export RUSTC_WRAPPER=sccache
    # Check sscache version
    ls -a /home/travis/.rustup/toolchains/*
    sccache --version
    # At this point cargo should be installed
    cargo install cross
}

main
