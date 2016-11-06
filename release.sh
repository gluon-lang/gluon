(cd base && cargo publish $@) &&
    (cd parser && cargo publish $@) &&
    (cd check && cargo publish $@) &&
    (cd vm && cargo publish $@) &&
    cargo publish
    (cd c-api && cargo publish $@)
