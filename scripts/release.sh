#!/bin/sh

(cd base && cargo publish $@) &&
    (cd parser && cargo publish $@) &&
    (cd check && cargo publish $@) &&
    (cd vm && cargo publish $@) &&
    (cd format && cargo publish $@) &&
    cargo publish $@ &&
    (cd c-api && cargo publish $@) &&
    (cd repl && cargo publish $@)
