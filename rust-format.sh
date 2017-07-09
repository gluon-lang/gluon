for d in $(find . -name "Cargo.toml" -printf '%h\n')
do
    (cd $d; cargo fmt)
    status=$?
    if [ $status -ne 0 ] && [ $status -ne 101  ]; then # 101 is due to a bug in rustfmt that the ./vm package is triggering
        exit $status;
    fi
done