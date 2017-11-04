# Contributing to Gluon

## Filing bug reports

It does not matter if you found a soundness issue in typechecker or found the documentation confusing. Either way filing an issue to the [issue tracker][] is extremely helpful.

[issue tracker]:https://github.com/gluon-lang/gluon/issues

## Finding something to work on

A good place to start is to look at the issues marked as [beginner][]. These are issues that should be possible to work on without knowledge on the inner workings of Gluon.

If you find something that looks interesting, please leave a comment on the issue. That way, you can get assistance quicker and there is no risk of duplicating work.

[beginner]:https://github.com/gluon-lang/gluon/labels/Beginner

## Building

Gluon can build with version 1.9.0 of Rust or later but we recommend version 1.11.0 or later to avoid some very long compile times for the `gluon_parser` crate.

## Testing

To build and run all(*) tests for Gluon you can call `cargo test --features test --all`. Instead of `--all` you can pass the `-p <crate name>` and `--test <test module>` flags to compile a specific crate and/or test module. For instance, `cargo test --features test -p gluon_parser --test basic` to run the tests in [parsers/tests/basic.rs](https://github.com/gluon-lang/gluon/blob/master/parser/tests/basic.rs).

(*) You can see what Travis CI actually builds and tests in [scripts/travis.sh](https://github.com/gluon-lang/gluon/blob/master/scripts/travis.sh). Most of the time you should not need to worry about these additional tests and can just rely on travis running them.

## Pull requests

Once you have made some changes, you will need to file a pull request to get your changes merged into the main repository. If the code is still a work in progress, it can still be a good idea to submit a PR. That will let other contributors see your progress and provide assistance (you may prefix the PR message with [WIP] to make it explicit that the PR is incomplete).

You may see that some of the [commits][] follow the [commit message convention of Angular][]. Following this convention is optional but if you enjoy using it, feel free to do so! 

[commits]:https://github.com/gluon-lang/gluon/commit/9b36d699c63e482969239ed9f84779f7cd1ad2f3
[commit message convention of Angular]:https://github.com/angular/angular.js/blob/master/CONTRIBUTING.md#commit-message-format
