# Contributing to Gluon

## Filing bug reports

It does not matter if you found a soundness issue in typechecker or found the documentation confusing. Either way filing a an issue to the [issue tracker][] is extremely helpful.

[issue tracker]:https://github.com/Marwes/gluon/issues

## Finding something to work on

A good place to start is to look at the issues marked as [beginner][] which are issues that should be possible to work on without knowledge on the inner workings of Gluon.

If you find something that looks interesting then please leave a comment on the issue, that way you can get assistance quicker and there is no risk of duplicating work.

[beginner]:https://github.com/Marwes/gluon/labels/Beginner

## Building

Gluon can build with version 1.9.0 of Rust or later but we recommend to use version 1.11.0 or later to avoid some very long compile times for the `gluon_parser` crate.

## Testing

To build and run all tests for Gluon you can use the `test.sh` script. If you look inside it you can see that it actually builds from the `c-api` directory (this is necessary as the `gluon_c-api` crate depends on the `gluon` crate). This means that all build artifacts end up in `c-api/target`. For this reason if you want to run tests only for a single crate you should run something like `(cd c-api && cargo test --features test -p gluon_check testname)`.

If you are building with a nightly version of rust which supports workspaces you can use the `test-nightly.sh` script instead which puts the build artifacts in the root folder instead of in `c-api`.

## Pull requests

Once you have made some changes you will need to file a pull request to get your changes merged into the main repository. If the code is still a work in progress it can still be a good idea to submit a PR as that will let other contributors see your progress and provide assistance (you may prefix the PR message with [WIP] to make it explicit that the PR is incomplete).

You may see that some of the [commits](https://github.com/Marwes/gluon/commit/9b36d699c63e482969239ed9f84779f7cd1ad2f3) follow the [commit message convention of Angular](https://github.com/angular/angular.js/blob/master/CONTRIBUTING.md#commit-message-format). Following this convention is optional but if you enjoy using it then feel free to do so! 