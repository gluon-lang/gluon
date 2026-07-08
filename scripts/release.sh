#!/bin/bash
set -ex

VERSION=$1

git cliff --unreleased --tag $VERSION --prepend CHANGELOG.md

git add CHANGELOG.md

./scripts/version.sh $VERSION
