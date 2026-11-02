#!/usr/bin/env bash

# Check that the Verso branch in lakefile.lean is a bump branch that matches
# the Lean version of the nightly in lean-toolchain
#
# Usage: check-verso-bump-branch.sh

set -euo pipefail

toolchain=$(cat lean-toolchain)
if [[ "$toolchain" != *:nightly-* ]]; then
    echo "::error::expected lean-toolchain to be a nightly toolchain, $toolchain does not have the right form."
    exit 1
fi

lean_version=$(lean --version)
echo "$lean_version"
version=$(lean --version | grep -oE '[0-9]+\.[0-9]+\.[0-9]+' | head -n1) || {
    echo "::error::Couldn't find a version number in the output of 'lean --version'."
    exit 1
}
expected="bump/v$version"

pinned=$(grep -E '^require verso from' lakefile.lean | grep -oE 'bump/v4\.[0-9]+\.[0-9]+' | sort -u || true)
if [ -z "$pinned" ]; then
    echo "::error file=lakefile.lean::Verso should be required from '$expected', but it isn't required from a bump branch."
    exit 1
fi
if [ "$pinned" != "$expected" ]; then
    echo "::error file=lakefile.lean::Verso is required from '${pinned//$'\n'/, }', but $toolchain needs '$expected'."
    echo "Update the requirement in lakefile.lean and run 'lake --keep-toolchain update verso'."
    exit 1
fi

echo "Verso is required from $pinned, which matches $toolchain."
