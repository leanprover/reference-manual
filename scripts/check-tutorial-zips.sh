#!/usr/bin/env bash

# Verify that tutorial project zip files can be unpacked and built with lake
#
# Usage: check-tutorial-zips.sh [TOOLCHAIN]
#
# When TOOLCHAIN is given, it replaces the `lean-toolchain` file of each
# unpacked project. On Linux, some nightly toolchains currently report a version
# string that the zips turn into a toolchain name that elan rejects, so CI passes
# this repository's toolchain when building from a nightly. Releases and release
# candidates are unaffected and build with the toolchain from the zip.
# See https://github.com/leanprover/lean4/issues/14702
toolchain="${1:-}"

# First check that we actually found some zip files
zip_count=$(find _out/site/tutorials -name "*.zip" 2>/dev/null | wc -l)
if [ "$zip_count" -eq 0 ]; then
    echo "Error: No tutorial zip files found in _out/site/tutorials"
    echo "If the output structure changed, update this script."
    exit 1
fi

successes=0
failures=0

while IFS= read -r zip; do
    echo "=== Testing: $zip"
    tmpdir=$(mktemp -d)
    unzip -q "$zip" -d "$tmpdir"

    # Find the project directory (may be nested inside the zip)
    project_dir=$(find "$tmpdir" -name "lakefile.lean" -o -name "lakefile.toml" | head -1 | xargs dirname 2>/dev/null)

    if [ -z "$project_dir" ]; then
        echo "Warning: No lakefile found in $zip"
        ((failures++))
    else
        if [ -n "$toolchain" ]; then
            echo "Using toolchain: $toolchain"
            echo "$toolchain" > "$project_dir/lean-toolchain"
        fi
        pushd "$project_dir" > /dev/null
        if lake build 2>&1; then
            echo "Build succeeded"
            ((successes++))
        else
            echo "Build failed"
            ((failures++))
        fi
        popd > /dev/null
    fi

    rm -rf "$tmpdir"
done < <(find _out/site/tutorials -name "*.zip" 2>/dev/null)

echo
echo "Summary:"
echo "  Succeeded: $successes"
echo "  Failed:    $failures"

if [ $failures -ne 0 ]; then
    exit 1
else
    exit 0
fi
