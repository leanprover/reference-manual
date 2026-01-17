#!/usr/bin/env bash
set -euo pipefail

# VERSION is set by release-tag.yml from the git tag
if [ -z "${VERSION:-}" ]; then
    echo "Error: VERSION environment variable must be set"
    exit 1
fi

# Build both manual and tutorials using the combined generate script
./generate-html.sh --mode production --version "$VERSION" --output "html/site"
