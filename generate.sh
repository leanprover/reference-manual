#!/usr/bin/env bash
set -euo pipefail

# Generate the manual and tutorials with support for preview and production modes

# Default values
MODE="preview"
VERSION=""
OUTPUT="_out/site"
DRAFT_FLAG=""

# Parse arguments
while [[ $# -gt 0 ]]; do
  case $1 in
    --mode)
      MODE="$2"
      shift 2
      ;;
    --version)
      VERSION="$2"
      shift 2
      ;;
    --output)
      OUTPUT="$2"
      shift 2
      ;;
    --draft)
      DRAFT_FLAG="--draft"
      shift
      ;;
    *)
      echo "Unknown option: $1"
      echo "Usage: $0 [--mode preview|production] [--version VERSION] [--output DIR] [--draft]"
      exit 1
      ;;
  esac
done

# Validate production mode requirements
if [ "$MODE" = "production" ]; then
  if [ -z "$VERSION" ]; then
    echo "Error: --version required for production mode"
    exit 1
  fi
  if [ -n "$DRAFT_FLAG" ]; then
    echo "Error: --draft not supported in production mode"
    exit 1
  fi
fi

# Set up remote configs based on mode
if [ "$MODE" = "preview" ]; then
  REF_REMOTE_CONFIG="test-data/reference-remotes.json"
  TUT_REMOTE_CONFIG="test-data/tutorial-remotes.json"
else
  # Production mode: generate temporary configs from templates
  REF_REMOTE_CONFIG="_build/production-remotes-reference.json"
  TUT_REMOTE_CONFIG="_build/production-remotes-tutorials.json"

  # Replace __VERSION__ in templates and write to temporary files
  mkdir -p _build
  sed "s/__VERSION__/$VERSION/g" config/production-remotes-reference.json.template > "$REF_REMOTE_CONFIG"
  sed "s/__VERSION__/$VERSION/g" config/production-remotes-tutorials.json.template > "$TUT_REMOTE_CONFIG"

  echo "Generated production configs with version $VERSION"
fi

# Generate the manual and tutorials
echo "Running generate-manual with args --depth 2 --verbose --delay-html-multi multi.json --remote-config $REF_REMOTE_CONFIG --with-word-count words.txt $DRAFT_FLAG"
lake --quiet exe generate-manual --depth 2 --verbose --delay-html-multi multi.json --remote-config "$REF_REMOTE_CONFIG" --with-word-count "words.txt" $DRAFT_FLAG

echo "Running generate-tutorials with args --verbose --delay tutorials.json --remote-config $TUT_REMOTE_CONFIG $DRAFT_FLAG"
lake --quiet exe generate-tutorials --verbose --delay tutorials.json --remote-config "$TUT_REMOTE_CONFIG" $DRAFT_FLAG

echo "Running generate-manual with args --verbose --resume-html-multi multi.json --remote-config $REF_REMOTE_CONFIG $DRAFT_FLAG"
lake --quiet exe generate-manual --verbose --resume-html-multi multi.json --remote-config "$REF_REMOTE_CONFIG" $DRAFT_FLAG

echo "Running generate-tutorials with args --verbose --resume tutorials.json --remote-config $TUT_REMOTE_CONFIG $DRAFT_FLAG"
lake --quiet exe generate-tutorials --verbose --resume tutorials.json --remote-config "$TUT_REMOTE_CONFIG" $DRAFT_FLAG

# Set up output directories
echo "Setting up output directories"
mkdir -p "$OUTPUT/reference"
mkdir -p "$OUTPUT/tutorials"

# Copy files
echo "Copying files to site directory"
if [ "$MODE" = "preview" ]; then
  cp test-data/index.html "$OUTPUT/index.html"
fi
cp -r _out/html-multi/ "$OUTPUT/reference/"
cp -r _tutorial-out/ "$OUTPUT/tutorials/"

echo "Done! Site generated at $OUTPUT/"
