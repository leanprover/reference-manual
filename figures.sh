#!/bin/bash

# FIXME: The Lake config doesn't seem to always build the figures. For now, this is a hack to work
# around it, but it should be fixed when deadlines are over.

shopt -s nullglob

cd figures || exit
for f in *.tex; do
    stem=${f%.*}
    lualatex "$stem"
    lualatex "$stem"
    lualatex "$stem"
    lualatex "$stem"
    pdftocairo -svg "$stem.pdf" "$stem.svg"
done

cd ..
mkdir -p static/figures
cp figures/*.pdf static/figures/
cp figures/*.svg static/figures/
