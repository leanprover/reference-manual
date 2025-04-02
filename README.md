# Mathlib Documentation

## Reading the Manual

The latest release of this Mathlib manual can be read [here](https://leanprover-community.github.io/mathlib-manual/html-multi/).

## Code origin / Installation

This is mostly adapted code from the [Lean Language Reference](https://github.com/leanprover/reference-manual). **You should check there for installation instructions.**

Any problems beyond the content itself are probably carried over from there, and might need fixing there.

## Building the Reference Manual Locally

This reference manual contains figures that are built from LaTeX sources. To build them, you'll need the following:
 * A LaTeX installation, including LuaLaTeX and the following packages from TeXLive:
   + `scheme-minimal`
   + `latex-bin`
   + `fontspec`
   + `standalone`
   + `pgf`
   + `pdftexcmds`
   + `luatex85`
   + `infwarerr`
   + `ltxcmds`
   + `xcolor`
   + `fontawesome`
   + `spath3`
   + `inter`
   + `epstopdf-pkg`
   + `tex-gyre`
   + `sourcecodepro`
 * `pdftocairo`, which can be found in the `poppler-utils` package on Debian-derived systems and the `poppler` package in Homebrew

Additionally, to run the style checker locally, you'll need [Vale](https://vale.sh/). It runs in CI, so this is not a necessary step to contribute.

To build the manual, run the following command:

```
lake exe generate-manual --depth 2
```

Then run a local web server on its output:
```
python3 -m http.server 8880 --directory _out/html-multi
```

Then open <http://localhost:8880> in your browser.

## Development

In theory, one should be able to update this by calling a simple

```
lake update
```

However, this requires Verso to be compatible with the Lean version Mathlib uses.

## Contributing

We happily accept content!
