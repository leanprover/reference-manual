# Lean Language Reference

The Lean Language Reference is intended as a comprehensive, precise description of Lean. It is first and foremost a reference work in which Lean users can look up detailed information, rather than a tutorial for new users.

This new reference has been rebuilt from the ground up in Verso. This means that all example code is type checked, the source code contains tests to ensure that it stays up-to-date with respect to changes in Lean, and we can add any features that we need to improve the documentation. Verso also makes it easy to integrate tightly with Lean, so we can show function docstrings directly, mechanically check descriptions of syntax against the actual parser, and insert cross-references automatically.


## Reading the Manual

The latest release of this reference manual can be read [here](https://lean-lang.org/doc/reference/latest/).

For developers:
 * The output of building the current state of the `nightly-testing` branch can be read [here](https://lean-reference-manual-review.netlify.app/).
 * Each pull request in this repository causes two separate previews to be generated, one with extra information that's only useful to those actively working on the text, such as TODO notes and symbol coverage progress bars. These are posted by a bot to the PR after the first successful build.

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
   + `lualatex-math`
   + `infwarerr`
   + `ltxcmds`
   + `xcolor`
   + `fontawesome`
   + `spath3`
   + `inter`
   + `epstopdf-pkg`
   + `tex-gyre`
   + `tex-gyre-math`
   + `unicode-math`
   + `amsmath`
   + `sourcecodepro`
 * `pdftocairo`, which can be found in the `poppler-utils` package on Debian-derived systems and the `poppler` package in Homebrew
 
Additionally, to run the style checker locally, you'll need [Vale](https://vale.sh/). It runs in CI, so this is not a necessary step to contribute.

To build the manual, run the following command:

```
lake exe generate-manual --depth 2
```

Then run a local web server on its output:
```
python3 -m http.server 8880 --directory _out/html-multi &
```

Then open <http://localhost:8880> in your browser.

## Contributing

Please see [CONTRIBUTING.md](CONTRIBUTING.md) for more information.

