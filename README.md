# Lean Language Reference

The Lean Language Reference is intended as a comprehensive, precise description of Lean. It is first and foremost a reference work in which Lean users can look up detailed information, rather than a tutorial for new users.

This new reference has been rebuilt from the ground up in Verso. This means that all example code is type checked, the source code contains tests to ensure that it stays up-to-date with respect to changes in Lean, and we can add any features that we need to improve the documentation. Verso also makes it easy to integrate tightly with Lean, so we can show function docstrings directly, mechanically check descriptions of syntax against the actual parser, and insert cross-references automatically.


## Reading the Manual

The latest release of this reference manual can be read [here](https://lean-lang.org/doc/reference/latest/).

For developers:
 * The output of building the current state of the `nightly-testing` branch can be read [here](https://lean-reference-manual-review.netlify.app/).
 * Each pull request in this repository causes two separate previews to be generated, one with extra information that's only useful to those actively working on the text, such as TODO notes and symbol coverage progress bars. These are posted by a bot to the PR after the first successful build.

## Branches and Development

The two most important branches are:
 * `main` tracks the latest Lean release or release candidate
 * `nightly-testing` tracks the latest Lean nightlies

New content that addresses in-development features of Lean will be
written on `nightly-testing`, while updates to existing content may be
written either on `main` or `nightly-testing`, as appropriate. From
time to time, `main` will be merged into `nightly-testing`; when Lean
is released, the commits in `nightly-testing` are rebased onto `main`
to achieve a clean history.

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
python3 ./server.py 8880 &
```

Then open <http://localhost:8880> in your browser.

## Building the Reference Manual Using Docker

If you prefer to use Docker, you can build and run the reference manual without installing dependencies manually. Follow these steps:

1. Build the Docker image:

   ```bash
   docker build -t reference-manual .
   ```

2. Run the Docker container:

   ```bash
   docker run -p 8880:8880 reference-manual
   ```

3. Open <http://localhost:8880> in your browser to view the reference manual.

## Contributing

Please see [CONTRIBUTING.md](CONTRIBUTING.md) for more information.

