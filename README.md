# Mathlib Documentation

## Reading the Manual

The latest release of this Mathlib manual can be read [here](https://leanprover-community.github.io/mathlib-manual/html-multi/).

## Code origin / Installation

This is mostly adapted code from the [Lean Language Reference](https://github.com/leanprover/reference-manual). **You should check there for installation instructions.**

Any problems beyond the content itself are probably carried over from there, and might need fixing there.

## Version bumping

The Lean reference manual has tags of the form `v4.X.0` which can be used. The process should be:

* change `lean-toolchain` to next stable release `v4.X.0`
* call `lake update`
* try `lake build`
* merge upstream tag `v4.X.0` into `main` with the following merging strategy:
  * `Meta/` and `Meta.lean` are important and should probably be completely replaced with the new upstream version.
  * Modified files (which "our" version should be kept) include: `Manual/Tactics` and `Manual/Guides` (with their Lean files)
    and `Manual.lean`
  * The `lakefile.lean` has only modified `require` statements
  * `Manual/Tweaks.lean` is completely ours.
  * Things that "we" deleted can stay deleted. I used something like `git status | sed -n 's/deleted by us://p' | xargs git rm`
    to delete them all once in the merge conflict.
* All workflows are deleted except `ci.yml` which has been largely rewritten to allow for export github pages. Best strategy should be to accept "ours" and then pick the relevant steps manually from upstream.

# Original README

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
python3 ./server.py 8880 &
```

Then open <http://localhost:8880> in your browser.

## Development

In theory, one should be able to update this by setting the desired toolchain in `lean-toolchain` and then call

```
lake update
```

However, this requires Verso to be compatible with the Lean version Mathlib uses.

Since this project is directly forked from [Lean Language Reference](https://lean-lang.org/doc/reference/latest) you might want to rebase the newest version thereof. In case of merge conflicts, everything in `Manual.lean`, `Manual/Tactics*` and `.github/workflows/ci.yml` should be "ours" and most likely everything else can just be resolved as "theirs". `Manual/Guides*` should not exist upstream and be completely "ours".

## Contributing

We happily accept content!
