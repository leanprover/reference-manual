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

## Backporting Manual Changes

The manual for a Lean version is automatically deployed when a Git tag that matches the version is pushed. For Lean version `4.X.Y`, the manual is deployed from the contents of Git tag `v4.X.Y` (note the leading `v`). For version `4.X.Y-rcN`, the tag is `v4.X.Y-rcN`. In the event that a backported update is necessary, the tag should be changed. Pushing a new tag triggers the necessary deployment, but to do so requires first deleting any existing tag of the same name, because Git doesn't  support modification of existing tags. The following describes the steps and commands you may use to manage this process.

Make any desired changes to the codebase. Once you have tested changes locally, create a new branch based on the version of the reference manual you are modifying. By convention, this branch should match the tag (i.e. version number), but without the leading `v`. Push this branch to the remote.

For example, for modifications to the reference manual associated with Lean version 4.22, the branch should be named `4.22.0`. These examples assume that the main reference manual repository is named `origin` in your local checkout:

```
git checkout -b 4.22.0  # create new branch
git push origin 4.22.0  # push new branch to remote
```

Any existing tag matching the desired version number must be deleted on both the remote and locally, then regeneratged locally and pushed to the remote to trigger deployment. 

For example, for modifications to the reference manual associated with Lean version 4.22, the tag to be regenerated is `v4.22.0` and the commands to delete it are:

```
git push origin :v4.22.0  # delete remote tag
git tag --delete v4.22.0  # delete local tag
```

Recreating the `v4.22.0` tag locally and pushing to origin will now trigger the new deployment:

```
git tag v4.22.0  # create new tag locally
git push origin v4.22.0  # push tag to remote
```


## Contributing

Please see [CONTRIBUTING.md](CONTRIBUTING.md) for more information.

