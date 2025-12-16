# Lean Language Reference

The Lean Language Reference is intended as a comprehensive, precise
description of Lean. It is first and foremost a reference work in
which Lean users can look up detailed information, rather than a
tutorial for new users.

This new reference has been rebuilt from the ground up in Verso. This
means that all example code is type checked, the source code contains
tests to ensure that it stays up-to-date with respect to changes in
Lean, and we can add any features that we need to improve the
documentation. Verso also makes it easy to integrate tightly with
Lean, so we can show function docstrings directly, mechanically check
descriptions of syntax against the actual parser, and insert
cross-references automatically.

## Reading the Manual

The latest release of this reference manual can be read
[here](https://lean-lang.org/doc/reference/latest/).

For developers:

- The output of building the current state of the `nightly-testing`
  branch can be read
  [here](https://lean-reference-manual-review.netlify.app/).
- Each pull request in this repository causes two separate previews to
  be generated, one with extra information that's only useful to those
  actively working on the text, such as TODO notes and symbol coverage
  progress bars. These are posted by a bot to the PR after the first
  successful build.

## Branches and Development

The two most important branches are:

- `main` tracks the latest Lean release or release candidate
- `nightly-testing` tracks the latest Lean nightlies

New content that addresses in-development features of Lean will be
written on `nightly-testing`, while updates to existing content may be
written either on `main` or `nightly-testing`, as appropriate. From
time to time, `main` will be merged into `nightly-testing`; when Lean
is released, the commits in `nightly-testing` are rebased onto `main`
to achieve a clean history.

See later in this README for details about how these branches are kept
up to date.

## Building the Reference Manual Locally

This reference manual contains figures that are built from LaTeX
sources. To build them, you'll need the following:

- A LaTeX installation, including LuaLaTeX and the following packages
  from TeXLive:
  - `scheme-minimal`
  - `latex-bin`
  - `fontspec`
  - `standalone`
  - `pgf`
  - `pdftexcmds`
  - `luatex85`
  - `lualatex-math`
  - `infwarerr`
  - `ltxcmds`
  - `xcolor`
  - `fontawesome`
  - `spath3`
  - `inter`
  - `epstopdf-pkg`
  - `tex-gyre`
  - `tex-gyre-math`
  - `unicode-math`
  - `amsmath`
  - `sourcecodepro`
- `pdftocairo`, which can be found in the `poppler-utils` package on
  Debian-derived systems and the `poppler` package in Homebrew

Additionally, to run the style checker locally, you'll need
[Vale](https://vale.sh/). It runs in CI, so this is not a necessary
step to contribute.

Part of the manual deployment process adds JavaScript to each version
that inserts metadata to both enable links to live.lean-lang.org and
arrange for them to target the correct versions of Lean. To test these
links locally, follow the instructions in a comment in the definition
of `staticJs` in `Main.lean`.

To build the manual, run the following command:

```
lake exe generate-manual --depth 2
```

Then run a local web server on its output:

```
python3 ./server.py 8880 &
```

Then open <http://localhost:8880> in your browser.

## Contributing

Please see [CONTRIBUTING.md](CONTRIBUTING.md) for more information.

# Deployment Infrastructure

TL;DR: push a tag of the form `vX.Y.Z` onto the commit that should be
released as the manual for that version, and the rest is automatic.

This directory contains the deployment infrastructure for the
reference manual. Deployment happens in GitHub Actions, in response to
certain tags being pushed. Because the latest version of the GH action
file will always be used, and we want to be able to mutate tags to
re-deploy old manual versions (e.g. to update CSS for consistent look
and feel while keeping content version-accurate, or add a "THIS IS
OBSOLETE" banner in a few years). Thus, the steps of the workflow that
might change are captured in scripts that are versioned along with the
code.

The files are:

- `prep.sh` is used to set up the build, installing OS-level
  dependencies and Elan.

- `build.sh` is used to build the executable that generates the
  manual.

- `generate.sh` actually generates release-ready HTML, saving it in
  `/html` in the root of this repository.

- `release.py` puts the generated HTML in the right place on a new
  commit on the branch `deploy`

Everything above is what needs to happen specifically to the single
version of the documentation that is being updated in the course of
the deploy. There is one further step, which is computing the desired
state of the final `postdeploy` branch from the state in the branch
`deploy`. This is done by the script `overlay.py`, which is triggered
by pushes to `deploy`, and therefore runs at branch `main` rather than
at the tag being pushed.

We might have named the two branches `predeploy` and `deploy`, but
chose instead `deploy` and `postdeploy` so that we cold leave
unchanged the older tags for particular versions of the manual which
still have workflows that emit commits to `deploy`.

## Deployment Overview

The goal is to have versioned snapshots of the manual, with a
structure like:

- `https://lean-lang.org/doc/reference/latest/`- latest version
- `https://lean-lang.org/doc/reference/4.19.0/` - manual for v4.19.0
- `https://lean-lang.org/doc/reference/4.20.0/` - manual for v4.19.0

and so forth. `https://lean-lang.org/doc/reference/` should redirect
to `latest`. It's important to be able to edit past deployments as
well.

An orphan branch, called `deploy`, should at all times contain this
structure. With the three URLs above, the branch would contain three
directories:

- `/4.20.0/` - built HTML served for 4.20.0
- `/4.19.0/` - built HTML served for 4.19.0
- `/latest` - symlink to `/4.20.0`

The `release.py` script is responsible for updating this structure. It
takes the generated HTML directory, the version number, and the
deployment branch name as arguments, and then does the following:

1.  It copies the HTML to the branch (deleting an existing directory
    first if needed).
2.  It updates the `latest` symlink to point at the most recent
    version, with all numbered releases being considered more recent
    than any nightly and real releases being more recent than their
    RCs.
3.  It commits the changes to the branch `deploy`, then switches back
    to the original branch.

A successful push to deploy in this way triggers a GH action that runs
the `overlay.py` script, which is then responsible for creating a new
commit to `postdeploy`, based on `deploy`. This commit includes all
desired overlays. At time of writing, this is just a single file
`static/metadata.js` in each version of the reference manual that
contains information about whether the version is in fact stable or
latest.

A successful push to `postdeploy` in this way triggers a GH Action
which actually publishes the content to netlify.

## Overlays

The script `overlay.py` computes `postdeploy` from `deploy` any time
`deploy` changes. Its purpose is to add metadata or make in-place
changes to `deploy` content that is best thought of as a unified
overlay on top of the data that exists at the historical tags
`4.19.0`, `4.20.0`, etc.

Examples of the sorts of things we might like to achieve with this
overlay mechanism are:

- injecting version metadata so that a particular version of the
  manual knows _that_ it is the current latest or latest-stable
  version
- global css changes across all versions, for consistency
- banners appended to sufficiently old versions' manuals describing
  how they are so old as to be deprecated and unsupported

Interactions between overlays created by `overlay.py` and reference
manual versions should be carefully considered to ensure
backwards-compatibility.

An overlay that simply injects a `<div>` inside old versions is
relatively safe, for the document being injected into doesn't need to
know about the injection. However, if a document depends rigidly on
the presence of data created by the overlay mechanism, a problem could
occur if the overlay changes to not produce that data in the future.

Therefore we can be careful on both sides:

- overlays should, ideally, as time goes on, only monotonically
  produce more data, e.g. it should only add fields to injected
  javascript values and avoid changing the contract of existing
  fields.
- documents should, ideally, fail gracefully if injected data they
  expect to exist is missing

### Local Testing

To test `overlay.py` locally before pushing, do the following.

- Ensure branches `deploy` and `postdeploy` exist locally.
- You'll probably want to do

```
git fetch
git checkout deploy
git reset --hard remotes/upstream/deploy
git checkout postdeploy
git reset --hard remotes/upstream/postdeploy
```

- From the `reference-manual` checkout directory, on branch `main`,
  from a clean working directory (i.e. make sure to commit any changes
  you've made) run

```shell
python3 -B deploy/overlay.py . deploy postdeploy
```

- Inspect whatever `postdeploy` results you're interested in, e.g.

```
git show postdeploy:4.25.0-rc2/Type-Classes/Basic-Classes/index.html
# Expect to see <meta name="robots" content="noindex">
```

```
git show postdeploy:latest/Type-Classes/Basic-Classes/index.html
# Expect to *not* see <meta name="robots" content="noindex">
```

# Supporting Nightlies

Everything described in this section has two goals:

1.  We should always be able to produce a reference manual for a new
    Lean release with a minimal delay. This means we need to discover
    breaking changes and adapt to them on an ongoing basis.
2.  Lean developers should always be able to document their changes to
    the language.

## Keeping `nightly-testing` Updated

Keeping the `nightly-testing` branch up to date is key to supporting
both goals. It needs to be kept up to date in two ways: it needs to
support the latest Lean nightly, and it needs to include all changes
made on `main` so that they will also be adapted and ready to go for
releases.

### Maintaining `nightly-testing`

To the extent that it is feasible, the `nightly-testing` branch is
kept up to date with Lean nightlies. The process for doing so is
partially automated. The CI config file
[`update-nightly.yml`](.github/workflows/update-nightly.yml)
[runs](https://github.com/leanprover/reference-manual/actions/workflows/update-nightly.yml)
every six hours. If it detects a newer nightly than the one in
`nightly-testing`'s `lean-toolchain` file, then it attempts to change
the contents of `lean-toolchain` to the latest nightly and build the HTML
version of the manual. On success, it commits the result and pushes it
to `nightly-testing`, adding the tag
`nightly-testing-YYYY-MM-DD`.

When the automated process fails, a human-created PR to `nightly-testing` is
required.

1. Create a branch `bump-YYYY-MM-DD` file off of the `nightly-testing`
   branch
2. Update the `lean-toolchain` to the latest available
   `leanprover/lean4:nightly-*` toolchain
3. Make any changes to the manual necessary to build the manual on top of the
   new nightly.
   After these changes are added back to `nightly-testing` via PR, the
   [`tag-nightly-testing.yml`](.github/workflows/tag-nightly-testing.yml) action
   [runs](https://github.com/leanprover/reference-manual/actions/workflows/tag-nightly-testing.yml)
   automatically and applies the `nightly-testing-YYYY-MM-DD` tag.

The [`merge-main-nightly.yml`](.github/workflows/merge-main-nightly.yml)
workflow
[runs](https://github.com/leanprover/reference-manual/actions/workflows/update-nightly.yml)
every six hours. It attempts to merge `main` into `nightly-testing` and
generate HTML. If this succeeds, then the result is pushed to
`nightly-testing`. If it fails, human intervention is required. (Hint: make
sure that the toolchain is up-to-date before trying to fix failures of merging
main into nightly.)

### Maintaining `nightly-with-manual` in Lean

The Lean repository contains a branch `nightly-with-manual` that
contains the most recent Lean nightly for which a reference manual
`nightly-testing` build succeeded. In particular, it should always
contain the Lean nightly indicated by this repository's most recent
`nightly-testing-YYYY-MM-DD` tag.

When a change is pushed to `nightly-testing` that modifies
`lean-toolchain`,
[`nightly-with-manual.yml`](.github/workflows/nightly-with-manual.yml)
[runs](https://github.com/leanprover/reference-manual/actions/workflows/nightly-with-manual.yml).
This workflow also runs twice per day on its own, and it is
explicitly invoked by `update-nightly.yml`. It finds the most recent
`nightly-testing-YYYY-MM-DD` tag in the `reference-manual` repository. This
tag also exists in the `lean4-nightly` repository, and the commit it
corresponds to also exists in the `lean4` repository. The workflow resets
the `nightly-with-manual` branch to this commit.

This branch is important because it is used to provide feedback in
Lean PRs as to whether the manual succeeds in building their PR, or
whether documentation adaptation will also be necessary.

### PR Feedback in Lean

For every pull request, Lean's CI creates or updates a branch in this
repository to serve as the basis for adaptations. For PR #XXXXX, the
branch is named `lean-pr-testing-XXXXX`. This branch is based off the
most recent nightly. In it, the toolchain is set to the release that's
created for each Lean PR.

These branches are used to report status upstream to Lean. When this
reposistory's [`ci.yml`](.github/workflows/ci.yml) runs on them, the
status is reported upstream by
[`lean-pr-testing-comments.sh`](scripts/lean-pr-testing-comments.sh).

On each push to `nightly-testing`,
[`discover-lean-pr-testing.yml`](scripts/discover-lean-pr-testing.yml)
runs. When it discovers that a Lean PR has been merged, it
automatically merges the PR's corresponding adaptation branch into
`nightly-testing`.
