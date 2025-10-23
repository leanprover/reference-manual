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

* `prep.sh` is used to set up the build, installing OS-level
  dependencies and Elan.

* `build.sh` is used to build the executable that generates the
  manual.

* `generate.sh` actually generates release-ready HTML, saving it in
  `/html` in the root of this repository.

* `release.py` puts the generated HTML in the right place on a new commit
  on the branch `deploy`

Everything above is what needs to happen specifically to the single version
of the documentation that is being updated in the course of the deploy.
There is one further step, which is computing the desired state
of the final `postdeploy` branch from the state in the branch `deploy`.
This is done by the script `overlay.py`, which is triggered by pushes
to `deploy`, and therefore runs at branch `main` rather than at the tag
being pushed.

We might have named the two branches `predeploy` and `deploy`, but
chose instead `deploy` and `postdeploy` so that we cold leave
unchanged the older tags for particular versions of the manual which
still have workflows that emit commits to `deploy`.

## Deployment Overview

The goal is to have versioned snapshots of the manual, with a structure like:

 * `https://lean-lang.org/doc/reference/latest/`- latest version
 * `https://lean-lang.org/doc/reference/4.19.0/` - manual for v4.19.0
 * `https://lean-lang.org/doc/reference/4.20.0/` - manual for v4.19.0

and so forth.  `https://lean-lang.org/doc/reference/` should redirect
to `latest`. It's important to be able to edit past deployments as well.

An orphan branch, called `deploy`, should at all times contain this
structure. With the three URLs above, the branch would contain three
directories:

 * `/4.20.0/` - built HTML served for 4.20.0
 * `/4.19.0/` - built HTML served for 4.19.0
 * `/latest` - symlink to `/4.20.0`

The `release.py` script is responsible for updating this structure. It
takes the generated HTML directory, the version number, and the
deployment branch name as arguments, and then does the following:
 1. It copies the HTML to the branch (deleting an existing directory
    first if needed).
 2. It updates the `latest` symlink to point at the most recent
    version, with all numbered releases being considered more recent
    than any nightly and real releases being more recent than their
    RCs.
 3. It commits the changes to the branch `deploy`, then switches
    back to the original branch.

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

Examples of the sorts of things we might like to achieve with this overlay mechanism are:
- injecting version metadata so that a particular version of the manual knows *that* it is the current latest or latest-stable version
- global css changes across all versions, for consistency
- banners appended to sufficiently old versions' manuals describing how they are so old as to be deprecated and unsupported

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
produce more data, e.g. it should only add fields to injected javascript values and avoid changing the contract of existing fields.
- documents should, ideally, fail gracefully if injected data they expect to exist is missing
