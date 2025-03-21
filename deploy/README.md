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
  
* `release.py` puts the generated HTML in the right place on the
  deployment branch.
  
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
 3. It commits the changes to the deployment branch, then switches
    back to the original branch.

After this, the GH Action for deployment pushes the edited deploy
branch. Another action is responsible for actually deploying the
contents of this branch when it's pushed.

## 
