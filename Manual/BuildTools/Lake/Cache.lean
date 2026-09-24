/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen, Mac Malone
-/

import VersoManual

import Lean.Parser.Command
import Lake.Build.Package
import Lake.Build.Library
import Lake.Build.Module

import Manual.Meta

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option guard_msgs.diff true

#doc (Manual) "Caching Builds" =>
%%%
tag := "lake-cache"
%%%

Builds of large packages can consume significant time.
Compounding this, switching between local development branches can cause Lake to rebuild the same code many times.
To address these problems, Lake provides a number of ways to {deftech (key := "build cache")}_cache_ builds for later reuse.
Lake's {ref "lake-cache-local"}[local artifact cache] enables reuse of builds when switching between branches and across multiple local copies of the same package.
The {ref "lake-cache-remote"}[remote artifact cache] expands this to sharing artifact caches across machines. However, it requires the package developers to own cloud storage.
As an alternative for developers without cloud storage but already using GitHub, {ref "lake-github"}[release builds] provide a low-setup way to ship complete builds to users.

# Artifact Caches
%%%
tag := "lake-cache-local"
%%%

*This is an experimental feature that is still undergoing development.*

Lake supports a {deftech (key := "local cache")}_local artifact cache_ that stores individual build products, tracking the complete set of inputs that gave rise to them.
Each {tech}[toolchain] has its own cache because intermediate build products are not compatible between toolchain versions.
However, a toolchain's cache is shared between all local {tech}[workspaces] that use it, so common dependencies don't need to be rebuilt.
If two separate workspaces with the same toolchain depend on the same package, then they can share each others' build products.

Because it is an experimental feature, the local cache is disabled by default.
It is only enabled when the {envVar}`LAKE_ARTIFACT_CACHE` environment variable is set to `true` or when the {TODO}[ref] `enableArtifactCache` field is set to `true` in the {ref "lake-config"}[configuration file].


# Remote Artifact Caches
%%%
tag := "lake-cache-remote"
%%%

Build products can be retrieved from remote cache servers and placed into the local cache.
This makes it possible to completely avoid local builds.
The {lake}`cache get` command is used to download artifacts into the local cache.

Compared to {ref "lake-github"}[GitHub release builds], the remote artifact cache is much more fine-grained.
It tracks build products at the level of individual source files, {tech}[`.olean` files], and object code, rather than at the level of entire packages.

## Mappings

When passed the `-o` option, {lake}`build` tracks the inputs used to generate each build product.
These are stored to a {deftech}_mappings file_ in JSON lines format, where each line of the file must be a valid JSON object.
A mappings file tracks a single package within a build, and includes all intermediate and final build products from the package that are part of the build.

By default, {lake}`build` saves the workspace's {tech}[root package]'s mappings.
The {lakeOpt}`--package` option selects a different package in the workspace, such as a dependency, saving its mappings instead.
The tracked build products include those that were already up to date and not regenerated, but not the package's targets that the build did not cover.
The {lake}`cache put` command uploads the build products in the mappings file from the local cache to the remote cache.

## Configuration

:::paragraph
Remote artifact caches are configured using the following environment variables:
 * {envVar}`LAKE_CACHE_KEY`
 * {envVar}`LAKE_CACHE_ARTIFACT_ENDPOINT`
 * {envVar}`LAKE_CACHE_REVISION_ENDPOINT`
:::

# GitHub Release Builds
%%%
tag := "lake-github"
%%%

Lake supports uploading and downloading the complete set of build artifacts (i.e., the archived build directory) to/from the GitHub releases of packages.
This enables end users to fetch pre-built artifacts from the cloud without needed to rebuild the package from source themselves.
The {envVar}`LAKE_NO_CACHE` environment variable can be used to disable this feature.

## Downloading

To download artifacts, one should configure the package options `releaseRepo` and `buildArchive` to point to the GitHub repository hosting the release and the correct artifact name within it (if the defaults are not sufficient).
Then, set `preferReleaseBuild := true` to tell Lake to fetch and unpack it as an extra package dependency.

Lake will only fetch release builds as part of its standard build process if the package wanting it is a dependency (as the root package is expected to modified and thus not often compatible with this scheme).
However, should one wish to fetch a release for a root package (e.g., after cloning the release's source but before editing), one can manually do so via `lake build :release`.

Lake internally uses `curl` to download the release and `tar` to unpack it, so the end user must have both tools installed in order to use this feature.
If Lake fails to fetch a release for any reason, it will move on to building from the source.
This mechanism is not technically limited to GitHub: any Git host that uses the same URL scheme works as well.

## Uploading

To upload a built package as an artifact to a GitHub release, Lake provides the {lake}`upload` command as a convenient shorthand.
This command uses `tar` to pack the package's build directory into an archive and uses `gh release upload` to attach it to a pre-existing GitHub release for the specified tag.
Thus, in order to use it, the package uploader (but not the downloader) needs to have `gh`, the GitHub CLI, installed and in `PATH`.
