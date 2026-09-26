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

# Local Artifact Caches
%%%
tag := "lake-cache-local"
%%%

*This is an experimental feature that is still undergoing development.*

Lake supports a {deftech (key := "local cache")}_local artifact cache_ that stores individual build products, tracking the complete set of inputs that gave rise to them.
By default, each {tech}[toolchain] has its own cache because intermediate build products are usually not compatible between toolchain versions.
However, a toolchain's cache is shared between all local {tech}[workspaces] that use it, so common dependencies don't need to be rebuilt.
If two separate workspaces with the same toolchain depend on the same package, then they can share each others' build products.

Because it is an experimental feature, the local cache is disabled by default.
It is only enabled when the {envVar}`LAKE_ARTIFACT_CACHE` environment variable is set to `true` or when the {tomlField Lake.Package}`enableArtifactCache` field is set to `true` in the {ref "lake-config"}[configuration file].

The location of the Lake cache can be configured with the {envVar}`LAKE_CACHE_DIR`  environment variable .
If set to an empty value, Lake will locate the cache in appropriate system location for the OS (e.g., in a `.lake` folder in the home directory or under the `XDG_CACHE_GOME`).
When `LAKE_CACHE_DIR` is set, the cache is not toolchain-bound, so it will share build products across toolchains where possible.
However, since the format of the Lake cache may change between different Lean versions, it is often best to use separate directories per version, or to otherwise ensure only compatible toolchain versions are being used.

## Mappings

When passed the `-o` option, {lake}`build` tracks the inputs used to generate each build product.
These are stored to a {deftech}_mappings file_ in JSON lines format, where each line of the file must be a valid JSON object.
A mappings file tracks a single package within a build, and includes all intermediate and final build products from the package that are part of the build.

By default, {lake}`build` saves the workspace's {tech}[root package]'s mappings.
The {lakeOpt}`--package` option selects a different package in the workspace, such as a dependency, saving its mappings instead.
The tracked build products include those that were already up to date and not regenerated, but not the package's targets that the build did not cover.

Lake can bundle a mappings file along with the {tech}[artifacts] it reference into directory via {lake}`cache stage`.
The directory can then be transported to another setup and reinserted into local artifact cache via {lake}`cache unstage`.
To better automate the process of transferring cache artifacts between machines, Lake provides builtin support for {tech}[remote cache services].

# Remote Artifact Caches
%%%
tag := "lake-cache-remote"
%%%

A {deftech}_remote cache service_ is a cloud storage service that hosts a {deftech}_remote artifact cache_, a store of mappings and artifacts for many package builds.
The {lake}`cache put` command uploads the build products in a {tech}[mappings file] from the local cache to a remote cache, and the {lake}`cache get` command downloads artifacts from the service into the local cache.
Setting up a remote artifact cache subscription to a separate cloud storage service with Amazon S3 interface (e.g., Amazon, Cloudflare), making it more involved than {ref "lake-github"}[GitHub release builds]

However, compared to GitHub release builds, a remote artifact cache is much more fine-grained.
It tracks build products at the level of individual source files, {tech}[`.olean` files], and object code, rather than at the level of entire packages.
This makes it possible to use the cache _incrementally_, downloading only the parts of the cache necessary to build a particular module or uploading only artifacts which have changed between builds.
It is, therefore, more space- and bandwidth-efficient, which is good for large projects which want to serve caches for many different builds.

## Configuration

Services providing remote artifact caches are specified in the global Lake configuration file through the `cache` table.
Each service is a table in the `cache.service` array of tables.
The set of configured services can be listed through the {lake}`cache services` command.

S3 buckets provided by cloud storage services often have separate endpoints for downloads and uploads.
The upload endpoint is usually authenticated whereas the download endpoint is made publicly available.
In Lake, each set of endpoints is represented as a distinct service.
The default services for {lake}`cache get` and {lake}`cache put` are specified by the `cache.defaultService` and `cache.defaultUploadService` keys, respectively.

:::example "Configuring an S3 Remote Cache Service"
*~/.lake/config.toml*
```toml
cache.defaultService = "s3-get"
cache.defaultUploadService = "s3-put"

[[cache.service]]
name = "s3-get"
kind = "s3"
artifactEndpoint = "https://s3-get.com/arts"
revisionEndpoint = "https://s3-get.com/revs"

[[cache.service]]
name = "s3-put"
kind = "s3"
artifactEndpoint = "https://s3-put.com/arts"
revisionEndpoint = "https://s3-put.com/revs"
```
:::

:::paragraph
A remote cache service can also be configured for per-command using the following environment variables:
 * {envVar}`LAKE_CACHE_KEY`
 * {envVar}`LAKE_CACHE_ARTIFACT_ENDPOINT`
 * {envVar}`LAKE_CACHE_REVISION_ENDPOINT`
:::

In general, the environment route is only recommended for CI or other workflows without a persistent configuration.
For local use, the global configuration is best.

## Uploading Builds

When uploading a trusted build, {lake}`cache put` provides the simplest interface.
However, when uploading builds from untrusted sources, it can leak service keys (e.g., caching builds of pull requests).
To avoid this, there is a {lake}`cache put-staged` command which uploads a directory produced by {lake}`cache stage`.
This command does not load a Lake workspace and thus does not run arbitrary code from the package.
However, it requires that build's identifiers (e.g., platform, toolchain, revision) be specified manually.

## Identifying Builds

By default, Lake segregates builds in the remote artifact cache by platform and toolchain (for each package revision).
While the results of Lean elaboration are generally cross-platform, they do not have to be, and Lake cannot distinguish between such cases.
Nonetheless, a package can promise Lake that its Lean code does not depend on platform specifics by setting {tomlField Lake.PackageConfig}`platformIndependent` to `true`.
Similarly, a package can set {tomlField Lake.PackageConfig}`fixedToolchain` to `true` to inform Lake that the package only compatible with a single toolchain.
With either option, Lake will no longer differentiate builds by that vector and, with both, the package's revision will be sole identifier.
An individual upload or download can also remove this identifiers by setting {lakeOpt}`--platform` or {lakeOpt}`--toolchain` to `none`.

# GitHub Release Builds
%%%
tag := "lake-github"
%%%

Lake supports uploading and downloading the complete set of build artifacts (i.e., the archived build directory) to/from the GitHub releases of packages.
This enables end users to fetch pre-built artifacts from the cloud without needed to rebuild the package from source themselves.
The {envVar}`LAKE_NO_CACHE` environment variable can be used to disable this feature.

## Downloading

To download artifacts, one should configure the package options {tomlField Lake.PackageConfig}`releaseRepo` and {tomlField Lake.PackageConfig}`buildArchive` to point to the GitHub repository hosting the release and the correct artifact name within it (if the defaults are not sufficient).
Then, set {tomlField Lake.PackageConfig}`preferReleaseBuild` to `true` to tell Lake to fetch and unpack it as an extra package dependency.

Lake will only fetch release builds as part of its standard build process if the package wanting it is a dependency (as the root package is expected to modified and thus not often compatible with this scheme).
However, should one wish to fetch a release for a root package (e.g., after cloning the release's source but before editing), one can manually do so via `lake build :release`.

Lake internally uses `curl` to download the release and `tar` to unpack it, so the end user must have both tools installed in order to use this feature.
If Lake fails to fetch a release for any reason, it will move on to building from the source.
This mechanism is not technically limited to GitHub: any Git host that uses the same URL scheme works as well.

## Uploading

To upload a built package as an artifact to a GitHub release, Lake provides the {lake}`upload` command as a convenient shorthand.
This command uses `tar` to pack the package's build directory into an archive and uses `gh release upload` to attach it to a pre-existing GitHub release for the specified tag.
Thus, in order to use it, the package uploader (but not the downloader) needs to have `gh`, the GitHub CLI, installed and in `PATH`.
