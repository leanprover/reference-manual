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

Lake supports a {deftech (key := "local cache")}_local artifact cache_ that stores individual build products, tracking the complete set of inputs that contributed to their final value.
Each {tech}[toolchain] has its own cache because intermediate build products are not compatible between toolchain versions.
However, a toolchain's cache is shared between all local {tech}[workspaces] that use it, so common dependencies don't need to be rebuilt.
If two separate workspaces with the same toolchain depend on the same package, then they can share each others' build products.

Because it is an experimental feature, the local cache is disabled by default.
It is only enabled when the {envVar}`LAKE_ARTIFACT_CACHE` environment variable is set to `true` or when the {tomlField Lake.PackageConfig}`enableArtifactCache` field is set to `true` in the {ref "lake-config"}[configuration file].


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

## Cache Services
%%%
tag := "lake-cache-services"
%%%

A {deftech}_cache service_ is a named remote server that supplies both {tech (key := "artifact")}[build artifacts] and {tech (key := "mappings file")}[mappings].
A service named `"reservoir"` that provides cached data from Reservoir is always available.
Additional cache services can be defined in the system's Lake configuration file and in {tech}[packages].
The {lakeOpt}`--service` option selects a named cache service when using one of {ref "lake-cli-cache"}[Lake's cache commands].

Defining a cache service in a package enables package authors to provide pre-built artifacts to users.
Services defined in the system's configuration file can support both reading with {lake}`cache get` and writing with {lake}`cache put`, while services defined in packages are read-only.

:::paragraph
The available cache services can be queried using {lake}`cache services`.
If there are duplicate names, cache service names passed to {lakeOpt}`--service` are resolved by consulting the following sources in order:
0. the name `"reservoir"` always points to Reservoir
1. the {ref "lake-system-config"}[system Lake configuration file]
2. the root package's Lake configuration file
3. direct dependencies, with later {keywordOf Lake.DSL.requireDecl}`require` statements taking precedence
4. transitive dependencies, in increasing depth order, with later dependencies taking precedence over earlier dependencies
:::

:::paragraph
Running {lake}`cache get` with the {lakeOpt}`--service` option causes Lake to fetch both the {tech}[mappings file] and the {tech (key := "artifact")}[build artifacts] that the service provides.
The {lakeOpt}`--mappings-only` flag causes it to fetch only the mappings file and record that the artifacts it describes are available from the service.
If {lake}`build` discovers that a desired artifact is available on a service but not present, it downloads it when it is needed.
To use an S3-based service instead of Reservoir, a {lake}`cache get` command should specify the following options:
* {lakeOpt}`--service` to specify the service name (optional if {tomlField Lake.CacheConfig (show := "cache.defaultService")}`defaultService` is set)
* {lakeOpt}`--scope` for the cache's {tech (key := "cache scope")}[scope], which the service provider should advertise to users
* optionally {lakeOpt}`--mappings-only`, which delays the download of artifacts until they are required for a build
* optionally {lakeOpt}`--package`, to fetch mappings and artifacts for a package other than the {tech}[root package].
:::


### Service Kinds
%%%
tag := "lake-cache-service-kinds"
%%%

There are two kinds of remote cache services: those that implement the S3 endpoint protocol, and those that implement Reservoir's API.
Both store {tech (key := "artifact")}[build artifacts], indexed by their content hashes, as well as {tech (key := "mappings file")}[mappings].
The {lake}`cache put` command only supports uploading to S3-style cache services.
The kind of a service is specified in the {tomlField Lake.CacheServiceConfig}`kind` field in a package or system configuration file.

S3-style cache services require [S3-compatible](https://docs.aws.amazon.com/AmazonS3/latest/API/Welcome.html) buckets with two endpoints: one for artifacts, and one for {tech (key := "mappings file")}[mappings] associated with each Git revision.
Both endpoints may point at the same bucket.
Lake fetches artifacts directly from the artifact endpoint, requesting files based on their content hashes.
Mappings are fetched from the revision endpoint according to the Git revision.
When uploading to S3-style cache services with {lake}`cache put`, the contents of {envVar}`LAKE_CACHE_KEY` are used for authentication over the [AWS Signature Version 4 protocol](https://docs.aws.amazon.com/AmazonS3/latest/API/sig-v4-authenticating-requests.html).

For S3 endpoints, the configured {tech (key := "cache scope")}[scope] is used as a directory prefix.
If an S3 endpoint has artifact endpoint `ARTS` and scope `SCOPE`, then an artifact with hash `HASH` would be requested from `ARTS/SCOPE/HASH.art`.
Similarly, if the revision endpoint is `REVS` then the mappings for `COMMIT` would be requested from `REVS/SCOPE/COMMIT.jsonl`.
If the {lakeOpt}`--repo` option is provided instead of {lakeOpt}`--scope`, then mappings are stored in a directory that additionally encodes the platform and toolchain.

Reservoir itself is a Reservoir-style cache service.
Organizations that need to carefully audit available packages or that for policy reasons cannot connect to Reservoir itself may implement their own.
This requires implementing a compatible HTTP API.



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
