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

#doc (Manual) "Package Overrides" =>
%%%
tag := "package-overrides"
%%%

Together, the {tech}[package configuration] and {tech}[manifest] describe the exact manner by which Lake expects to acquire dependencies.
Usually, this involves making a local copy of a remote Git repository over the network.
Lake terminates with an error if the remote repository cannot be accessed.
Because the sources of dependencies are predictable, builds are reproducible across systems; packages are retrieved in the same way from the same sources on all machines.

Nonetheless, there are situations where it is infeasible to acquire package dependencies the same way the original developers did.
For example, some companies require that all dependencies are audited prior to use, and not everyone always has access to the Internet while working.
In these situations, it is necessary to acquire packages in some other way.

Lake's {deftech}_package overrides_ allow a package dependency to be redirected from one source to another without modifying any {tech}[package configurations] or {tech}[manifests].
They do not allow packages to be added to or removed from the {tech}[workspace].
All transitive dependencies in the workspace respect the redirection.
The package overrides file is a JSON file that contains an alternate list of package entries.
These entries will take precedence over those in the package's {tech}[manifest].
This file can be provided to Lake either via the {lakeOpt}`--packages` option or by placing it at a fixed path within the Lake workspace: `.lake/package-overrides.json`.

The syntax of package entries in the package overrides file mirrors that of the {tech}[manifest].
Thus, it is possible to copy an entry from a manifest into a package overrides file (and vice versa).
One way to determine the necessary syntax for a package entry is to add a temporary dependency to a {tech}[package configuration] that matches the desired configuration, run {lake}`update` to generate a manifest with that dependency, and then copy the entry from the manifest into the package overrides file.

:::example "Making Remote Dependencies Local"

Consider a use case where programs are being developed in a restricted enviroment without network access (e.g., for security reasons).
The team wishes to compile a small tool written in Lean that depends on the [`@leanprover/Cli`](https://reservoir.lean-lang.org/@leanprover/Cli) library to provide a simple command-line interface.
That tool's {tech}[manifest] thus looks something like this:

```lakeManifest
{
  "version": "1.2.0",
  "packagesDir": ".lake/packages",
  "packages": [{
    "url": "https://github.com/leanprover/lean4-cli",
    "type": "git",
    "subDir": null,
    "scope": "leanprover",
    "rev": "0000000000000000000000000000000000000000",
    "name": "Cli",
    "manifestFile": "lake-manifest.json",
    "inputRev": null,
    "inherited": false,
    "configFile": "lakefile.toml"
  }],
  "name": "myTool",
  "lakeDir": ".lake",
  "fixedToolchain": false
}
```

This manifest would instruct Lake to download the `Cli` package from the indicated GitHub URL when building this tool.
However, the restricted environment does not have network access, so the build will fail unless Lake uses a local copy instead.
This can be done with the following {tech}[package overrides] file:

```lakePackageOverrides
{
  "version": "1.2.0",
  "packages": [{
    "type": "path",
    "dir": "/etc/lean-packages/Cli",
    "name": "Cli",
    "manifestFile": "lake-manifest.json",
    "inherited": false,
    "configFile": "lakefile.toml"
  }]
}
```

With this, Lake will instead resolve the `Cli` dependency to the local package located at the path `/etc/lean-packages/Cli`.

:::
