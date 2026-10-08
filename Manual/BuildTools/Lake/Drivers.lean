/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
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

#doc (Manual) "Test and Lint Drivers" =>
%%%
tag := "test-lint-drivers"
%%%

A {deftech}_test driver_ runs the tests for a package.
It can be an executable target, a {tech}[Lake script], or a library.
Lake itself isn't a test framework: the {lake}`test` command just locates the configured target, builds it, and (for executables and scripts) runs it.
Library drivers are exercised purely by elaboration, so they aren't run as a separate step.
Assertions, test discovery, and reporting are up to the target itself, whether that's a third-party testing library or hand-written checks.

For executables and scripts, Lake treats a nonzero exit code as a test failure.
For libraries, any elaboration error counts as a test failure, including failures of {keyword}`#guard`-style commands.

A {deftech}_lint driver_ is similar, but it's run by {lake}`lint` and checks the package for stylistic issues and other problems that aren't _errors_ but indicate likely problems.
Lint drivers can only be executables or scripts, not libraries.

# Configuring a Test Driver
%%%
tag := "lake-test-driver-config"
%%%

In a `lakefile.toml`, set {tomlField Lake.PackageConfig}`testDriver` to the name of an executable target, library target, or script defined in the same configuration:

:::::example "Test Driver (`lakefile.toml`)"

::::lakeToml Lake.PackageConfig _root_
```toml
name = "my-package"
testDriver = "my-package-tests"

[[lean_exe]]
name = "my-package-tests"
root = "Tests"
```
```expected
{wsIdx := 0,
  baseName := `«my-package»,
  keyName := `«my-package»,
  origName := `«my-package»,
  dir := FilePath.mk ".",
  relDir := FilePath.mk ".",
  config :=
    {toWorkspaceConfig := { packagesDir := FilePath.mk ".lake/packages" },
      toLeanConfig :=
        { buildType := Lake.BuildType.release,
          leanOptions := #[],
          moreLeanArgs := #[],
          weakLeanArgs := #[],
          moreLeancArgs := #[],
          moreServerOptions := #[],
          weakLeancArgs := #[],
          moreLinkObjs := #[],
          moreLinkLibs := #[],
          moreLinkArgs := #[],
          weakLinkArgs := #[],
          backend := Lake.Backend.default,
          platformIndependent := none,
          precompileImports := false,
          dynlibs := #[],
          plugins := #[],
          requiresModuleSystem := false,
          allowNonModules := false },
      bootstrap := false,
      extraDepTargets := #[],
      precompileModules := false,
      moreGlobalServerArgs := #[],
      srcDir := FilePath.mk ".",
      buildDir := FilePath.mk ".lake/build",
      leanLibDir := FilePath.mk "lib/lean",
      nativeLibDir := FilePath.mk "lib",
      binDir := FilePath.mk "bin",
      irDir := FilePath.mk "ir",
      releaseRepo := none,
      buildArchive := ELIDED,
      preferReleaseBuild := false,
      testDriver := "my-package-tests",
      testDriverArgs := #[],
      lintDriver := "",
      lintDriverArgs := #[],
      version := { toSemVerCore := { major := 0, minor := 0, patch := 0 }, specialDescr := "" },
      versionTags := { filter := #<fun>, name := `default, descr? := none},
      description := "",
      keywords := #[],
      homepage := "",
      license := "",
      licenseFiles := #[FilePath.mk "LICENSE"],
      readmeFile := FilePath.mk "README.md",
      reservoir := true,
      enableArtifactCache? := none,
      restoreAllArtifacts? := none,
      libPrefixOnWindows := false,
      allowImportAll := false,
      builtinLint? := none,
      checks := #[],
      fixedToolchain := false},
  configFile := FilePath.mk "lakefile",
  relConfigFile := FilePath.mk "lakefile",
  relManifestFile := FilePath.mk "lake-manifest.json",
  scope := "",
  remoteUrl := "",
  depConfigs := #[],
  depIdxs := #[],
  depPkgs := #[],
  targetDecls :=
    #[{toConfigDecl :=
          {pkg := `«my-package»,
            name := `«my-package-tests»,
            kind := `lean_exe,
            config :=
              {toLeanConfig :=
                  { buildType := Lake.BuildType.release,
                    leanOptions := #[],
                    moreLeanArgs := #[],
                    weakLeanArgs := #[],
                    moreLeancArgs := #[],
                    moreServerOptions := #[],
                    weakLeancArgs := #[],
                    moreLinkObjs := #[],
                    moreLinkLibs := #[],
                    moreLinkArgs := #[],
                    weakLinkArgs := #[],
                    backend := Lake.Backend.default,
                    platformIndependent := none,
                    precompileImports := false,
                    dynlibs := #[],
                    plugins := #[],
                    requiresModuleSystem := false,
                    allowNonModules := false },
                srcDir := FilePath.mk ".",
                root := `Tests,
                exeName := "my-package-tests",
                needs := #[],
                extraDepTargets := #[],
                supportInterpreter := false,
                nativeFacets := #<fun>},
            wf_data := …},
        pkg_eq := …}],
  targetDeclMap :=
    {`«my-package-tests» ↦
        {toPConfigDecl :=
            {toConfigDecl :=
                {pkg := `«my-package»,
                  name := `«my-package-tests»,
                  kind := `lean_exe,
                  config :=
                    {toLeanConfig :=
                        { buildType := Lake.BuildType.release,
                          leanOptions := #[],
                          moreLeanArgs := #[],
                          weakLeanArgs := #[],
                          moreLeancArgs := #[],
                          moreServerOptions := #[],
                          weakLeancArgs := #[],
                          moreLinkObjs := #[],
                          moreLinkLibs := #[],
                          moreLinkArgs := #[],
                          weakLinkArgs := #[],
                          backend := Lake.Backend.default,
                          platformIndependent := none,
                          precompileImports := false,
                          dynlibs := #[],
                          plugins := #[],
                          requiresModuleSystem := false,
                          allowNonModules := false },
                      srcDir := FilePath.mk ".",
                      root := `Tests,
                      exeName := "my-package-tests",
                      needs := #[],
                      extraDepTargets := #[],
                      supportInterpreter := false,
                      nativeFacets := #<fun>},
                  wf_data := …},
              pkg_eq := …},
          name_eq := …},
      },
  defaultTargets := #[],
  scripts := {},
  defaultScripts := #[],
  postUpdateHooks := #[],
  buildArchive := ELIDED,
  testDriver := "my-package-tests",
  lintDriver := ""}
```
::::
:::::

In a `lakefile.lean`, either set the {name Lake.Package.testDriver}`testDriver` field on the {keyword}`package` declaration (as above), or tag a script, executable, or library declaration with the {attr}`test_driver` attribute.
The attribute form is often convenient because it places the marker next to the target.

:::::example "Test Driver (`lakefile.lean`)"

::::lakeLean
```lean
import Lake
open Lake DSL

package «my-package» where
  testDriver := "my-package-tests"

lean_exe «my-package-tests» where
  root := `Tests
```
```expected
{wsIdx := 0,
  baseName := `«my-package»,
  keyName := Lean.Name.mkNum `«my-package» 0,
  origName := `«my-package»,
  dir := FilePath.mk ".",
  relDir := FilePath.mk ".",
  config :=
    {toWorkspaceConfig := { packagesDir := FilePath.mk ".lake/packages" },
      toLeanConfig :=
        { buildType := Lake.BuildType.release,
          leanOptions := #[],
          moreLeanArgs := #[],
          weakLeanArgs := #[],
          moreLeancArgs := #[],
          moreServerOptions := #[],
          weakLeancArgs := #[],
          moreLinkObjs := #[],
          moreLinkLibs := #[],
          moreLinkArgs := #[],
          weakLinkArgs := #[],
          backend := Lake.Backend.default,
          platformIndependent := none,
          precompileImports := false,
          dynlibs := #[],
          plugins := #[],
          requiresModuleSystem := false,
          allowNonModules := false },
      bootstrap := false,
      extraDepTargets := #[],
      precompileModules := false,
      moreGlobalServerArgs := #[],
      srcDir := FilePath.mk ".",
      buildDir := FilePath.mk ".lake/build",
      leanLibDir := FilePath.mk "lib/lean",
      nativeLibDir := FilePath.mk "lib",
      binDir := FilePath.mk "bin",
      irDir := FilePath.mk "ir",
      releaseRepo := none,
      buildArchive := ELIDED,
      preferReleaseBuild := false,
      testDriver := "my-package-tests",
      testDriverArgs := #[],
      lintDriver := "",
      lintDriverArgs := #[],
      version := { toSemVerCore := { major := 0, minor := 0, patch := 0 }, specialDescr := "" },
      versionTags := { filter := #<fun>, name := `default, descr? := none},
      description := "",
      keywords := #[],
      homepage := "",
      license := "",
      licenseFiles := #[FilePath.mk "LICENSE"],
      readmeFile := FilePath.mk "README.md",
      reservoir := true,
      enableArtifactCache? := none,
      restoreAllArtifacts? := none,
      libPrefixOnWindows := false,
      allowImportAll := false,
      builtinLint? := none,
      checks := #[],
      fixedToolchain := false},
  configFile := FilePath.mk "lakefile.lean",
  relConfigFile := FilePath.mk "lakefile.lean",
  relManifestFile := FilePath.mk "lake-manifest.json",
  scope := "",
  remoteUrl := "",
  depConfigs := #[],
  depIdxs := #[],
  depPkgs := #[],
  targetDecls :=
    #[{toConfigDecl :=
          {pkg := Lean.Name.mkNum `«my-package» 0,
            name := `«my-package-tests»,
            kind := `lean_exe,
            config :=
              {toLeanConfig :=
                  { buildType := Lake.BuildType.release,
                    leanOptions := #[],
                    moreLeanArgs := #[],
                    weakLeanArgs := #[],
                    moreLeancArgs := #[],
                    moreServerOptions := #[],
                    weakLeancArgs := #[],
                    moreLinkObjs := #[],
                    moreLinkLibs := #[],
                    moreLinkArgs := #[],
                    weakLinkArgs := #[],
                    backend := Lake.Backend.default,
                    platformIndependent := none,
                    precompileImports := false,
                    dynlibs := #[],
                    plugins := #[],
                    requiresModuleSystem := false,
                    allowNonModules := false },
                srcDir := FilePath.mk ".",
                root := `Tests,
                exeName := "my-package-tests",
                needs := #[],
                extraDepTargets := #[],
                supportInterpreter := false,
                nativeFacets := #<fun>},
            wf_data := …},
        pkg_eq := …}],
  targetDeclMap :=
    {`«my-package-tests» ↦
        {toPConfigDecl :=
            {toConfigDecl :=
                {pkg := Lean.Name.mkNum `«my-package» 0,
                  name := `«my-package-tests»,
                  kind := `lean_exe,
                  config :=
                    {toLeanConfig :=
                        { buildType := Lake.BuildType.release,
                          leanOptions := #[],
                          moreLeanArgs := #[],
                          weakLeanArgs := #[],
                          moreLeancArgs := #[],
                          moreServerOptions := #[],
                          weakLeancArgs := #[],
                          moreLinkObjs := #[],
                          moreLinkLibs := #[],
                          moreLinkArgs := #[],
                          weakLinkArgs := #[],
                          backend := Lake.Backend.default,
                          platformIndependent := none,
                          precompileImports := false,
                          dynlibs := #[],
                          plugins := #[],
                          requiresModuleSystem := false,
                          allowNonModules := false },
                      srcDir := FilePath.mk ".",
                      root := `Tests,
                      exeName := "my-package-tests",
                      needs := #[],
                      extraDepTargets := #[],
                      supportInterpreter := false,
                      nativeFacets := #<fun>},
                  wf_data := …},
              pkg_eq := …},
          name_eq := …},
      },
  defaultTargets := #[],
  scripts := {},
  defaultScripts := #[],
  postUpdateHooks := #[],
  buildArchive := ELIDED,
  testDriver := "my-package-tests",
  lintDriver := ""}
```
::::
:::::

Only one declaration per package can be tagged with {attr}`test_driver`.
It is an error to use both the {attr}`test_driver` attribute and a non-empty {name Lake.Package.testDriver}`testDriver` field in the same Lake configuration file.

A test driver may also be a target in a package dependency that is transitively {tech (key:="require")}[required].
To use a target from another package, use `<pkg>/<name>` as the value of `testDriver`, where `<pkg>` is the name of the package in which the target is found..

# Running Tests
%%%
tag := "lake-test-running"
%%%

The {lake}`test` command runs the configured driver for the {tech}[root package] only.
Test drivers for dependencies are not run.

:::paragraph
If the test driver is an executable or a script, Lake passes the arguments from {tomlField Lake.PackageConfig}`testDriverArgs` first, then anything after `--` on the command line.
For example,

```
lake test -- --filter Foo --verbose
```

passes `--filter Foo --verbose` to the driver after whatever {tomlField Lake.PackageConfig}`testDriverArgs` is already configured.
Lake builds executable drivers before running them.
:::

If the test driver is a library, arguments are not accepted.
Lake reports an error if {tomlField Lake.PackageConfig}`testDriverArgs` is non-empty or if any arguments follow `--`.
To run the tests, the library is just {tech (key:="Lean elaborator")}[elaborated].

{lake}`check-test` terminates with exit code 0 (that is, successfully) if a test driver is configured for the root package.
It doesn't check that the named target actually exists.

# Lint Drivers
%%%
tag := "lake-lint-drivers"
%%%

Lint drivers are configured and run similarly to {ref "lake-test-driver-config"}[test drivers].
The Lake configuration file specifies a target that serves as the lint driver, and {lake}`lint` runs it.
This target must be an executable or a script; unlike test drivers, lint drivers may not be libraries.

In a TOML-format Lake configuration file, the package-level field {tomlField Lake.PackageConfig}`lintDriver` specifies the name of the lint driver target.

:::::example "Lint Driver (`lakefile.toml`)"
This minimal `lakefile.toml` configures a lint driver:

::::lakeToml Lake.PackageConfig _root_
```toml
name = "my-package"
lintDriver = "my-package-lint"

[[lean_exe]]
name = "my-package-lint"
root = "Lint"
```
```expected
{wsIdx := 0,
  baseName := `«my-package»,
  keyName := `«my-package»,
  origName := `«my-package»,
  dir := FilePath.mk ".",
  relDir := FilePath.mk ".",
  config :=
    {toWorkspaceConfig := { packagesDir := FilePath.mk ".lake/packages" },
      toLeanConfig :=
        { buildType := Lake.BuildType.release,
          leanOptions := #[],
          moreLeanArgs := #[],
          weakLeanArgs := #[],
          moreLeancArgs := #[],
          moreServerOptions := #[],
          weakLeancArgs := #[],
          moreLinkObjs := #[],
          moreLinkLibs := #[],
          moreLinkArgs := #[],
          weakLinkArgs := #[],
          backend := Lake.Backend.default,
          platformIndependent := none,
          precompileImports := false,
          dynlibs := #[],
          plugins := #[],
          requiresModuleSystem := false,
          allowNonModules := false },
      bootstrap := false,
      extraDepTargets := #[],
      precompileModules := false,
      moreGlobalServerArgs := #[],
      srcDir := FilePath.mk ".",
      buildDir := FilePath.mk ".lake/build",
      leanLibDir := FilePath.mk "lib/lean",
      nativeLibDir := FilePath.mk "lib",
      binDir := FilePath.mk "bin",
      irDir := FilePath.mk "ir",
      releaseRepo := none,
      buildArchive := ELIDED,
      preferReleaseBuild := false,
      testDriver := "",
      testDriverArgs := #[],
      lintDriver := "my-package-lint",
      lintDriverArgs := #[],
      version := { toSemVerCore := { major := 0, minor := 0, patch := 0 }, specialDescr := "" },
      versionTags := { filter := #<fun>, name := `default, descr? := none},
      description := "",
      keywords := #[],
      homepage := "",
      license := "",
      licenseFiles := #[FilePath.mk "LICENSE"],
      readmeFile := FilePath.mk "README.md",
      reservoir := true,
      enableArtifactCache? := none,
      restoreAllArtifacts? := none,
      libPrefixOnWindows := false,
      allowImportAll := false,
      builtinLint? := none,
      checks := #[],
      fixedToolchain := false},
  configFile := FilePath.mk "lakefile",
  relConfigFile := FilePath.mk "lakefile",
  relManifestFile := FilePath.mk "lake-manifest.json",
  scope := "",
  remoteUrl := "",
  depConfigs := #[],
  depIdxs := #[],
  depPkgs := #[],
  targetDecls :=
    #[{toConfigDecl :=
          {pkg := `«my-package»,
            name := `«my-package-lint»,
            kind := `lean_exe,
            config :=
              {toLeanConfig :=
                  { buildType := Lake.BuildType.release,
                    leanOptions := #[],
                    moreLeanArgs := #[],
                    weakLeanArgs := #[],
                    moreLeancArgs := #[],
                    moreServerOptions := #[],
                    weakLeancArgs := #[],
                    moreLinkObjs := #[],
                    moreLinkLibs := #[],
                    moreLinkArgs := #[],
                    weakLinkArgs := #[],
                    backend := Lake.Backend.default,
                    platformIndependent := none,
                    precompileImports := false,
                    dynlibs := #[],
                    plugins := #[],
                    requiresModuleSystem := false,
                    allowNonModules := false },
                srcDir := FilePath.mk ".",
                root := `Lint,
                exeName := "my-package-lint",
                needs := #[],
                extraDepTargets := #[],
                supportInterpreter := false,
                nativeFacets := #<fun>},
            wf_data := …},
        pkg_eq := …}],
  targetDeclMap :=
    {`«my-package-lint» ↦
        {toPConfigDecl :=
            {toConfigDecl :=
                {pkg := `«my-package»,
                  name := `«my-package-lint»,
                  kind := `lean_exe,
                  config :=
                    {toLeanConfig :=
                        { buildType := Lake.BuildType.release,
                          leanOptions := #[],
                          moreLeanArgs := #[],
                          weakLeanArgs := #[],
                          moreLeancArgs := #[],
                          moreServerOptions := #[],
                          weakLeancArgs := #[],
                          moreLinkObjs := #[],
                          moreLinkLibs := #[],
                          moreLinkArgs := #[],
                          weakLinkArgs := #[],
                          backend := Lake.Backend.default,
                          platformIndependent := none,
                          precompileImports := false,
                          dynlibs := #[],
                          plugins := #[],
                          requiresModuleSystem := false,
                          allowNonModules := false },
                      srcDir := FilePath.mk ".",
                      root := `Lint,
                      exeName := "my-package-lint",
                      needs := #[],
                      extraDepTargets := #[],
                      supportInterpreter := false,
                      nativeFacets := #<fun>},
                  wf_data := …},
              pkg_eq := …},
          name_eq := …},
      },
  defaultTargets := #[],
  scripts := {},
  defaultScripts := #[],
  postUpdateHooks := #[],
  buildArchive := ELIDED,
  testDriver := "",
  lintDriver := "my-package-lint"}
```
::::
:::::


In a `lakefile.lean`, either set the {name Lake.Package.lintDriver}`lintDriver` field on the {keyword}`package` declaration, or tag a script or executable declaration with the {attr}`lint_driver` attribute.
The attribute form is often convenient because it places the marker next to the target.

:::::example "Lint Driver (`lakefile.lean`)"

::::lakeLean
```lean
import Lake
open Lake DSL

package «my-package» where
  lintDriver := "my-package-lint"

lean_exe «my-package-lint» where
  root := `Lint
```
```expected
{wsIdx := 0,
  baseName := `«my-package»,
  keyName := Lean.Name.mkNum `«my-package» 0,
  origName := `«my-package»,
  dir := FilePath.mk ".",
  relDir := FilePath.mk ".",
  config :=
    {toWorkspaceConfig := { packagesDir := FilePath.mk ".lake/packages" },
      toLeanConfig :=
        { buildType := Lake.BuildType.release,
          leanOptions := #[],
          moreLeanArgs := #[],
          weakLeanArgs := #[],
          moreLeancArgs := #[],
          moreServerOptions := #[],
          weakLeancArgs := #[],
          moreLinkObjs := #[],
          moreLinkLibs := #[],
          moreLinkArgs := #[],
          weakLinkArgs := #[],
          backend := Lake.Backend.default,
          platformIndependent := none,
          precompileImports := false,
          dynlibs := #[],
          plugins := #[],
          requiresModuleSystem := false,
          allowNonModules := false },
      bootstrap := false,
      extraDepTargets := #[],
      precompileModules := false,
      moreGlobalServerArgs := #[],
      srcDir := FilePath.mk ".",
      buildDir := FilePath.mk ".lake/build",
      leanLibDir := FilePath.mk "lib/lean",
      nativeLibDir := FilePath.mk "lib",
      binDir := FilePath.mk "bin",
      irDir := FilePath.mk "ir",
      releaseRepo := none,
      buildArchive := ELIDED,
      preferReleaseBuild := false,
      testDriver := "",
      testDriverArgs := #[],
      lintDriver := "my-package-lint",
      lintDriverArgs := #[],
      version := { toSemVerCore := { major := 0, minor := 0, patch := 0 }, specialDescr := "" },
      versionTags := { filter := #<fun>, name := `default, descr? := none},
      description := "",
      keywords := #[],
      homepage := "",
      license := "",
      licenseFiles := #[FilePath.mk "LICENSE"],
      readmeFile := FilePath.mk "README.md",
      reservoir := true,
      enableArtifactCache? := none,
      restoreAllArtifacts? := none,
      libPrefixOnWindows := false,
      allowImportAll := false,
      builtinLint? := none,
      checks := #[],
      fixedToolchain := false},
  configFile := FilePath.mk "lakefile.lean",
  relConfigFile := FilePath.mk "lakefile.lean",
  relManifestFile := FilePath.mk "lake-manifest.json",
  scope := "",
  remoteUrl := "",
  depConfigs := #[],
  depIdxs := #[],
  depPkgs := #[],
  targetDecls :=
    #[{toConfigDecl :=
          {pkg := Lean.Name.mkNum `«my-package» 0,
            name := `«my-package-lint»,
            kind := `lean_exe,
            config :=
              {toLeanConfig :=
                  { buildType := Lake.BuildType.release,
                    leanOptions := #[],
                    moreLeanArgs := #[],
                    weakLeanArgs := #[],
                    moreLeancArgs := #[],
                    moreServerOptions := #[],
                    weakLeancArgs := #[],
                    moreLinkObjs := #[],
                    moreLinkLibs := #[],
                    moreLinkArgs := #[],
                    weakLinkArgs := #[],
                    backend := Lake.Backend.default,
                    platformIndependent := none,
                    precompileImports := false,
                    dynlibs := #[],
                    plugins := #[],
                    requiresModuleSystem := false,
                    allowNonModules := false },
                srcDir := FilePath.mk ".",
                root := `Lint,
                exeName := "my-package-lint",
                needs := #[],
                extraDepTargets := #[],
                supportInterpreter := false,
                nativeFacets := #<fun>},
            wf_data := …},
        pkg_eq := …}],
  targetDeclMap :=
    {`«my-package-lint» ↦
        {toPConfigDecl :=
            {toConfigDecl :=
                {pkg := Lean.Name.mkNum `«my-package» 0,
                  name := `«my-package-lint»,
                  kind := `lean_exe,
                  config :=
                    {toLeanConfig :=
                        { buildType := Lake.BuildType.release,
                          leanOptions := #[],
                          moreLeanArgs := #[],
                          weakLeanArgs := #[],
                          moreLeancArgs := #[],
                          moreServerOptions := #[],
                          weakLeancArgs := #[],
                          moreLinkObjs := #[],
                          moreLinkLibs := #[],
                          moreLinkArgs := #[],
                          weakLinkArgs := #[],
                          backend := Lake.Backend.default,
                          platformIndependent := none,
                          precompileImports := false,
                          dynlibs := #[],
                          plugins := #[],
                          requiresModuleSystem := false,
                          allowNonModules := false },
                      srcDir := FilePath.mk ".",
                      root := `Lint,
                      exeName := "my-package-lint",
                      needs := #[],
                      extraDepTargets := #[],
                      supportInterpreter := false,
                      nativeFacets := #<fun>},
                  wf_data := …},
              pkg_eq := …},
          name_eq := …},
      },
  defaultTargets := #[],
  scripts := {},
  defaultScripts := #[],
  postUpdateHooks := #[],
  buildArchive := ELIDED,
  testDriver := "",
  lintDriver := "my-package-lint"}
```
::::
:::::

Only one declaration per package can be tagged with {attr}`lint_driver`.
It is an error to use both the {attr}`lint_driver` attribute and a non-empty {name Lake.Package.lintDriver}`lintDriver` field in the same Lake configuration file.

:::lakeSession -show
```lean +lakefile
import Lake
open Lake DSL
package p

@[lint_driver]
lean_exe Foo where

@[lint_driver]
lean_exe Bar where
```
```lakeCmd "lake build" +error
error: p: only one script or executable can be tagged @[lint_driver]
```
:::

A lint driver in a dependency package can be referenced with the same `<pkg>/<name>` syntax used for test drivers.

{lake}`lint` runs the configured driver, passing {tomlField Lake.PackageConfig}`lintDriverArgs` first, then anything after `--` on the command line:

```
lake lint -- --warnings-as-errors
```

Lake also has a separate {deftech}_builtin linter_ that operates on Lean modules directly, independent of any configured driver.
Builtin linting is enabled by the `--builtin-lint` and related flags (see {lake}`lint`), or by setting {tomlField Lake.PackageConfig}`builtinLint` to `true` in the package configuration.
When builtin linting is active, positional `MODULE` arguments before `--` select which modules to lint, and they are _not_ passed to the configured driver.
So `lake lint Mathlib` triggers builtin linting on `Mathlib`, whereas `lake lint -- Mathlib` passes `Mathlib` to the driver.
The two mechanisms are independent and can run together: when both apply, Lake runs the builtin linter first and then the driver.

{lake}`check-lint` exits with code 0 (that is, successfully) if a lint driver is configured for the root package or if {tomlField Lake.PackageConfig}`builtinLint` is set to `true` in its configuration.
