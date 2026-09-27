/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Linter.CodeQuality
import Lean.Linter.EnvLinter

import Manual.Meta

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

open Verso.Code.External

#doc (Manual) "Linters and Code Quality" =>
%%%
tag := "linters"
shortContextTitle := "Linters"
draft := true
%%%

A {deftech}[linter] is a check that identifies problematic or error-prone patterns in code.
Linters can also be used to enforce project-specific standards for documentation, code style, or file structure.
Lean includes a number of linters, along with a framework for defining custom linters and extracting metrics from them.

{ref "linters-editor"}[Linters] are useful for individuals working on small problems in order to catch mistakes early.
For larger problems or groups working together, configuring the different kinds of available {ref "linting-workflows"}[linter workflows] allow the team to improve their collaboration.
As a projects needs evolve, it may even become necessary to write {ref "implementing-linters"}[custom linters].

# Linters and Warnings
%%%
tag := "linters-editor"
%%%

When using Lean interactively, linters are run after each {tech}[command] is {tech (key := "Lean elaborator")}[elaborated].
Linters run on a separate thread, so their warnings may arrive after the command has been processed and elaboration has proceeded to the next command.

:::paragraph
Linter warnings have a standarized format.
Each ends with instructions for disabling the linter.
For example, the unused variable linter issues a warning on this code:
```lean (name := lintWarn)
example :=
  let y := 2
  "hello"
```
The warning explains that {option}`linter.unusedVariables` can be used to disable it:
```leanOutput lintWarn (severity := Lean.MessageSeverity.warning)
Variable name `y` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _y

Note: This linter can be disabled with `set_option linter.unusedVariables false`
```
Setting the option as instructed disables the linter:
```lean
set_option linter.unusedVariables false in
example :=
  let y := 2
  "hello"
```
:::

:::paragraph
Linter options can be set in three scopes:

: Command scope

  Use {keywordOf Lean.Parser.Command.set_option}`set_option`{lit}` linter.x ... `{keywordOf Lean.Parser.Command.in}`in`{lit}` ...` to enable or disable a linter in single command.

: Section scope

  The {keywordOf Lean.Parser.Command.set_option}`set_option` command can be used to enable or disable a linter for the remainder of the current {tech}[section scope].

: Package scope

  Lean options, including linter options, can be set in the {tomlField Lake.PackageConfig}`leanOptions` field in a {ref "lake-config"}[Lake configuration file].
:::

Linters are organized into {deftech}_linter sets_.
All the linters in a set may be enabled together with a single option.
Linters may be a part of arbitrarily many linter sets, and they are enabled if any of their sets are enabled.

Whether a given linter is enabled is determined by multiple options.
Even though every option has a default value, Lean still tracks whether they've been explicitly set.
If the linter's own option has been set, then that value is used.
If the linter's option has not been set, but {option}`linter.all` has been, then its value is used.
If neither the linter's own option nor {option}`linter.all` has been set, then the linter is enabled if its default value is {name}`true` or if any linter set that contains it has been explicitly enabled.

There are a few consequences of this prioritization.
First, linter sets can only ever enable linters, not disable them.
Setting a linter set's option to {lean}`false` has no effect.
Second, setting {option}`linter.all` to either {name}`true` or {name}`false` takes precedence over all linter sets.
{option}`linter.all` also takes precendece over a linter option's default value, but not over an explicit value.

{optionDocs linter.all}

{optionDocs linter.extra}

{optionDocs linter.coreInternal}

# Linting Workflows
%%%
tag := "linting-workflows"
%%%

In addition to providing feedback on individual commands while a module is under development, linters can be applied at the package level.
When modules are elaborated, their linter warnings are stored in their {tech}[`.olean` files] for replay.
In addition to collecting these interactive results, linting a package provides the opportunity to run {deftech}_environment linters_, which are linters that report potential problems in a the environment that results from importing a collection of modules, rather than in source files themselves.

## Kinds of Linters
%%%
tag := "kinds-of-linters"
%%%

Linters run in two contexts:
: Interactive linters

  These linters are run in the context of the Lean elaborator and language server while checking a single Lean file.
  Lean invokes these linters when the corresponding options are enabled.

: Environment linters

  These linters are run after a collection of modules have been built, in an environment that results from importing their modules.
  Environment linters are only invoked by {lake}`lint`.

:::paragraph
There are three kinds of interactive linters:

: Command linters

  Command linters are run once for each top-level command.

: Module linters

  Module linters are run at the end of the module.

: Stateful linters

  Stateful linters are a special kind of command linter that can modify a shared state from one command to the next.
  They can be used to enforce non-local invariants, such as those governing file structure, while still providing feedback before the entire file has elaborated.
:::


## Running `lake lint`
%%%
tag := "running-lake-lint"
%%%

Linting via {lake}`lint` can invoke either the current project's {tech}[lint driver], Lake's built-in support for linting, or both.
The linters described in this chapter are built-in; a lint driver is a way to run additional linting tools that do not fit this paradigm.
Built-in linting occurs when {tomlField Lake.PackageConfig}`builtinLint` is {lean}`true` in the Lake configuration or when the {lakeOpt}`--builtin-lint` or {lakeOpt}`--builtin-only` command-line options are passed to {lake}`lint`.

The {lakeOptDef option}`--linters` and {lakeOptDef option}`--lint-only` options take a comma-separated list of linter option names.
{lakeOpt}`--linters` sets the indicated linter options, while {lakeOpt}`--lint-only` also disables all other linters.
Within this list, a `-` prefix disables the linter and a leading period abbreviates `linter.`, so `.XYZ` is equivalent to `linter.XYZ`.
Later entries take precedence over earlier entries.
Positional module arguments restrict built-in linting to the indicated modules; otherwise, linting begins at the module roots of all default targets.
The {lakeOptDef flag}`--record-exceptions` flag causes {keywordOf Lean.Parser.Command.set_option}`set_option` commands to be added to files to suppress warnings.


## Environment Linters and the Import Hierarchy
%%%
tag := "env-linters-imports"
%%%

Environment linters typically consist of two modules.
One module defines the linter's option, and it must be imported by every module that will be checked with the linter.
Modules that don't transitively import the linter's option are not checked.
This allows the modules to override the linter option's value as needed.
The other module defines the linter itself; this module only needs to be imported publicly by the root module from which linting is initiated.
The environment linter runs only when it is transitively imported by the root module, but it can be applied to code in modules that the linter itself imports.
Only modules that share a prefix with the root module are linted.

## Code Quality Metrics
%%%
tag := "code-quality-metrics"
%%%

In addition to emitting warnings, linters can save {deftech}_code quality metrics_, which are named values that are associated either with a module or with a particular declaration.
The values may be either {name}`Float` or mappings from {name}`String` to {name}`Float`, and arbitrarily many values with a given name may be associated with a module or declaration.
These associations are referred to as {deftech (key := "code quality metric entry")}_entries_.

Every linter is already implicitly a metric.
The metric's name is the linter option's name, and the metric's value is the number of times that the linter's warning was issued in a given module.

Code quality metrics are emitted in JSON format and can be processed by arbitrary scripts.
For example, they can be used to track the number of linter warnings in a codebase over time, or to ensure that no new lints are introduced in a change.
Custom metrics can be used to track features such as the number of times each {tactic}`simp` lemma is used, making it easier to gain insights into a codebase that are not immediately available by inspecting the code itself.

:::paragraph
When {lake}`lint` is run with the {lakeOpt}`--code-quality` flag, it emits a JSON representation of the metrics entries to standard output as a sequence of JSON objects.
The {tech}[lint driver] is skipped.
Each entry is an object with three fields:

* `name` contains the metric name,
* `value` contains the metric value, as a single-field object whose key name determines the field's interpretation,
* `source` contains the location for which the metric was saved, also as a single-field object.

Metric values contain either the key `scalar` with a numeric value or the key `dict` with an object that maps arbitrary strings to numbers.
Sources are either the key `module` with an object that maps `name` to a string or the key `declaration` together with an object that maps `module` and `name` to strings.
The JSON output may include newlines, and should be parsed with an actual JSON parser.
:::

:::example "Metrics Entries as JSON"
A scalar value attributed to a module, as produced for replayed linter warnings:
```codeQualityEntries
{"name": "linter.unusedVariables",
 "source": {"module": {"name": "Proj.Basic"}},
 "value": {"scalar": {"value": 2}}}
```

A dictionary value attributed to a declaration, as logged by a linter:
```codeQualityEntries
{"name": "linter.simpUsage.lemmas",
 "source": {"declaration": {"module": "Proj.Lemmas", "name": "t3"}},
 "value": {"dict": {"dictionary": {"Nat.add_zero": 1, "Nat.zero_add": 1}}}}
```
:::



When {lake}`lint` is run with the {lakeOpt}`--code-quality` flag, it additionally runs the code quality checks specified in the Lake configuration's {tomlField Lake.PackageConfig}`checks` field and on the command line via the {lakeOpt}`--checks` option.
Both the configuration field and the command-line option point at modules; all {ref "package-code-quality-checks"}[registered checks] in all specified modules are run.
These checks are Lean functions that can add additional metrics that require more than a single command or module's state.
Checks can replace _ad hoc_ data collection mechanisms for CI and reporting with a single consistent mechanism.


::::example "Existing Warnings as Metrics" (tag := "example-warnings-as-metrics")
:::lakeSession
```toml -show
name = "metrics"
defaultTargets = ["Code"]

[[lean_lib]]
name = "Code"
```
Without any further configuration, running {lake}`lint` with the {lakeOpt}`--code-quality` flag on a project returns a metric for each linter that tracks the number of warnings it issues in each module.
This module contains two unused variable warnings:
```lean (file := "Code/Basic.lean")
module

public def first (x y : Nat) : Nat := x

public def second (x y : Nat) : Nat := y
```
```lean (file := "Code.lean")
module
public import Code.Basic
```
```lakeCmd "lake build" +ignoreOutput -show
```
Linting the package shows these messages:
```lakeCmd "lake lint --builtin-only" +error
-- Text linter diagnostics in Code.Basic:
⟨project⟩/Code/Basic.lean:3:20: warning: Variable name `y` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _y

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⟨project⟩/Code/Basic.lean:5:19: warning: Variable name `x` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _x

Note: This linter can be disabled with `set_option linter.unusedVariables false`
-- No environment linters were run for Code.
```
The module `Code.Basic` itself is annotated with two instances of {option}`linter.unusedVariables`:
```lakeCmd "lake lint --code-quality"
{"value": {"scalar": {"value": 2}},
 "source": {"module": {"name": "Code.Basic"}},
 "name": "linter.unusedVariables"}
```
:::
::::

# Implementing Linters
%%%
tag := "implementing-linters"
%%%

Many large-scale projects require custom linters that enforce project-specific standards.
The steps for defining a new linter are:
1. Registering an option to control the new linter.
2. Determining whether the linter should be a command linter, module linter, stateful linter, or environment linter.
3. Deciding which code quality metrics, if any, should be saved.
4. Implementing any package-level code quality checks that are needed.

The first step in defining a linter is to register the option that controls it.
Options are registered using {keywordOf Lean.Option.registerOption}`register_option`, which takes a default value and a description for the new option.
The default value determines whether the linter is enabled or disabled by default.
In a module, this option should be both public and in the {tech}[meta phase].
Linters should be controlled by a {name}`Bool` option.
Further options that configure a linter, such as options that set thresholds, may be added within the linter's own namespace.

Linters should use {name Lean.Linter.logLint}`logLint` or {name}`Lean.Linter.logLintIf` instead of {name}`Lean.logWarning` to display lint warnings.
These helpers ensure that the linter warning's message is formatted consistently.
They also internally tag it as a linter message, which causes Lake and Lean to include it in {lake}`lint`'s output.
{name Lean.Linter.logLintIf}`logLintIf` additionally resolves the linter option's value correctly, taking {option}`linter.all` and linter sets into consideration.
{name Lean.Linter.logLint}`logLint` should be used in contexts where the linter's option has already been checked.

Some linters need to check whether they are enabled before they are ready to log a warning.
For example, computationally expensive linters that do not compute any useful code quality metrics may wish to terminate early if they are not enabled.
These linters should check whether they are enabled using helpers that correctly take linter sets and {option}`linter.all` into account.
This is done by first calling {name}`Lean.Linter.getLinterOptions`, and then checking the option's value using {name}`Lean.Linter.getLinterValue`.

Finally, the implementation of each linter should wrap command-specific checks with {name}`Lean.withSetOptionIn`.
Without this wrapper, uses of {keywordOf Lean.Parser.Command.set_option}`set_option`{lit}` ... `{keywordOf Lean.Parser.Command.in}`in`{lit}` ...` around the command being linted are not taken into account.
Command linters and stateful linters should wrap it around their entire implementation, while module linters should wrap operations on single commands.


{docstring Lean.Linter.logLintIf}

{docstring Lean.Linter.logLint +allowMissing}

{docstring Lean.Linter.getLinterValue +allowMissing}

{docstring Lean.Linter.getLinterOptions +allowMissing}

{docstring Lean.withSetOptionIn}

## Command Linters
%%%
tag := "command-linters"
%%%

:::leanSection
```lean -show
open Lean Elab Command
```

Command linters are the simplest form of linter.
A command linter is a value of type {name Lean.Elab.Command.Linter}`Lean.Elab.Command.Linter`, which is a structure with a {name Lean.Elab.Command.Linter.run}`run` field of type {lean}`Syntax → CommandElabM Unit`.
The {name}`addLinter` function saves a new command linter, and must be run in an {keywordOf Lean.Parser.Command.initialize}`initialize` block.
The {keywordOf Lean.Parser.Command.initialize}`initialize` block must be in the {tech}[meta phase] when used in a {tech}[module].

Command linters are run after the elaboration of each command, concurrently with the elaboration of the rest of the file.
The linter's {name Lean.Elab.Command.Linter.run}`run` function is applied to the command's syntax in a context where the command's info tree is available.
Any environment modifications made by the linter are discarded, but new message log entries, code actions, and {ref "code-quality-metrics"}[code quality metrics] are saved.
:::


{docstring Lean.Elab.Command.Linter +allowMissing}

{docstring Lean.Elab.Command.addLinter +allowMissing}


::::example "Counting Tactics" (tag := "example-linter-enabled")
This custom linter issues a warning when the number of tactics in a command exceeds a configurable threshold.
Tactics are found by processing the command's info tree, recording the unique starting positions of {tech}[original] syntax with tactic info whose kind is a tactic kind.
Deduplication is needed because tactic info is saved for macro expansion steps and repeated executions of the same tactic.
The linter terminates early if it is disabled, rather than waiting until it is time to log the message to make the decision.


:::leanModules (moduleRoot := Steps)
```leanModule (moduleName := Steps.Linter)
module
public meta import Lean.Linter.Basic
public meta import Lean.Elab.InfoTree.Util

open Lean Elab Command

meta section

public register_option linter.tacticCount : Bool := {
  defValue := true
  descr := "warn when a command runs many tactics"
}

public register_option linter.tacticCount.max : Nat := {
  defValue := 100
  descr := "the number of tactics a command may run before `linter.tacticCount` warns"
}

/-- Whether `kind` is the syntax kind of a tactic, as opposed to a tactic sequence or block. -/
def isTacticKind (env : Environment) (kind : SyntaxNodeKind) : Bool :=
  match (Parser.parserExtension.getState env).categories.find? `tactic with
  | some category => category.kinds.contains kind
  | none => false

/-- The number of distinct tactics from the source file that were run while elaborating `tree`. -/
def countTactics (env : Environment) (tree : InfoTree) : Nat :=
  let positions : Std.HashSet String.Pos.Raw := tree.foldInfo (init := {}) fun _ info positions =>
    match info with
    | .ofTacticInfo ti =>
      match ti.stx.getHeadInfo, ti.stx.getPos? with
      | .original .., some pos =>
        if isTacticKind env ti.stx.getKind then positions.insert pos else positions
      | _, _ => positions
    | _ => positions
  positions.size

/-- Warns when a command runs more than `linter.tacticCount.max` tactics. -/
def tacticCount : Linter where
  run := withSetOptionIn fun stx => do
    -- Don't compute the result if it will never be shown
    unless Linter.getLinterValue linter.tacticCount (← Linter.getLinterOptions) do return
    let env ← getEnv
    let count := (← getInfoState).trees.foldl (init := 0) fun n t => n + countTactics env t
    let limit := linter.tacticCount.max.get (← getOptions)
    if count > limit then
      Linter.logLint linter.tacticCount stx m!"this command runs {count} tactics, more than {limit}"

initialize addLinter tacticCount
```

This module demonstrates that the linter runs and that it respects locally set options:
```leanModule (moduleName := Steps.Test) (name := tooMany)
module
import Steps.Linter

set_option linter.tacticCount.max 4

theorem short (n : Nat) : n + 0 = n := by
  simp

theorem long (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_add]
    rw [ih]
    rfl

set_option linter.tacticCount false in
theorem silenced (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_add]
    rw [ih]
    rfl
```
```leanOutput tooMany
this command runs 5 tactics, more than 4

Note: This linter can be disabled with `set_option linter.tacticCount false`
```
:::
::::


## Module Linters
%%%
tag := "module-linters"
%%%
:::leanSection
```lean -show
open Lean Elab Command
```
Module linters run after each module's elaboration is completed.
Module linters have type {name}`Lean.Elab.Command.ModuleLinter`, which is a structure with a {name ModuleLinter.run}`run` function of type {lean}`Array Syntax → CommandElabM Unit`.
The function is called on all the top-level commands from the module.
Because the linter is invoked after the whole module is elaborated, its warnings do not appear until the very end of elaboration.

Unlike command linters, module linters do not have access to the commands' info trees and cannot save code actions.
They do, however, have access to the module's final environment.
This means that they are primarily useful for syntactic checks.
If info trees are needed for a whole-file check, consider using a {ref "stateful-linters"}[stateful linter] instead.

The {name}`addModuleLinter` function saves a new module linter, and must be run in an {keywordOf Lean.Parser.Command.initialize}`initialize` block.
The {keywordOf Lean.Parser.Command.initialize}`initialize` block must be in the {tech}[meta phase] when used in a {tech}[module].
:::


{docstring Lean.Elab.Command.ModuleLinter +allowMissing}

{docstring Lean.Elab.Command.addModuleLinter +allowMissing}

::::example "Limiting the Number of Declarations" (tag := "example-module-linter")

:::leanModules (moduleRoot := Limit)
The module `Limit.Linter` contains a module linter that issues a warning when a module contains too many declarations.
The limit is determined by the value of an option.
Even though the warning is attached to the first declaration that exceeds the limit, it does not appear until the entire file is elaborated because it is implemented as a module linter.
```leanModule (moduleName := Limit.Linter)
module
public meta import Lean.Linter.Basic

open Lean Elab Command

meta section

public register_option linter.declarationLimit : Bool := {
  defValue := true
  descr := "warn when a file contains more declarations than `linter.declarationLimit.max`"
}

public register_option linter.declarationLimit.max : Nat := {
  defValue := 200
  descr := "the number of declarations that a file may contain"
}

/-- Warns at the first declaration past the limit. -/
def declarationLimit : ModuleLinter where
  run cmds := do
    let limit := linter.declarationLimit.max.get (← getOptions)
    let decls := cmds.filter (·.isOfKind ``Parser.Command.declaration)
    if h : limit < decls.size then
      Linter.logLintIf linter.declarationLimit decls[limit]
        m!"this file contains {decls.size} declarations, more than {limit}"

initialize addModuleLinter declarationLimit
```
This module sets the maximum declaration count to {lean}`2`:
```leanModule (moduleName := Limit.Test) (name := limitTest)
module
import Limit.Linter

set_option linter.declarationLimit.max 2

def a := 1
def b := 2
def c := 3
```
Building the file demonstrates the linter warning:
```leanOutput limitTest
this file contains 3 declarations, more than 2

Note: This linter can be disabled with `set_option linter.declarationLimit false`
```
:::
::::



## Stateful Linters
%%%
tag := "stateful-linters"
%%%
:::leanSection
```lean -show
open Lean Elab Command
```

Like command linters, stateful linters are invoked after each command is elaborated.
Similarly, they also have access to the command's info tree and environment.
Unlike command linters, they are not independent of the results of linting prior commands.
Instead, they have a state that is accumulated throughout the module.
This provides the opportunity to check non-local properties, while still emitting a warning as soon as the violation has occurred rather than waiting for the rest of the file to be processed.

Furthermore, stateful linters are run in two phases, called the “early” and “late” phases.
After command elaboration is complete, the early phases of all stateful linters are run, followed by all late phases.
This allows cooperation: an early phase might compute data that is used in the late phases of multiple linters.
The early phase is optional, and many useful stateful linters have no early phase.
Stateful linters may read the saved state of any other stateful linter, not just their own, via handles returned by linter registration.

Stateful linters are registered using {name}`Lean.Elab.Command.registerStatefulLinter`.
Like the other linter registration functions, it must be invoked in an {keywordOf Lean.Parser.Command.initialize}`initialize` block in the {tech}[meta phase].
The linter must be public.
The registration function takes the implementations of the early and late phases as arguments.
Unlike the other linter registrations, registration returns a useful value; this value is a handle by which the linter's state can be read.
{name}`StatefulLinter` and {name}`registerStatefulLinter` both take two type parameters; the first is the state that is threaded between commands, the second is the data computed in the early phase.

Stateful linters are also run at the end of the module.
Because they've had the opportunity to collect information from each command, they can provide feedback that module linters cannot.
:::

{docstring Lean.Elab.Command.StatefulLinter}

{docstring Lean.Elab.Command.registerStatefulLinter}

{docstring Lean.Elab.Command.PrevStateFn}

{docstring Lean.Elab.Command.PreStateFn}

::::example "Enforcing a File Layout" (tag := "example-file-layout")
:::leanModules (moduleRoot := Layout)

This stateful linter checks that a module has a particular structure.
It should start with a module docstring, then set any options that are needed, and then finally include declarations.
The linter's state is a simple state machine that tracks this ordering.
When it encounters a command, it checks the invariant locally and updates the state.
```leanModule (moduleName := Layout.Linter)
module
public meta import Lean.Linter.Basic

open Lean Elab Command

meta section

public register_option linter.fileLayout : Bool := {
  defValue := true
  descr := "warn when commands appear out of the expected order in a file"
}

public inductive Region where
  | moduleDoc
  | setup
  | body
deriving Inhabited, Ord, DecidableEq

instance : LT Region := ltOfOrd

def Region.describe : Region → String
  | .moduleDoc => "module docstring"
  | .setup => "setup command"
  | .body => "declaration"

open Parser in
def Region.ofCommand (stx : Syntax) : Option Region :=
  if stx.isOfKind ``Command.moduleDoc then
    some .moduleDoc
  else if stx.isOfKind ``Command.open ||
          stx.isOfKind ``Command.set_option ||
          stx.isOfKind ``Command.universe ||
          stx.isOfKind ``Command.variable then
    some .setup
  else if stx.isOfKind ``Command.declaration then
    some .body
  else
    none

public structure LayoutState where
  current : Option Region := none
deriving Inhabited

def checkLayout (stx : Syntax) (st : LayoutState) : CommandElabM LayoutState := do
  let some region := Region.ofCommand stx | return st
  if let some current := st.current then
    if region < current then
      Linter.logLintIf linter.fileLayout stx
        m!"{region.describe} after {current.describe}"
  else if region != .moduleDoc then
    Linter.logLintIf linter.fileLayout stx
      m!"the first command in a file should be a module docstring"
  let current := st.current.getD region
  return { current := some (if region > current then region else current) }

public initialize fileLayoutLinter : StatefulLinter LayoutState Unit ←
  registerStatefulLinter {} (post := fun stx st _ _ _ => withSetOptionIn (checkLayout · st) stx)
```
This file contains three violations: it begins without a module docstring, it sets an option after a declaration, and it places a module docstring after a command:
```leanModule (moduleName := Layout.Test) (name := ordering)
module
import Layout.Linter

open Nat

/-! This module docstring comes too late. -/

def x := 1

set_option autoImplicit false

theorem y : x = 1 := rfl
```
```leanOutput ordering
the first command in a file should be a module docstring

Note: This linter can be disabled with `set_option linter.fileLayout false`
```
```leanOutput ordering
setup command after declaration

Note: This linter can be disabled with `set_option linter.fileLayout false`
```
```leanOutput ordering
module docstring after setup command

Note: This linter can be disabled with `set_option linter.fileLayout false`
```
:::
::::



## Environment Linters
%%%
tag := "environment-linters"
%%%

Environment linters are run by {lake}`lint` after a project is built when {lakeOpt}`--builtin-lint` is enabled or the {tomlField Lake.PackageConfig}`builtinLint` field is enabled in the Lake configuration.
After Lake builds the project, its built-in linter iterates over each library target's root module, importing the module and then running the configured environment linters on the resulting environment.
Each environment linter consists of a test routine along with success and failure messages.
Unlike command and module linters, environment linters do not need to be transitively imported by the modules that they check.

Like other linters, environment linters are controlled by options.
Unlike the linter itself, the option declaration must be transitively imported.
Options that control environment linters are specially registered, and the values of these options are stored during elaboration so that the linter can retrieve the option values from the imported environment, even those that are locally set using {keywordOf Lean.Parser.Command.in}`in`.

To define an environment linter, do the following:
1. In one module, register a public option in the {tech}[meta phase] that controls the linter.
  In an {keywordOf Lean.Parser.Command.initialize}`initialize` block, run {name Lean.Linter.addEnvLinterOption}`addEnvLinterOption` to instruct Lean to track the option's value during elaboration.
  This module should be transitively imported by every module in which the linter is to be used.
  The initialize block must run in the meta phase.
2. In a second module, define the linter itself.
  Use the {attr}`builtin_env_linter` attribute to associate the linter with the option.
  This module does not need to be imported by a module in order to check it, but it must be transitively imported by the root module of the target being linted.

:::syntax attr (title := "Environment Linters")
```grammar
builtin_env_linter $_:ident
```
Registers an environment linter that is controlled by the indicated option name.
:::

{docstring Lean.Linter.EnvLinter.EnvLinter}

{docstring Lean.Linter.addEnvLinterOption +allowMissing}


::::example "API Completeness Linter" (tag := "example-env-linter")
Generally speaking, a data structure that provides a `get!` function should also provide `get?` and `getD`.
These functions need not be defined in the same module, however.
An environment linter can ensure that every namespace in a project that defines any of these names also defines the others.

:::lakeSession
```toml -show
name = "envlint"
defaultTargets = ["Data"]

[[lean_lib]]
name = "Lints"

[[lean_lib]]
name = "Data"
```
The linter itself consists of two modules: `Lints.Options` defines the option that controls the linter and should be imported by the entire project, while `Lints.GetVariants` only needs to be imported by the root module:
```lean (file := "Lints/Options.lean")
module
public meta import Lean.Linter.Init

open Lean

meta section

public register_option linter.envLinter.getVariants : Bool := {
  defValue := true
  descr := "warn when a namespace defines some but not all of `get!`, `get?`, and `getD`"
}

initialize Linter.addEnvLinterOption linter.envLinter.getVariants
```
```lean (file := "Lints/GetVariants.lean")
module
public import Lints.Options
public meta import Lean.Linter.EnvLinter.Basic

open Lean Linter EnvLinter

meta section

/-- The variants that are expected to be defined together. -/
def getVariants : List String := ["get!", "get?", "getD"]

@[builtin_env_linter linter.envLinter.getVariants]
public def getVariantsLinter : EnvLinter where
  test declName := do
    let .str ns variant := declName | return none
    unless getVariants.contains variant do return none
    let env ← getEnv
    let missing := getVariants.filter fun v => !env.contains (.str ns v)
    if missing.isEmpty then return none
    let missing := missing.map fun v => m!"`{Name.str ns v}`"
    return some m!"`{declName}` is defined, but {MessageData.andList missing} {if missing.length == 1 then "is" else "are"} not"
  noErrorsFound := "Every namespace defines all of `get!`, `get?`, and `getD`."
  errorsFound := "THE FOLLOWING NAMESPACES DEFINE ONLY SOME OF `get!`, `get?`, AND `getD`:"
```
The library itself contains a variety of data structures, with their implementations in multiple modules:
```lean (file := "Data/Stack.lean")
module
import Lints.Options

public structure Stack where
  items : Array Nat

public def Stack.get! (s : Stack) (i : Nat) : Nat := s.items[i]!
```
```lean (file := "Data/Queue.lean")
module
import Lints.Options

public structure Queue where
  items : Array Nat

public def Queue.get! (q : Queue) (i : Nat) : Nat := q.items[i]!
```
```lean (file := "Data/Safe.lean")
module
import Lints.Options
public import Data.Stack

public def Stack.get? (s : Stack) (i : Nat) : Option Nat := s.items[i]?

public def Stack.getD (s : Stack) (i : Nat) (default : Nat) : Nat := s.items.getD i default
```
The root module imports all the implementation modules along with the linter:
```lean (file := "Data.lean")
module
public import Lints.GetVariants
public import Data.Stack
public import Data.Queue
public import Data.Safe
```
```lakeCmd "lake build" +ignoreOutput -show
```
Linting the package returns the following warnings:
```lakeCmd "lake lint --builtin-only" +error
-- Found 1 error in 12 declarations (plus 24 automatically generated ones) in Data with 1 linters

/- The `linter.envLinter.getVariants` linter reports:
THE FOLLOWING NAMESPACES DEFINE ONLY SOME OF `get!`, `get?`, AND `getD`: -/
-- Data.Queue
./Data/Queue.lean:7:1: error: Queue.get! `Queue.get!` is defined, but `Queue.get?` and `Queue.getD` are not
```
:::
::::

## Recording Code Quality Entries
%%%
tag := "recording-code-quality"
%%%

Each saved value is referred to as an {name Lean.Linter.CodeQuality.Entry}`Entry`.
They are saved using {name}`Lean.Linter.logCodeQualityEntry`.
Analogous to {name Lean.Linter.logLintIf}`logLintIf`, {name Lean.Linter.logCodeQualityEntryIf}`logCodeQualityEntryIf` takes a linter option name and logs the entry if the corresponding linter is enabled, taking linter sets, {option}`linter.all`, and the {lakeOpt}`--lint-only` option into account.

Code quality entries relate a metric name, a source, and a value.
The metric name may be any string, but to avoid overlap, it should typically include the linter's option name as a prefix.
Using only the linter's name risks conflicting with the automatic counts of linter warnings that Lake emits as code quality metrics.
The helpers {name}`Lean.Linter.findCodeQualitySource` and {name}`Lean.Linter.findCodeQualitySource?` determine a {name Lean.Linter.CodeQuality.Source}`Source` from syntax parsed from the file, with the former falling back to the current module if it cannot find a declaration.
Sources may only be modules or declarations, and there is no way to attribute an entry to a smaller unit.
Instead, dictionary values can be used that encode the finer structure.
Values may be floating-point values or dictionaries that map strings to floating-point numbers.
Integral measures, such as counts, should also use floating-point numbers.

The same metric name may be logged any number of times for a given source.
Clients are responsible for aggregating metrics appropriately.

{docstring Lean.Linter.CodeQuality.Entry +allowMissing}

{docstring Lean.Linter.CodeQuality.Source +allowMissing}

{docstring Lean.Linter.CodeQuality.Value +allowMissing}

{docstring Lean.Linter.logCodeQualityEntry}

{docstring Lean.Linter.logCodeQualityEntryIf}

{docstring Lean.Linter.findMatchingDecl?}

{docstring Lean.Linter.findCodeQualitySource}

{docstring Lean.Linter.findCodeQualitySource?}


::::example "Measuring Simp Lemma Usage" (tag := "example-simp-metrics")
Even though linters are primarily intended to warn about potentially problematic code, they can also be used to just gather metrics, with warnings emitted by later checks.
This example demonstrates a command linter that logs metrics about the usage of explicit {tactic}`simp` lemmas, which could provide insights into missing {attrs}`@[simp]` annotations in a library.
These metrics are then collected and summarized by a small Lean program.

:::lakeSession
```toml
name = "simpstats"
defaultTargets = ["Code", "simp-stats"]

[[lean_lib]]
name = "Lints"

[[lean_lib]]
name = "Code"

[[lean_exe]]
name = "simp-stats"
root = "SimpStats"
```

The linter first traverses the syntax of the command with {name}`simpLemmaStarts`, which finds the source location of each explicit {tactic}`simp` lemma.
Lemmas are identified by their starting position because a {tactic}`simp` lemma list allows the lemmas to be applied to arguments.
The {name}`simpUsage` linter itself then uses the info tree to discover constant references that begin at the identified starting positions, logging a metric that contains a dictionary that maps fully-resolved names to occurrence counts.

```lean (file := "Lints/SimpUsage.lean")
module
public meta import Lean.Linter.Basic
public meta import Lean.Linter.Util

open Lean Elab Command

meta section

public register_option linter.simpUsage : Bool := {
  defValue := true
  descr := "record which lemmas are passed to `simp` as code quality metrics"
}

partial def simpLemmaStarts (stx : Syntax) : Array String.Pos.Raw := Id.run do
  let mut starts := #[]
  if stx.isOfKind ``Parser.Tactic.simpLemma then
    -- The lemma itself follows the optional `↓`/`↑` and `←` modifiers.
    if let some pos := stx[2].getPos? then starts := starts.push pos
  for arg in stx.getArgs do
    starts := starts ++ simpLemmaStarts arg
  return starts

def simpUsage : Linter where
  run := withSetOptionIn fun stx => do
    unless Linter.getLinterValue linter.simpUsage (← Linter.getLinterOptions) do return
    let starts := simpLemmaStarts stx
    if starts.isEmpty then return
    -- Each lemma occurrence is identified by its position, since the info tree can contain
    -- several nodes for the same syntax.
    let mut found : Std.HashSet (String.Pos.Raw × Name) := {}
    for tree in (← getInfoState).trees do
      found := tree.foldInfo (init := found) fun _ info found =>
        match info with
        | .ofTermInfo ti =>
          match ti.expr.constName?, ti.stx.getRange? with
          | some n, some r =>
            if starts.contains r.start then found.insert (r.start, n) else found
          | _, _ => found
        | _ => found
    let mut counts : Std.TreeMap String Float := {}
    for (_, n) in found do
      counts := counts.alter n.toString fun c => some (c.getD 0.0 + 1)
    unless counts.isEmpty do
      Linter.logCodeQualityEntryIf linter.simpUsage {
        name := "linter.simpUsage.lemmas"
        source := ← Linter.findCodeQualitySource stx
        value := .dict counts
      }

initialize addLinter simpUsage
```

This script takes the collected metrics from a project and summarizes them.
The function {name}`parseEntries` parses a sequence of JSON values, while {name}`main` processes the result and sorts the simp lemmas by their usage count.
```lean (file := "SimpStats.lean")
import Lean.Data.Json
open Lean

/-- Parses a sequence of JSON values, as printed by `lake lint --code-quality`. -/
def parseEntries (s : String) : Except String (Array Json) :=
  let p : Std.Internal.Parsec.String.Parser (Array Json) := do
    Std.Internal.Parsec.String.ws
    let entries ← Std.Internal.Parsec.many Json.Parser.anyCore
    Std.Internal.Parsec.eof
    return entries
  p.run s

def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  let entries ← IO.ofExcept (parseEntries input)
  let mut totals : Std.TreeMap String Float := {}
  for entry in entries do
    let .ok "linter.simpUsage.lemmas" := entry.getObjValAs? String "name"
      | continue
    let .ok (.obj dict) := do
      let v ← entry.getObjVal? "value"
      let d ← v.getObjVal? "dict"
      d.getObjVal? "dictionary"
      | continue
    for (lemma, count) in dict do
      let .ok n := count.getNum? | continue
      totals := totals.insert lemma (totals.getD lemma 0 + n.toFloat)
  let sorted := totals.toArray.qsort fun (_, a) (_, b) => a > b
  for (lemma, n) in sorted do
    IO.println s!"{n.toUInt64} {lemma}"
  return 0
```

The project itself contains four lemmas, {name}`t1` through {name}`t4`, spread across two modules:
```lean (file := "Code.lean")
module
public import Code.Lemmas
import Lints.SimpUsage

public theorem t4 (n : Nat) : n * 1 = n := by
  simp [Nat.mul_one]
```
```lean (file := "Code/Lemmas.lean")
module
import Lints.SimpUsage

public theorem t1 (n : Nat) : n + 0 = n := by
  simp [Nat.add_zero]

public theorem t2 (n m : Nat) : n + m = m + n := by
  simp [Nat.add_comm]

public theorem t3 (n : Nat) : 0 + n + 0 = n := by
  simp [Nat.add_zero, Nat.zero_add]
```

```lakeCmd "lake build" +ignoreOutput -show
```

After building, the code quality metrics list the uses of explicit {tactic}`simp` lemmas, and the sorting script summarizes them:
```lakeCmd "lake lint --code-quality"
{"value": {"dict": {"dictionary": {"Nat.add_zero": 1}}},
 "source": {"declaration": {"name": "t1", "module": "Code.Lemmas"}},
 "name": "linter.simpUsage.lemmas"}
{"value": {"dict": {"dictionary": {"Nat.add_comm": 1}}},
 "source": {"declaration": {"name": "t2", "module": "Code.Lemmas"}},
 "name": "linter.simpUsage.lemmas"}
{"value": {"dict": {"dictionary": {"Nat.zero_add": 1, "Nat.add_zero": 1}}},
 "source": {"declaration": {"name": "t3", "module": "Code.Lemmas"}},
 "name": "linter.simpUsage.lemmas"}
{"value": {"dict": {"dictionary": {"Nat.mul_one": 1}}},
 "source": {"declaration": {"name": "t4", "module": "Code"}},
 "name": "linter.simpUsage.lemmas"}
```
```lakeCmd "lake lint --code-quality | lake -q exe simp-stats"
2 Nat.add_zero
1 Nat.zero_add
1 Nat.add_comm
1 Nat.mul_one
```
:::
::::


## Package Code Quality Checks
%%%
tag := "package-code-quality-checks"
%%%

Package code quality checks are an opportunity to measure a property of an entire library or executable {tech}[target], as opposed to a declaration or module in isolation.
They are configured in the Lake configuration file or on the command line, and do not need to be imported by the code that they are measuring.
Package checks emit code quality entries.
Because they run as part of Lean and Lake, they have access to Lean's metaprogramming features and do not need to build their own _ad hoc_ mechanisms.
Scripts that enforce a limit or invariant on a whole package only need to parse JSON, rather than interacting with Lean code in complicated ways.

Package checks are enabled by adding their defining modules to the {tomlField Lake.PackageConfig}`checks` field in the Lake configuration or by using Lake's {lakeOpt}`--checks` option.
Within the configured package check modules, each check is a public definition of type {name Lean.Linter.CodeQuality.PackageCheck}`PackageCheck` in the `meta` phase that is registered with the {attr}`package_code_quality_check` attribute.
Given an argument of type {name Lean.Linter.CodeQuality.PackageCheckContext}`PackageCheckContext`, a package check may use any feature of {name Lean.MetaM}`MetaM` to compute an array of code quality entries.
The context specifies the library or executable's {tech (key := "module roots")}[root module] along with the {tech}[workspace]'s source search path.
Package checks should not throw exceptions to indicate that the package violated an invariant or desired property; instead, these issues should be returned as entries and then checked by a consumer of the data.

Enabled checks are run only when the {lakeOpt}`--code-quality` or {lakeOpt}`--checks` options are passed—{lake}`lint` will not otherwise run them.
For each root module, all registered package checks are run concurrently, and their resulting entries are appended to the overall collection of quality metrics.
Modules that are included in libraries through their {tech}[globs] field are not considered as roots.
Custom targets are not included, even if they build Lean code, and neither are non-default library and executable targets.
If modules are specified on the command line, they are checked instead of the default targets' root modules.
Exceptions thrown by package checks are written to standard error, but do not terminate linting.
If any exceptions were thrown, {lake}`lint` returns a non-zero exit code.

Checks are run in an environment in which the root module is imported.
Modules that are imported by multiple root modules can be checked multiple times by package checks.
If the root module is a {tech}[module] using the {ref "module-scopes"}[module system], then only public and server information is available in this environment; private declarations are not visible.
If the root module does not use the module system, then private information is also visible.
Each root module is checked in a fresh environment.

:::syntax attr (title := "Package Code Quality Checks")
```grammar
package_code_quality_check
```

Registers a package code quality check.
:::

{docstring Lean.Linter.CodeQuality.PackageCheck +allowMissing}

{docstring Lean.Linter.CodeQuality.PackageCheckContext +allowMissing}

::::example "Finding Duplicate Theorems" (tag := "example-package-check")

Because package checks have access to an entire library, they can be used to find duplicate theorems.
This example check is limited: it only finds theorems that match each other almost exactly, and does not take reorderings of hypotheses or unfoldings of definitions into account.
A more realistic check could use a more nuanced similarity measure, reporting theorems that exceed some threshold measure.

First, the `Checks` module is added to the package's {tomlField Lake.PackageConfig}`checks` field:
:::lakeSession
```toml
name = "dups"
defaultTargets = ["Code"]
checks = ["Checks"]

[[lean_lib]]
name = "Checks"

[[lean_lib]]
name = "Code"
```

Its single check starts by computing equivalence classes of theorems.
Theorems are identified by checking whether their types are propositions, and internal theorems produced as helpers for other declarations are skipped.
Non-internal theorems are sorted into equivalence classes using a hash table; the {lean}`BEq` instance for {lean}`Lean.Expr` and its corresponding {lean}`Hashable Lean.Expr` instance check equality modulo renaming of bound variables and changes of binder info.
Only modules in the root module's package are searched.
As a result, theorems that differ only by hypothesis naming or status as implicit parameters are grouped, while those that re-order hypotheses are not.
After the equivalence classes are identified, each element of each class with more than one element is given a metrics entry that lists the entire class.
```lean (file := "Checks.lean")
module
public meta import Lean.Linter.CodeQuality.Frontend
public meta import Lean.Compiler.ModPkgExt

open Lean Meta Linter CodeQuality

meta section

@[package_code_quality_check]
public def duplicateTheorems : PackageCheck where
  run ctx := do
    let env ← getEnv
    let some rootIdx := env.getModuleIdx? ctx.topLevelModule | return #[]
    let pkg := env.getModulePackageByIdx? rootIdx
    -- Group the theorems of the package's modules by their statements. Each equivalence class
    -- is a dictionary that maps its members' names to 1.0 to facilitate reporting.
    let mut classes : ExprMap (Std.TreeMap String Float) := {}
    let mut theorems := #[]
    for h : i in 0 ... env.header.moduleData.size do
      unless env.getModulePackageByIdx? i == pkg do continue
      for declName in env.header.moduleData[i].constNames do
        if declName.isInternalDetail then continue
        let some info := env.find? declName | continue
        unless ← isProp info.type do continue
        classes := classes.alter info.type fun dups? =>
          some ((dups?.getD {}).insert declName.toString 1.0)
        theorems := theorems.push (env.header.moduleNames[i]!, declName, info.type)
    -- Report each theorem that has duplicates.
    let mut entries := #[]
    for (modName, declName, type) in theorems do
      let some dups := classes[type]? | continue
      if dups.size < 2 then continue
      entries := entries.push {
        name := "duplicateTheorems"
        source := .declaration modName declName
        value := .dict dups
      }
    return entries
```

The code itself contains multiple restatements of the same theorem, three of which fall into the same equivalence class.
{name}`zero_add'` and {name}`add_zero_rev` have different statements.
```lean (file := "Code/Basic.lean")
module

public theorem add_zero' (n : Nat) : n + 0 = n := rfl

public theorem zero_add' (n : Nat) : 0 + n = n := Nat.zero_add n
```
```lean (file := "Code/Extra.lean")
module
public import Code.Basic

public theorem add_zero'' (m : Nat) : m + 0 = m := rfl

public theorem also_add_zero (k : Nat) : k + 0 = k := add_zero' k

public theorem add_zero_rev (n : Nat) : n = n + 0 := rfl
```
```lean (file := "Code.lean")
module
public import Code.Basic
public import Code.Extra
```
```lakeCmd "lake build Code Checks" +ignoreOutput -show
```
Each of the three versions of the theorem is marked with the entire equivalence class in the output:
```lakeCmd "lake lint --code-quality"
{"value":
 {"dict":
  {"dictionary": {"also_add_zero": 1, "add_zero''": 1, "add_zero'": 1}}},
 "source": {"declaration": {"name": "add_zero'", "module": "Code.Basic"}},
 "name": "duplicateTheorems"}
{"value":
 {"dict":
  {"dictionary": {"also_add_zero": 1, "add_zero''": 1, "add_zero'": 1}}},
 "source": {"declaration": {"name": "add_zero''", "module": "Code.Extra"}},
 "name": "duplicateTheorems"}
{"value":
 {"dict":
  {"dictionary": {"also_add_zero": 1, "add_zero''": 1, "add_zero'": 1}}},
 "source": {"declaration": {"name": "also_add_zero", "module": "Code.Extra"}},
 "name": "duplicateTheorems"}
```
:::
::::
