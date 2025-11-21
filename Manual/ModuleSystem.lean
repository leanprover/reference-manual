/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich
-/

import VersoManual
import Manual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The Module System" =>
%%%
number := false
tag := "module-system"
%%%

The module system is an experimental feature that allows for more fine-grained control over what information is exported from, and imported into, Lean files.

The main benefits of doing so are:

: Much-improved average build times

  Changes to files that affect only non-exported information (e.g. proofs, comments, and docstrings) will not trigger rebuilds outside of these files.
  Even when some dependent files have to be rebuilt, those files that cannot be affected according to the `import` annotations can be skipped.

: Control over API evolution

  Library authors can trust that changes to non-exported information will not affect downstream users of their library.

: Avoiding accidental unfolding

  Limiting the scope in which definitions can be unfolded allows for avoiding both reductions that should be replaced by application of more specific theorems as well as unproductive reductions that were not in fact necessary.

: Smaller executables (TBD)

  Separating compile-time and run-time code allows for more aggressive dead code elimination, guaranteeing that metaprograms such as tactics do not make it into the final binary.

: Reduced memory usage

  Excluding private information such as proofs from importing can improve Lean's memory use both while building and editing a project.
  Porting mathlib4 to the module system has shown savings close to 50% from this even before imports are further minimized.

The module system is activated by prefixing a Lean file with the `module` keyword.
`module`s can only import other `module`s so adoption has to be done top-down.
Non-`module`s can import `module`s and will ignore all module-system-specific annotations.

At the time of writing, the module system is considered experimental and additionally guarded by the `experimental.module` option that has to be set to `true` in the project's Lake configuration file.
All libraries shipped with Lean are fully ported.
The language semantics described below are close to final, but not all benefits described above are implemented yet.

# Visibility

The main distinction the module system introduces is between the {deftech}_public scope_ that contains all information visible to other modules via `import` and the {deftech}_private scope_ that is not imported by default.
Both declarations and imports themselves are scoped in this way.

The default scope is private.
The new modifier `public` before a declaration or import puts it into the public scope instead.
No information from the private scope can be used in the public scope to ensure information in the latter still makes sense when only it is imported into other modules.

:::TODO
These examples should be output-checked and elaborated with `-Dexperimental.module=true`
:::

```
module

def priv : Nat := 0

public abbrev pub : Nat := priv  -- error: Unknown identifier `priv`
```
See option `backward.privateInPublic` for disabling/weakening this check while porting larger projects to the module system.

`public section` can be used to switch the default scope for declarations, with `private` locally negating it.
This is mostly intended to ease porting while avoiding merge conflicts.

Marking a declaration as public at minimum makes its "signature", i.e. its name and type, visible.
Some specific declarations/terms may still put other parts in the private scope as follows:
* `by` used in the public scope to prove a proposition puts the resulting proof in the private scope (by wrapping it in a public helper theorem).
  In special cases, this may break existing code as such a `by` can no longer fill in metavariables in its expected type, which would allow information to leak from the private to the public scope.
  The option `backward.proofsInPublic` can be used to disable this new behavior; it should usually be paired with `backward.privateInPublic` so that private references in the `by` now elaborated in the public scope do not break.
* `def` puts its body in the private scope by default. The defined constant cannot be unfolded when used in the public scope.
This can be changed with the `@[expose]` attribute.
`@[expose] section` can be used to apply the attribute to all `def`s in the section and can locally be negated by `@[no_expose]`.
* `theorem` and `opaque` never expose their body.
Consider using `@[expose] def` instead if exposition is absolutely necessary.
* `abbrev` and `instance` always expose their body.
For `instance`, individual field values can be marked `private`, which can be useful for programming purposes.
For proof fields, `by` already does the trick.
```
module

def myInternalHelper (x : Nat) : String := ...

public instance : ToString Nat where
  toString x := private myInternalHelper x
```

## Import Visibility

The basic form `public import M` makes the {tech}[public scope] of `M` available in the public scope of the current module. The {tech}[private scope] of `M` is discarded.
Without `public`, the public scope of `M` is instead imported into the private scope.
The import thus is irrelevant to downstream modules and ignored by them.

`import all M` behaves like `import M` but additionally imports the private scope of `M` into the private scope of the current module.
This is only allowed by default if `M` and the current module have the same module name root, as its main purpose is to allow for separating definitions and proofs into separate modules for internal organization of a library.
```
-- Module M.Defs
module

public def f : Nat := 0
```
```
-- Module M.Lemmas
module

import all M.Defs

public theorem f_eq_zero : f = 0 :=
  -- may access body of `f` imported into the private scope
  rfl
```
Note that the imported private scope includes private `import`s of `M`, including nested `import all`s that then are interpreted likewise.
That is, the set of private scopes accessible to the current module is the transitive closure of `import all` declarations.

The module system's `import all` is more powerful than `import` without the module system.
It makes imported private definitions accessible directly by name, as if they were defined in the current module.
Thus another use case of `import all` is to make declarations available that need to be used in multiple modules but should not leak outside the current library.

# The `meta` Phase

When it comes to actual code execution, there is no point to a definition without a body.
Thus, in order to eagerly know what definitions _might_ be executed at compile time and so need to be available including their bodies (in some executable shape), any definition used as an entry point to compile-time execution has to be tagged with the new `meta` modifier.
This is automatically done in built-in metaprogramming syntax such as `syntax`, `macro`, and `elab` but may need to be done explicitly when manually applying metaprogramming attributes such as `@[app_delab]`.

A `meta` definition may only access (and thus invoke) other `meta` definitions; a non-`meta` definition likewise may only access other non-`meta` definitions.
For imported definitions, the `meta` marker can be added after the fact using `meta import`.
`meta import`ing a definition already in the meta phase leaves it in that phase.
In addition, the import must be public if the imported definition may be compile-time executed outside the current module, i.e. if it is reachable from some public `meta` definition in the current module: use `public meta import` or, if already `meta`, `public import`.
This is usually the case, unless a definition was imported solely for use in local metaprograms such as `local syntax/macro/elab/...`.
```
module

meta import Std.Data.HashMap

local elab "my_elab" : command => do
  let m : Std.HashMap := {}
  ...
```

For convenience, `meta` also implies `partial`.
This can be overridden by giving an explicit `termination_by` metric (such as one suggested by `termination_by?`), which may be necessary when the type of the definition is not known to be `Nonempty`.

As a guideline, it is usually preferable to keep the amount of `meta` annotations as small as possible.
This avoids locking otherwise-reusable declarations into the meta phase and it helps the build system avoid more rebuilds.
Thus, when a metaprogram depends on other code that does not itself need to be marked `meta`, this other code should be located in a separate module and not marked `meta`.
Only the final module that actually registers a metaprogram needs the helpers as `meta` definitions.
It should use `public meta import` to import those helpers and then define its metaprograms using built-in syntax like `elab`, using `meta def`, or using `meta section`.

# Common Errors and Patterns

The following list contains common errors one might encounter when using the module system and especially porting existing files to the module system.

: Unknown constant

  Check whether you might be trying to access a private definition in the public scope.
  If so, you might want to make the current declaration private as well or otherwise enter the private scope such as through `private` on a field or `by` for a proof.
  TODO: improve error message.

  If the message is prefixed with `(interpreter)`, this suggests a missing `meta import`.
  The new import should be placed in the file defining the metaprogram depending on the missing constant, which is not necessarily the file triggering the error.
  Note that the language server always does `meta import`s for the benefit of `#eval` etc., so the error might only occur in a cmdline build.
  TODO: better, static `meta` checking.

: Definitional equality errors, especially after porting

  You are likely missing an {attr}`expose` attribute on a definition or alternatively, if imported, an `import all`.
  Prefer the former if anyone outside your library might feasible require the same access.
  {keywordOf Lean.reduceCmd}`#reduce` and/or {option}`trace.Meta.isDefEq` can help with finding the blocking definition.
  You might also see this as a kernel error when a tactic directly emits proof terms referencing specific declarations without going through the elaborator, such as for proof by reflection.
  In this case, there is no readily available trace for debugging; consider using `@[expose] section`s generously on the closure of relevant modules.

: "failed to compile 'partial' definition" on `meta` definition

  This can happen when a definition with a type that is not known to be `Nonempty` is marked `meta` or moved into a `meta section`, which both imply `partial` without a termination metric.
  Use `termination_by?` to make the previously implicitly inferred termination metric explicit, or provide a `Nonempty` instance.
  
## Recipe for Porting Existing Files

Start by enabling the module system throughout all files with minimal breaking changes:
* Prefix all files with `module`.
* Make all existing imports `public` unless you know they will be used only in proofs.
  Add `import all` when getting errors about references to private data.
  Add `public meta import` when getting "must be `meta`" errors (`public` may be avoided when defining local-only metaprograms).
* Prefix the remainder of the file with `@[expose] public section` or, for programming-focused files, with `public section`.

After getting an initial build under the module system to work, you can then work iteratively on minimizing uses of `public` and `@[expose]` where sensible.