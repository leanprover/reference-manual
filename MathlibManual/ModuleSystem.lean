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

: Average build times

  Changes to files that affect only non-exported information (e.g. proofs) will not trigger rebuilds outside of these files.
  Even when dependent files have to be rebuilt, those files that cannot be affected according to the `import` annotations can be skipped.

: API evolution

  Library authors can trust that changes to non-exported information will not affect downstream users of their library.

: Avoiding accidental unfolding

  Limiting the scope in which definitions can be unfolded allows for avoiding both reductions that should be replaced by application of more specific theorems as well as unproductive reductions that were not in fact necessary.

: Smaller executables

  Separating compile-time and run-time code allows for more aggressive dead code elimination.

The module system is activated by prefixing a Lean file with the `module` keyword.
`module`s can only import other `module`s so adoption has to be done top-down.
Non-`module`s can import `module`s and will ignore all module-system-specific annotations.

At the time of writing, the module system is considered experimental and additionally guarded by the `experimental.module` option that has to be set to `true` in the project's Lake configuration file.
Of libraries shipped with Lean, only `Init` is currently fully ported.
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

`public section` can be used to switch the default scope for declarations, with `private` locally negating it.
This is mostly intended to ease porting while avoiding merge conflicts.

Marking a declaration as public at minimum makes its "signature", i.e. its name and type, visible.
Some specific declarations/terms may still put other parts in the private scope as follows:
* `by` used in the public scope to prove a proposition puts the resulting proof in the private scope (by wrapping it in a public helper theorem).
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

The basic form `public import M` makes the public scope of `M` available in the public scope of the current module. The private scope of `M` is discarded.
Without `public`, the public scope of `M` is instead imported into the {tech}[private scope].
The import thus is irrelevant to downstream modules and ignored by them.

`import all M` behaves like `import M` but additionally imports the private scope of `M` into the private scope of the current module.
This is only allowed if `M` and the current module have the same module name root, as its main purpose is to allow for separating definitions and proofs into separate modules for internal organization of a library.
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

`public import all M` behaves like `public import M` followed by `import all M`, i.e. the `all` modifier becomes irrelevant for downstream modules.

# The `meta` Phase

When it comes to actual code execution, there is no point to a definition without a body.
Thus, in order to eagerly know what definitions _might_ be executed at compile time and so need to be available including their bodies (in some executable shape), any definition used as an entry point to compile-time execution has to be tagged with the new `meta` modifier.
This is automatically done in built-in metaprogramming syntax such as `syntax`, `macro`, and `elab` but may need to be done explicitly when manually applying metaprogramming attributes such as `@[app_delab]`.

A `meta` definition may access (and thus invoke) any `meta` or non-`meta` definition of the current module.
For accessing imported definitions, the definition must either have been marked as `meta` when it was declared or the import must be marked as such (`meta import` when the accessing definition is in the private scope and `public meta import` otherwise).

```
module

meta import Std.Data.HashMap

local elab "my_elab" : command => do
  let m : Std.HashMap := {}
  ...
```

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

## Recipe for Porting Existing Files

Start by enabling the module system throughout all files with minimal breaking changes:
* Prefix all files with `module`.
* Make all existing imports `public` unless you know they will be used only in proofs.
  Add `import all` when getting errors about references to private data.
  Add `public meta import` when getting "must be `meta`" errors (`public` may be avoided when defining local-only metaprograms).
* Prefix the remainder of the file with `@[expose] public section` or, for programming-focused files, with `public section`.

After getting an initial build under the module system to work, you can then work iteratively on minimizing uses of `public` and `@[expose]` where sensible.