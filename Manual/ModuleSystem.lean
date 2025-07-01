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
%%%

The module system is an experimental Lean 4 feature allowing for finer-grained control over what information is exported from Lean modules and imported into other modules, improving average build times, executable sizes, API design options, and more.

The module system is activated by prefixing a Lean file with the `module` keyword.
At the time of writing, it is additionally guarded by the `experimenta
.module` option that has to be set to `true` in the project's Lakefile.
`module`s can only import other `module`s so adoption has to be done top-down.
Non-`module`s can import `module`s and will ignore all module system-specific annotations.

# Visibility

The main distinction the module system introduces is between the *public scope* that contains all information visible to other modules via `import` and the *private scope* that is not imported by default.
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

public theorem priv_eq_priv : priv = priv := rfl
```

`public section` can be used to switch the default scope for declarations, with `private` locally negating it.
This is mostly intended to ease porting and avoiding merge conflicts during it.

Marking a declaration as public at minimum makes its "signature", i.e. its name and type, visible.
Some specific declarations/terms may still put other parts in the private scope as follows:
* `by` used in the public scope on a proposition puts the resulting proof in the private scope (by wrapping it in a public helper theorem).
* `def` puts its body in the private scope by default, thus it cannot be unfolded when used in the public scope.
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

The basic form `public import M` makes the public scope of `M` available in the public scope of the current module and discards the private scope.
Without `public`, the public scope of `M` is instead imported into the private scope.
The import thus is irrelevant to downstream modules and ignored by them.

`import all M` behaves like `import M` but additional imports the private scope of `M` into the private scope of the current module.
This is only allowed if `M` and the current module live in the same library as its main purpose is to allow for separating definitions and proofs into separate modules for internal organization of a library.
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
Note also that `import all` is more powerful than the basic `import` before the module system as it allows for accessing imported private definitions directly by name, as if they were defined in the current module.
Thus another use case of `import all` is to make declarations available that need to be used in multiple modules but should not leak outside the current library.

`public import all M` behaves like `public import M` followed by `import all M`, i.e. the `all` modifier becomes irrelevant for downstream modules.

# The `meta` Phase

When it comes to actual code execution, there is no point to a definition without a body.
Thus, in order to eagerly know what definitions *might* be executed at compile time and so need to be available including their bodies (in some executable shape), any definition used as an entry point to compile-time execution has to be tagged with the new `meta` modifier[^meta3].
This is automatically done in built-in metaprogramming syntax such as `syntax`, `macro`, and `elab` but may need to be done explicitly when manually applying metaprogramming attributes such as `@[app_delab]`.

[^meta3]: Semantically unrelated to the modifier of the same name in Lean 3.

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

* Unknown constant: check whether you might be trying to access a private definition in the public scope.
  If so, you might want to make the current declaration private as well or otherwise enter the private scope such as through `private` on a field or `by` for a proof.
  TODO: improve error message.
* Definitional equality errors, especially after porting: you are likely missing an `@[expose]` on a definition or alternatively, if imported, an `import all`.
  Prefer the former if anyone outside your library might feasible require the same access.
  `#reduce` and/or `trace.Meta.isDefEq` can help with finding the blocking definition.
  You might also see this as a kernel error when a tactic directly emits proof terms referencing specific declarations without going through the elaborator, such as for proof by reflection.
  In this case, there is no readily available trace for debugging; consider using `@[expose] section`s generously on the closure of relevant modules.
