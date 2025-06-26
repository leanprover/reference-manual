/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Namespaces" =>
%%%
tag := "namespaces"
%%%


Names that contain periods (that aren't inside {tech}[guillemets]) are hierarchical names; the periods separate the _components_ of a name.
All but the final component of a name are the namespace, while the final component is the name itself.

Namespaces serve to group related definitions, theorems, types, and other declarations.
When a namespace corresponds to a type's name, {tech}[generalized field notation] can be used to access its contents.
In addition to organizing names, namespaces also group {ref "language-extension"}[syntax extensions], {ref "attributes"}[attributes], and {ref "type-classes"}[instances].

Namespaces are orthogonal to {tech}[modules]: a module is a unit of code that is elaborated, compiled, and loaded together, but there is no necessary connection between a module's name and the names that it provides.
A module may contain names in any namespace, and the nesting structure of hierarchical modules is unrelated to that of hierarchical namespaces.

There is a root namespace, ordinarily denoted by simply omitting a namespace.
It can be explicitly indicated by beginning a name with `_root_`.
This can be necessary in contexts where a name would otherwise be interpreted relative to an ambient namespace (e.g. from a {tech}[section scope]) or local scope.

:::example "Explicit Root Namespace"
Names in the current namespace take precedence over names in the root namespace.
In this example, {name Forest.color}`color` in the definition of {name}`Forest.statement` refers to {name}`Forest.color`:
```lean
def color := "yellow"
namespace Forest
def color := "green"
def statement := s!"Lemons are {color}"
end Forest
```
```lean (name := green)
#eval Forest.statement
```
```leanOutput green
"Lemons are green"
```

Within the `Forest` namespace, references to {name _root_.color}`color` in the root namespace must be qualified with `_root_`:
```lean
namespace Forest
def nextStatement :=
  s!"Ripe lemons are {_root_.color}, not {color}"
end Forest
```
```lean (name := ygreen)
#eval Forest.nextStatement
```
```leanOutput ygreen
"Ripe lemons are yellow, not green"
```
:::

# Namespaces and Section Scopes

Every {tech}[section scope] has a {deftech}_current namespace_, which is determined by the {keywordOf Lean.Parser.Command.namespace}`namespace` command.{margin}[The {keywordOf Lean.Parser.Command.namespace}`namespace` command is described in the {ref "scope-commands"}[section on commands that introduce section scopes].]
Names that are declared within the section scope are added to the current namespace.
If the declared name has more than one component, then its namespace is nested within the current namespace; the body of the declaration's current namespace is the nested namespace.
Section scopes also include a set of {deftech}_opened namespaces_, which are namespaces whose contents are in scope without additional qualification.
{tech key:="resolve"}[Resolving] an identifier to a particular name takes the current namespace and opened namespaces into account.
However, {deftech}[protected] declarations (that is, those with the {keyword}`protected` {ref "declaration-modifiers"}[modifier]) are not brought into scope when their namespace is opened.
The rules for resolving identifiers into names that take the current namespace and opened namespaces into account are described in the {ref "identifiers-and-resolution"}[section on identifiers as terms].

:::example "Current Namespace"
Defining an inductive type results in the type's constructors being placed in its namespace, in this case as {name}`HotDrink.coffee`, {name}`HotDrink.tea`, and {name}`HotDrink.cocoa`.
```lean
inductive HotDrink where
  | coffee
  | tea
  | cocoa
```
Outside the namespace, these names must be qualified unless the namespace is opened:
```lean (name := okTea)
#check HotDrink.tea
```
```leanOutput okTea
HotDrink.tea : HotDrink
```
```lean (name := notOkTea) (error := true)
#check tea
```
```leanOutput notOkTea
unknown identifier 'tea'
```
```lean (name := okTea2)
section
open HotDrink
#check tea
end
```
```leanOutput okTea2
HotDrink.tea : HotDrink
```

If a function is defined directly inside the `HotDrink` namespace, then the body of the function is elaborated with the current namespace set to `HotDrink`.
The constructors are in scope:
```lean
def HotDrink.ofString? : String → Option HotDrink
  | "coffee" => some coffee
  | "tea" => some tea
  | "cocoa" => some cocoa
  | _ => none
```
Defining another inductive type creates a new namespace:
```lean
inductive ColdDrink where
  | water
  | juice
```

From within the `HotDrink` namespace, {name}`HotDrink.toString` can be defined without an explicit prefix.
Defining a function in the `ColdDrink` namespace requires an explicit `_root_` qualifier to avoid defining `HotDrink.ColdDrink.toString`:
```lean
namespace HotDrink

def toString : HotDrink → String
  | coffee => "coffee"
  | tea => "tea"
  | cocoa => "cocoa"

def _root_.ColdDrink.toString : ColdDrink → String
  | .water => "water"
  | .juice => "juice"

end HotDrink
```

:::

The {keywordOf Lean.Parser.Command.open}`open` command opens a namespace, making its contents available in the current section scope.
There are many variations on opening namespaces, providing flexibility in managing the local scope.

:::syntax command (title := "Opening Namespaces")
The {keywordOf Lean.Parser.Command.open}`open` command is used to open a namespace:
```grammar
open $_:openDecl
```
:::

:::syntax Lean.Parser.Command.openDecl (title := "Opening Entire Namespaces") (label := "open declaration")
A sequence of one or more identifiers results in each namespace in the sequence being opened:
```grammar
$_:ident $_:ident*
```
Each namespace in the sequence is considered relative to all currently-open namespaces, yielding a set of namespaces.
Every namespace in this set is opened before the next namespace in the sequence is processed.
:::

:::example "Opening Nested Namespaces"
Namespaces to be opened are considered relative to the currently-open namespaces.
If the same component occurs in different namespace paths, a single {keywordOf Lean.Parser.Command.open}`open` command can be used to open all of them by iteratively bringing each into scope.
This example defines names in a variety of namespaces:
```lean
namespace A -- _root_.A
def a1 := 0
namespace B -- _root_.A.B
def a2 := 0
namespace C -- _root_.A.B.C
def a3 := 0
end C
end B
end A
namespace B -- _root_.B
def a4 := 0
namespace C -- _root_.B.C
def a5 := 0
end C
end B
namespace C -- _root_.C
def a6 := 0
end C
```
The names are:
 * {name}`A.a1`
 * {name}`A.B.a2`
 * {name}`A.B.C.a3`
 * {name}`B.a4`
 * {name}`B.C.a5`
 * {name}`C.a6`

All six names can be brought into scope with a single iterated {keywordOf Lean.Parser.Command.open}`open` command:
```lean
section
open A B C
example := [a1, a2, a3, a4, a5, a6]
end
```

If the initial namespace in the command is `A.B` instead, then neither `_root_.A`, `_root_.B`, nor `_root_.B.C` is opened:
```lean (error := true) (name := dotted)
section
open A.B C
example := [a1, a2, a3, a4, a5, a6]
end
```
```leanOutput dotted
unknown identifier 'a1'
```
```leanOutput dotted
unknown identifier 'a4'
```
```leanOutput dotted
unknown identifier 'a5'
```
Opening `A.B` makes `A.B.C` visible as `C` along with `_root_.C`, so the subsequent `C` opens both.
:::


:::syntax Lean.Parser.Command.openDecl (title := "Hiding Names") (label := "open declaration")
A {keyword}`hiding` declaration specifies a set of names that should _not_ be brought into scope.
In contrast to opening an entire namespace, the provided identifier must uniquely designate a namespace to be opened.
```grammar
$_:ident hiding $x:ident $x:ident*
```
:::

```lean (show := false) (keep := false)
namespace A
namespace B
def x := 5
end B
end A
namespace B
end B
open A
-- test claim in preceding box
/-- error: ambiguous namespace 'B', possible interpretations: '[B, A.B]' -/
#check_msgs in
open B hiding x
```

:::syntax Lean.Parser.Command.openDecl (title := "Renaming") (label := "open declaration")
A {keyword}`renaming` declaration allows some names from the opened namespace to be renamed; they are accessible under the new name in the current section scope.
The provided identifier must uniquely designate a namespace to be opened.
```grammar
$_:ident renaming $[$x:ident → $x:ident],*
```

An ASCII arrow (`->`) may be used instead of the Unicode arrow (`→`).
:::

```lean (show := false) (keep := false)
namespace A
namespace B
def x := 5
end B
end A
namespace B
end B
open A
-- test claim in preceding box
/-- error: ambiguous namespace 'B', possible interpretations: '[B, A.B]' -/
#check_msgs in
open B renaming x → y
/-- error: ambiguous namespace 'B', possible interpretations: '[B, A.B]' -/
#check_msgs in
open B renaming x -> y
```


:::syntax Lean.Parser.Command.openDecl (title := "Restricted Opening") (label := "open declaration")
Parentheses indicate that _only_ the  names listed in the parentheses should be brought into scope.
```grammar
$_:ident ($x:ident $x*)
```
The indicated namespace is added to each currently-opened namespace, and each name is considered in each resulting namespace.
All of the listed names must be unambiguous; that is, they must exist in exactly one of the considered namespaces.
:::

```lean (show := false) (keep := false)
namespace A
namespace B
def y := ""
end B
end A
namespace B
end B
open A
-- test claim in preceding box
-- TODO the reality is a bit more subtle - the name should be accessible by only one path. This should be clarified.
/-- error: ambiguous identifier 'y', possible interpretations: [B.y, B.y] -/
#check_msgs in
open B (y)
```

:::syntax Lean.Parser.Command.openDecl (title := "Scoped Declarations Only") (label := "open declaration")
The {keyword}`scoped` keyword indicates that all scoped attributes, instances, and syntax from the provided namespaces should be opened, while not making any of the names available.
```grammar
scoped $x:ident $x*
```
:::

::::example "Opening Scoped Declarations"
In this example, a scoped {tech}[notation] and a definition are created in the namespace `NS`:
```lean
namespace NS
scoped notation "{!{" e "}!}" => (e, e)
def three := 3
end NS
```

Outside of the namespace, the notation is not available:

```syntaxError closed
def x := {!{ "pear" }!}
```
```leanOutput closed
<example>:1:21-1:22: unexpected token '!'; expected '}'
```

An {keyword}`open scoped` command makes the notation available:
:::keepEnv
```lean
open scoped NS
def x := {!{ "pear" }!}
```

However, the name {name}`NS.three` is not in scope:
```lean (error := true) (name := nothree)
def y := three
```
```leanOutput nothree
unknown identifier 'three'
```
:::
::::

# Exporting Names

{deftech}_Exporting_ a name makes it available in the current namespace.
Unlike a definition, this alias is completely transparent: uses are resolved directly to the original name.
Exporting a name to the root namespace makes it available without qualification; the Lean standard library does this for names such as the constructors of {name}`Option` and key type class methods such as {name}`get`.

:::syntax command (title := "Exporting Names")
The {keyword}`export` command adds names from other namespaces to the current namespace, as if they had been declared in it.
When the current namespace is opened, these exported names are also brought into scope.

```grammar
export $_ ($_*)
```

Internally, exported names are registered as aliases of their targets.
From the perspective of the kernel, only the original name exists; the elaborator resolves aliases as part of {tech key:="resolve"}[resolving] identifiers to names.
:::

:::example "Exported Names"
The declaration of the {tech}[inductive type] {name}`Veg.Leafy` establishes the constructors {name}`Veg.Leafy.spinach` and {name}`Veg.Leafy.cabbage`:
```lean
namespace Veg
inductive Leafy where
  | spinach
  | cabbage
export Leafy (spinach)
end Veg
export Veg.Leafy (cabbage)
```
The first {keyword}`export` command makes {name}`Veg.Leafy.spinach` accessible as {name}`Veg.spinach` because the {tech}[current namespace] is `Veg`.
The second makes {name}`Veg.Leafy.cabbage` accessible as {name}`cabbage`, because the current namespace is the root namespace.
:::
