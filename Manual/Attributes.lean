/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Lean.Parser.Command

open Manual
open Verso.Genre Manual InlineLean


open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

set_option pp.rawOnError true
set_option maxRecDepth 3000

set_option linter.unusedVariables false

#doc (Manual) "Attributes" =>
%%%
tag := "attributes"
htmlSplit := .never
%%%

{deftech}_Attributes_ are an extensible set of compile-time annotations on declarations.
They can be added as a {ref "declaration-modifiers"}[declaration modifier] or using the {keywordOf Lean.Parser.Command.attribute}`attribute` command.

Attributes can associate information with declarations in compile-time tables (including {tech}[custom simp sets], {tech}[macros], and {tech}[instances]), impose additional requirements on definitions (e.g. rejecting them if their type is not a type class), or generate additional code.
As with {tech}[macros] and custom {tech}[elaborators] for terms, commands, and tactics, the {tech}[syntax category] `attr` of attributes is designed to be extended, and there is a table that maps each extension to a compile-time program that interprets it.

Attributes are applied as {deftech}_attribute instances_ that pair a scope indicator with an attribute.
These may occur either in attributes as declaration modifiers or the stand-alone {keywordOf Lean.Parser.Command.attribute}`attribute` command.

:::syntax Lean.Parser.Term.attrInstance (title := "Attribute Instances")
```grammar
$_:attrKind $_:attr
```

An `attrKind` is the optional {ref "scoped-attributes"}[attribute scope] keywords {keyword}`local` or {keyword}`scoped`.
These control the visibility of the attribute's effects.
The attribute itself is anything from the extensible {tech}[syntax category] `attr`.
:::

The attribute system is very powerful: attributes can associate arbitrary information with declarations and generate any number of helpers.
This imposes some design trade-offs: storing this information takes space, and retrieving it takes time.
As a result, some attributes can only be applied to a declaration in the module where the declaration is defined.
This allows lookups to be much faster in large projects, because they don't need to examine data for all modules.
Each attribute determines how to store its own metadata and what the appropriate tradeoff between flexibility and performance is for a given use case.

# Attributes as Modifiers

Attributes can be added to declarations as a {ref "declaration-modifiers"}[declaration modifier].
They are placed between the documentation comment and the visibility modifiers.

:::syntax Lean.Parser.Term.attributes (open := false) (title := "Attributes")
```grammar
@[$_:attrInstance,*]
```
:::

# The {keyword}`attribute` Command

The {keywordOf Lean.Parser.Command.attribute}`attribute` command can be used to modify a declaration's attributes.
Some example uses include:
 * registering a pre-existing declaration as an {tech}[instance] in the local scope by adding {attr}`instance`,
 * marking a pre-existing theorem as a simp lemma or an extensionality lemma, using {attr}`simp` or {attr}`ext`, and
 * temporarily removing a simp lemma from the default {tech}[simp set].

:::syntax command (title := "Attribute Modification")
The {keywordOf Lean.Parser.Command.attribute}`attribute` command adds or removes attributes from an existing declaration.
The identifier is the name whose attributes are being modified.
```grammar
attribute [$_,*] $_
```
:::

In addition to attribute instances that add an attribute to an existing declaration, some attributes can be removed; this is called {deftech}_erasing_ the attribute.
Attributes can be erased by preceding their name with `-`.
Not all attributes support erasure, however.

:::syntax Lean.Parser.Command.eraseAttr (title := "Erasing Attributes")
Attributes are erased by preceding their name with a `-`.

```grammar
-$_:ident
```
:::


# Scoped Attributes
%%%
tag := "scoped-attributes"
%%%

Many attributes can be applied in a particular scope.
This determines whether the attribute's effect is visible only in the current section scope, in namespaces that open the current namespace, or everywhere.
These scope indications are also used to control {ref "syntax-rules"}[syntax extensions] and {ref "instance-attribute"}[type class instances].
Each attribute is responsible for defining precisely what these terms mean for its particular effect.

:::syntax attrKind (open := false) (title := "Attribute Scopes") (alias := Lean.Parser.Term.attrKind)
Globally-scoped declarations (the default) are in effect whenever the {tech}[module] in which they're established is transitively imported.
They are indicated by the absence of another scope modifier.
```grammar
```

Locally-scoped declarations are in effect only for the extent of the {tech}[section scope] in which they are established.
```grammar
local
```

Scoped declarations are in effect whenever the {tech key:="current namespace"}[namespace] in which they are established is opened.
```grammar
scoped
```
:::
