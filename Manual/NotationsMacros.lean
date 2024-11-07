/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Language.Classes
import Manual.Language.Functions
import Manual.Language.Files
import Manual.Language.InductiveTypes

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "Notations and Macros" =>
%%%
tag := "language-extension"
%%%

Different mathematical fields have their own notational conventions, and many notations are re-used with differing meanings in different fields.
It is important that formal developments are able to use established notations: formalized mathematics is already difficult, and the mental overhead of translating between syntaxes can be substantial.
At the same time, it's important to be able to control the scope of notational extensions.
Many fields use related notations with very different meanings, and it should be possible to combine developments from these separate fields in a way where both readers and the system know which convention is in force in any given region of a file.

Lean addresses the problem of notational extensibility with a variety of mechanisms, each of which solves different aspects of the problem.
They can be combined flexibly to achieve the necessary results:

 * The {ref "parser"}_extensible parser_ {index}[parser] allows a great variety of notational conventions to be implemented declaratively, and combined flexibly.
 * {ref "macro-and-elab"}[Macros] allow new syntax to be easily mapped to existing syntax, which is a simple way to provide meaning to new constructs.
  Due to {tech}[hygiene] and automatic propagation of source positions, this process doesn't interfere with Lean's interactive features.
 * {ref "macro-and-elab"}[Elaborators] provide new notations with the same tools available to Lean's own syntax in cases where a macro is insufficiently expressive.

# Notations
%%%
tag := "notations"
%%%

:::planned 69
A presentation of the `notation` command and how to define infix operators
:::

::: TODO
 * How to define them
 * Precedence and associativity
 * Limitations - when not?
:::

# Defining New Syntax

## Syntax Categories and Extensions
%%%
tag := "syntax-categories"
%%%

# Macros
%%%
tag := "macros"
%%%

:::planned 71
 * Definition of {deftech}_macro_
 * `macro_rules`
   * Syntax patterns
   * Backtracking on expansion failure
 * {deftech}[Hygiene] and quotation
 * The `macro` command
:::


## Matching Syntax

::: TODO
 * Quasiquotations
   * Troubleshooting: longest match
:::

## Macro Attribute

## The `macro_rules` and `macro` commands

# Elaborators
%%%
tag := "elaborators"
%%%

:::planned 72
For now, a quick overview of elaborators - detailed description to be written in a later revision
:::
