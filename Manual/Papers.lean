/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Manual.Meta.Bibliography

open Manual

def beyondNotations : InProceedings where
  title := .concat (inlines!"Beyond notations: Hygienic macro expansion for theorem proving languages")
  authors := #[.concat (inlines!"Sebastian Ullrich"), .concat (inlines!"Leonardo de Moura")]
  year := 2020
  booktitle := .concat (inlines!"Proceedings of the International Joint Conference on Automated Reasoning")


def carneiro19 : Thesis where
  title := .concat (inlines!"The Type Theory of Lean")
  author := .concat (inlines!"Mario Carneiro")
  year := 2019
  university := .concat (inlines!"Carnegie Mellon University")
  url := some "https://github.com/digama0/lean-type-theory/releases/download/v1.0/main.pdf"
  degree := .concat (inlines!"Masters thesis")

def castPaper : ArXiv where
  title := .concat (inlines!"Simplifying Casts and Coercions")
  authors := #[.concat (inlines!"Robert Y. Lewis"), .concat (inlines!"Paul-Nicolas Madelaine")]
  year := 2020
  id := "2001.10594"

def pratt73 : InProceedings where
  title := .concat (inlines!"Top down operator precedence")
  authors := #[.concat (inlines!"Vaughan Pratt")]
  year := 1973
  booktitle := .concat (inlines!"Proceedings of the 1st Annual ACM SIGACT-SIGPLAN Symposium on Principles of Programming Languages")

def tabledRes : ArXiv where
  title := .concat (inlines!"Tabled typeclass resolution")
  authors := #[.concat (inlines!"Daniel Selsam"), .concat (inlines!"Sebastian Ullrich"), .concat (inlines!"Leonardo de Moura")]
  year := 2020
  id := "2001.04301"

def ullrich23 : Thesis where
  title := .concat (inlines!"An Extensible Theorem Proving Frontend")
  author := .concat (inlines!"Sebastian Ullrich")
  year := 2023
  university := .concat (inlines!"Karlsruhe Institute of Technology")
  url := some "https://www.lean-lang.org/papers/thesis-sebastian.pdf"
  degree := .concat (inlines!"Dr. Ing. dissertation")
