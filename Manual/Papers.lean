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

def doUnchained : InProceedings where
  title := .concat (inlines!"`do` Unchained: Embracing Local Imperativity in a Purely Functional Language")
  authors := #[.concat (inlines!"Sebastian Ullrich"), .concat (inlines!"Leonardo de Moura")]
  url := some "https://dl.acm.org/doi/10.1145/3547640"
  year := 2022
  booktitle := .concat (inlines!"Proceedings of the ACM on Programming Languages: ICFP 2022")

def countingBeans : InProceedings where
  title := .concat (inlines!"Counting Immutable Beans: Reference Counting Optimized for Purely Functional Programming")
  authors := #[.concat (inlines!"Sebastian Ullrich"), .concat (inlines!"Leonardo de Moura")]
  url := some "https://arxiv.org/abs/1908.05647"
  year := 2019
  booktitle := .concat (inlines!"Proceedings of the 31st Symposium on Implementation and Application of Functional Languages (IFL 2019)")

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

def launchbury94 : InProceedings where
  title := .concat (inlines!"Lazy functional state threads")
  authors := #[.concat (inlines! "John Launchbury"), .concat (inlines!"Simon L Peyton Jones")]
  year := 1994
  booktitle := .concat (inlines!"Proceedings of the ACM SIGPLAN 1994 Conference on Programming Language Design and Implementation")

def manolios2006 : InProceedings where
  title := .concat (inlines!"Termination Analysis with Calling Context Graphs")
  authors := #[.concat (inlines!"Panagiotis Manolios"), .concat (inlines!"Daron Vroon")]
  year := 2006
  booktitle := .concat (inlines!"Proceedings of the International Conference on Computer Aided Verification (CAV 2006)")
  series := some <| .concat (inlines!"LNCS 4144")
  url := "https://doi.org/10.1007/11817963_36"

def bulwahn2007 : InProceedings where
  title := .concat (inlines!"Finding Lexicographic Orders for Termination Proofs in Isabelle/HOL")
  authors := #[.concat (inlines!"Lukas Bulwahn"), .concat (inlines!"Alexander Krauss"), .concat (inlines!"Tobias Nipkow")]
  year := 2007
  booktitle := .concat (inlines!"Proceedings of the International Conference on Theorem Proving in Higher Order Logics (TPHOLS 2007)")
  series := some <| .concat (inlines!"LNTCS 4732")
  url := "https://doi.org/10.1007/978-3-540-74591-4_5"

def streicher1993 : Thesis where
  title := .concat (inlines!"Investigations into Intensional Type Theory")
  author := .concat (inlines!"Thomas Streicher")
  year := 1993
  university := .concat (inlines!"Ludwig-Maximilians-Universität München")
  url := "https://www2.mathematik.tu-darmstadt.de/~streicher/HabilStreicher.pdf"
  degree := .concat (inlines!"Habilitation")

def wadler1989 : InProceedings where
  title := .concat (inlines!"Theorems for free!")
  authors := #[.concat (inlines!"Philip Wadler")]
  year := 1989
  booktitle := .concat (inlines!"Proceedings of the Fourth International Conference on Functional Programming Languages and Computer Architecture")
  url := "https://dl.acm.org/doi/pdf/10.1145/99370.99404"

def wadlerBlott89 : InProceedings where
  title := .concat (inlines!"How to make ad-hoc polymorphism less ad hoc")
  authors := #[.concat (inlines!"Philip Wadler"), .concat (inlines!"Stephen Blott")]
  year := 1980
  booktitle := .concat (inlines!"Proceedings of the 16th Symposium on Principles of Programming Languages")
