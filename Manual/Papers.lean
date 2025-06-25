/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual.Bibliography

open Verso.Genre.Manual

def beyondNotations : InProceedings where
  title := inlines!"Beyond notations: Hygienic macro expansion for theorem proving languages"
  authors := #[inlines!"Sebastian Ullrich", inlines!"Leonardo de Moura"]
  year := 2020
  booktitle := inlines!"Proceedings of the International Joint Conference on Automated Reasoning"


def carneiro19 : Thesis where
  title := inlines!"The Type Theory of Lean"
  author := inlines!"Mario Carneiro"
  year := 2019
  university := inlines!"Carnegie Mellon University"
  url := some "https://github.com/digama0/lean-type-theory/releases/download/v1.0/main.pdf"
  degree := inlines!"Masters thesis"

def castPaper : ArXiv where
  title := inlines!"Simplifying Casts and Coercions"
  authors := #[inlines!"Robert Y. Lewis", inlines!"Paul-Nicolas Madelaine"]
  year := 2020
  id := "2001.10594"

def doUnchained : InProceedings where
  title := inlines!"`do` Unchained: Embracing Local Imperativity in a Purely Functional Language"
  authors := #[inlines!"Sebastian Ullrich", inlines!"Leonardo de Moura"]
  url := some "https://dl.acm.org/doi/10.1145/3547640"
  year := 2022
  booktitle := inlines!"Proceedings of the ACM on Programming Languages: ICFP 2022"

def countingBeans : InProceedings where
  title := inlines!"Counting Immutable Beans: Reference Counting Optimized for Purely Functional Programming"
  authors := #[inlines!"Sebastian Ullrich", inlines!"Leonardo de Moura"]
  url := some "https://arxiv.org/abs/1908.05647"
  year := 2019
  booktitle := inlines!"Proceedings of the 31st Symposium on Implementation and Application of Functional Languages (IFL 2019)"

def pratt73 : InProceedings where
  title := inlines!"Top down operator precedence"
  authors := #[inlines!"Vaughan Pratt"]
  year := 1973
  booktitle := inlines!"Proceedings of the 1st Annual ACM SIGACT-SIGPLAN Symposium on Principles of Programming Languages"

def tabledRes : ArXiv where
  title := inlines!"Tabled typeclass resolution"
  authors := #[inlines!"Daniel Selsam", inlines!"Sebastian Ullrich", inlines!"Leonardo de Moura"]
  year := 2020
  id := "2001.04301"

def ullrich23 : Thesis where
  title := inlines!"An Extensible Theorem Proving Frontend"
  author := inlines!"Sebastian Ullrich"
  year := 2023
  university := inlines!"Karlsruhe Institute of Technology"
  url := some "https://www.lean-lang.org/papers/thesis-sebastian.pdf"
  degree := inlines!"Dr. Ing. dissertation"

def launchbury94 : InProceedings where
  title := inlines!"Lazy functional state threads"
  authors := #[inlines!"John Launchbury", inlines!"Simon L Peyton Jones"]
  year := 1994
  booktitle := inlines!"Proceedings of the ACM SIGPLAN 1994 Conference on Programming Language Design and Implementation"

def manolios2006 : InProceedings where
  title := inlines!"Termination Analysis with Calling Context Graphs"
  authors := #[inlines!"Panagiotis Manolios", inlines!"Daron Vroon"]
  year := 2006
  booktitle := inlines!"Proceedings of the International Conference on Computer Aided Verification (CAV 2006)"
  series := some <| inlines!"LNCS 4144"
  url := "https://doi.org/10.1007/11817963_36"

def bulwahn2007 : InProceedings where
  title := inlines!"Finding Lexicographic Orders for Termination Proofs in Isabelle/HOL"
  authors := #[inlines!"Lukas Bulwahn", inlines!"Alexander Krauss", inlines!"Tobias Nipkow"]
  year := 2007
  booktitle := inlines!"Proceedings of the International Conference on Theorem Proving in Higher Order Logics (TPHOLS 2007)"
  series := some <| inlines!"LNTCS 4732"
  url := "https://doi.org/10.1007/978-3-540-74591-4_5"

def streicher1993 : Thesis where
  title := inlines!"Investigations into Intensional Type Theory"
  author := inlines!"Thomas Streicher"
  year := 1993
  university := inlines!"Ludwig-Maximilians-Universität München"
  url := "https://www2.mathematik.tu-darmstadt.de/~streicher/HabilStreicher.pdf"
  degree := inlines!"Habilitation"

def wadler1989 : InProceedings where
  title := inlines!"Theorems for free!"
  authors := #[inlines!"Philip Wadler"]
  year := 1989
  booktitle := inlines!"Proceedings of the Fourth International Conference on Functional Programming Languages and Computer Architecture"
  url := "https://dl.acm.org/doi/pdf/10.1145/99370.99404"

def wadlerBlott89 : InProceedings where
  title := inlines!"How to make ad-hoc polymorphism less ad hoc"
  authors := #[inlines!"Philip Wadler", inlines!"Stephen Blott"]
  year := 1980
  booktitle := inlines!"Proceedings of the 16th Symposium on Principles of Programming Languages"

def wadler2003 : InProceedings where
  title := inlines!"A Prettier Printer"
  authors := #[inlines!"Philip Wadler"]
  year := 2003
  booktitle := inlines!"The Fun of Programming, A symposium in honour of Professor Richard Bird's 60th birthday"
  url := "https://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf"
