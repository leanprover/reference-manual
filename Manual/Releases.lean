/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Releases.«v4.15.0»
import Manual.Releases.«v4.16.0»
import Manual.Releases.«v4.17.0»

open Manual
open Verso.Genre

#doc (Manual) "Release Notes" =>
%%%
tag := "release-notes"
file := "releases"
number := false
%%%

This section provides release notes about recent versions of Lean and is presented in reverse
chronological order. When updating your copy of Lean to a new version, it is strongly recommended
that you read the corresponding release notes. They may contain advice that will help you understand
the differences with the previous version and upgrade your projects.

The work-in-progress release notes of a release candidate can be found [in the Lean Github
repository](https://github.com/leanprover/lean4/tree/master/releases).

{include 0 Manual.Releases.«v4.17.0»}

{include 0 Manual.Releases.«v4.16.0»}

{include 0 Manual.Releases.«v4.15.0»}
