/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

open Verso.Genre Manual

#doc (Manual) "Supported Platforms" =>
%%%
tag := "platforms"
file := "platforms"
number := false
%%%



# Tier 1

:::paragraph
Tier 1 platforms are those for which Lean is built and tested by our CI infrastructure.
Binary releases of Lean are available for these platforms via {ref "elan"}[`elan`].
The Tier 1 platforms are:

* x86-64 Linux with glibc 2.26+
* aarch64 Linux with glibc 2.27+
* aarch64 (Apple Silicon) macOS 10.15+
* x86-64 Windows 11 (any version), Windows 10 (version 1903 or higher), Windows Server 2022, Windows Server 2025
:::

# Tier 2

Tier 2 platforms are those for which Lean is cross-compiled but not tested by our CI.
Binary releases are available for these platforms.

Releases may be silently broken due to the lack of automated testing.
Issue reports and fixes are welcome.

:::paragraph
The Tier 2 platforms are:
* x86-64 macOS 10.15+
* Emscripten WebAssembly
:::
