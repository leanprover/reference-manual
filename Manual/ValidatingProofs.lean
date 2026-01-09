/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/
import VersoManual

import Manual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option guard_msgs.diff true

open Lean (Syntax SourceInfo)

#doc (Manual) "Validating a Lean Proof" =>
%%%
file := "ValidatingProofs"
tag := "validating-proofs"
%%%

This section discusses how to validate a proof expressed in Lean.

Depending on the circumstances, additional steps may be recommended to rule out misleading proofs.
In particular, it matters a lot whether one is dealing with an honest proof attempt, and needs protection against only benign mistakes, or a possibly-malicious proof attempt that actively tries to mislead.

In particular, we use “honest” when the goal is to create a valid proof.
This allows for mistakes and bugs in proofs and meta-code (tactics, attributes, commands, etc.), but not for code that clearly only serves to circumvent the system.

In contrast, we use “malicious” to describe code to go out of its way to trick or mislead the user, exploit bugs or compromise the system.
This includes unreviewed AI-generated proofs and programs.

Furthermore it is important to distinguish the question “does the theorem have a valid proof” from “what does the theorem statement mean”.

Below, an escalating sequence of checks are presented, with instructions on how to perform them, an explanation of what they entail and the mistakes or attacks they guard against.

# The Blue Double Check Marks
%%%
tag := "validating-blue-check-marks"
%%%

In regular everyday use of Lean, it suffices to check the blue double check marks next to the theorem statement for assurance that the theorem is proved.

## Instructions

While working interactively with Lean, once the theorem is proved, blue double check marks appear in the gutter to the left of the code.

:::figure "A double blue check mark"
![Double blue check marks appearing in the editor gutter](/static/screenshots/doublecheckmarks.png)
:::

## Significance

The blue ticks indicate that the theorem statement has been successfully elaborated, according to the syntax and type class instances defined in the current file and its imports, and that the Lean kernel has accepted a proof of that theorem statement that follows from the definitions, theorems and axioms declared in the current file and its imports.

## Trust

This check is meaningful if one believes the formal theorem statement corresponds to its intended informal meanings and trusts the authors of the imported libraries to be honest, that they performed this check, and that no unsound axioms have been declared and used.

## Protection

:::listBullet "🛡️"
This check protects against

* Incomplete proof (missing goals, tactic error) *of the current theorem*
* Explicit use of `sorry` *in the current theorem*
* Honest bugs in meta-programs and tactics
* Proofs still being checked in the background
:::

## Comments

In the Visual Studio Code extension settings, the symbol can be changed.
Editors other than VS Code may have a different indication.

Running `lake build +Module`, where `Module` refers to the file containing the theorem, and observing success without error messages or warnings provides the same guarantees.

# Printing Axioms
%%%
tag := "validating-printing-axioms"
%%%

The blue double check marks appear  even when there are explicit uses of {lean}`sorry` or incomplete proofs in the dependencies of the theorem.
Because both {lean}`sorry` and incomplete proofs are elaborated to axioms, their presence can be detected by listing the axioms that a proof relies on.

## Instructions

Write `#print axioms thmName` after the theorem declaration, with `thmName` replaced by the name of the theorem and check that it reports only the built-in axioms {name}`propext`, {name}`Classical.choice`, and {name}`Quot.sound`.

## Significance

This command prints the set of axioms used by the theorem and the theorems it depends on.
The three axioms above are standard axioms of Lean's logic, and benign.

* If {name}`sorryAx` is reported, then this theorem or one of its dependencies uses `sorry` or is otherwise incomplete.
*  If {name}`Lean.trustCompiler` is reported, then native evaluation is used; see below for a discussion.
* Any other axiom means that a custom axiom was declared and used, and the theorem is only valid relative to the soundness of these axioms.

## Trust

This check is meaningful if one believes the formal theorem statement corresponds to its intended informal meanings and one trusts the authors of the imported libraries to be honest.

## Protection

:::listBullet "🛡️"
(In addition to the list above)

* Incomplete proofs
* Explicit use of `sorry`
* Custom axioms
:::

## Comments

At the time of writing, the `#print axioms` command does not work in a `module`.
To work around this, create a non-module file, `import` your module, and use `#print axioms` there.

```leanModule
module
/--
error: cannot use `#print axioms` in a `module`; consider temporarily removing the `module` header or placing the command in a separate file
-/
#guard_msgs in
#print axioms sorryAx
```

# Re-Checking Proofs with `lean4checker`
%%%
tag := "validating-lean4checker"
%%%

There is a small class of bugs and some dishonest ways of presenting proofs that can be caught by re-checking the proofs that are stored in {tech}[`.olean` files] when building the project.

## Instructions

Build your project using {lake}`build`, run `lean4checker --fresh` on the module that contains the theorem of interest, and check that no error is reported.

## Significance

The `lean4checker` tool reads the declarations and proofs as they are stored by `lean` during building (the {tech}[`.olean` files]), and replays them through the kernel.
It trusts that the `.olean` files are structurally correct.

## Trust

This check is meaningful if one believes the formal theorem statement corresponds to its intended informal meanings and believes the authors of the imported libraries to not be very cunningly malicious, and to neither compromise the user’s system nor use Lean’s extensibility to change the interpretation of the theorem statement.

## Protection

:::listBullet "🛡️"
(In addition to the list above)

* Bugs in Lean’s core handling of the kernel’s state (e.g. due to parallel proof processing, or import handling)
* Meta-programs or tactics intentionally bypassing that state (e.g. using low-level functionality to add unchecked theorems)
:::

## Comments

Since `lean4checker` reads the `.olean` files without validating their format, this check is  prone to an attacker crafting invalid `.olean` files (e.g. invalid pointers, invalid data in strings).

Lean tactics and other meta-code can perform arbitrary actions when run.
Importing libraries created by a determined malicious attacker and building them without further protection can compromise the user's system, after which no further meaningful checks are possible.

We recommend running `lean4checker` as part of CI for the additional protection against bugs in Lean's handling of declaration and as a deterrent against simple attacks.
The [lean-action](https://github.com/leanprover/lean-action) Github Action provides this functionality by setting `lean4checker: true`.

Without the `--fresh` flag the tool can be instructed to only check some modules, and assume others to be correct (e.g. trusted libraries), for faster processing.

# Gold Standard: `comparator`
%%%
tag := "validating-comparator"
%%%

To protect against a seriously malicious proof compromising how Lean interprets a theorem statement or the user's system, additional steps are necessary.
This should only be necessary for high risk scenarios (proof marketplaces, high-reward proof competitions).

## Instructions

In a trusted environment, write the theorem *statement* (the ”challenge”), and then feed the challenge as well as the proposed proof to the [`comparator`](https://github.com/leanprover/comparator) tool, as documented there.

## Significance

Comparator will build the proof in a sandboxed environment, to protect against malicious code in the build step.
The proof term is exported to a serialized format.
Outside the sandbox and out of the reach of possibly malicious code, it validates the exported format, loads the proofs, replays them using Lean's kernel, and checks that the proved theorem statement matches the one in the challenge file.

## Trust

This check is meaningful if the theorem statement in the trusted challenge file is correct and the sandbox used to build the possibly malicious code is safe.

## Protection

:::listBullet "🛡️"
(In addition to the list above)

* Actively malicious proofs
:::

## Comments

At the time of writing, `comparator` uses only the official Lean kernel.
In the future it will be easy to use multiple, independent kernel implementations; then this will also protect against implementation bugs in the official Lean kernel.

# Remaining Issues

When following the gold standard of checking proofs using comparator, some assumptions remain:

* The soundness of Lean’s logic.
* The implementation of that logic in Lean’s kernel (for now; see comment above).
* The plumbing provided by the `comparator` tool.
* The safety of the sandbox used by `comparator`
* No human error or misleading presentation of the theorem statement in the trusted challenge file.

# On `Lean.trustCompiler`

Lean supports proofs by native evaluation.
This is used by the `decide +native` tactic or internally by specific tactics ({tactic}`bv_decide` in particular) and produces proof terms that call compiled Lean code to do a calculation that is then trusted by the kernel.

Specific uses wrapped in honest tactics (e.g. `bv_decide`) are generally trustworthy.
The trusted code base is larger (it includes Lean's compilation toolchain and library annotations in the standard library), but still fixed and vetted.

General use (`decide +native` or direct use of {name}`ofReduceBool`) can be used to create invalid proofs whenever the native evaluation of a term disagrees with the kernel's evaluation.
In particular, all `implemented_by`/`extern` attributes in libraries become part of the trusted code base.

All these uses show up as an axiom {name}`Lean.trustCompiler` in {keywordOf Lean.Parser.Command.printAxioms}`#print axioms`.
External checkers (`lean4checker`, `comparator`) cannot check such proofs, as they do not have access to the Lean compiler.
When that level of checking is needed, proofs have to avoid using native evaluation.

