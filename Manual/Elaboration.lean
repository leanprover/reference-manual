import VersoManual

import Manual.Meta

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Elaboration, Evaluation, and Compilation" =>

:::planned


 * Describe the roles of the {deftech}_kernel_, the interpreter, the compiler, the {deftech key:="elaborate"}[elaborator], and how they interact
 * Sketch the pipeline (parser -> command elaborator (with macro expansion) -> term elaborator (with macro expansion) -> ...
 * Cost model for programs - what data is present at which stage?

:::
