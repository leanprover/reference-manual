import VersoManual

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "sadf" =>
%%%
%%%

This error occurs when an inductive type constructor is partially applied in the type of one of its
constructors such that one or more parameters of the type are omitted. The elaborator requires that
all parameters of an inductive type be specified everywhere that type is referenced in its
definition, including in the types of its constructors.

If it is necessary to allow the type constructor to be partially applied, without specifying a given
type parameter, that parameter must be converted to an index. See the manual section on
{ref "inductive-types"}[Inductive Types]for further explanation of the difference between indices
and parameters.

# Examples

## Omitting Parameter in Argument to Higher-Order Predicate
