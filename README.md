# perm_lang_ax1

This repository contains Isabelle theory files that formalize the definitions and proofs given in "Types for Enforcing Mutual Exclusion in a Higher-Order Language." The proofs are complete, but it still remains for them to be cleaned up to be more readable. If you are a reader who wants to look at the codebase, this document is an index describing where definitions from the paper correspond to a relevant theory file.

# 2 Language Syntax and Semantics

## 2.1 Constants
Constants `c` are split into "constants" (which include primitive constant values and special function constants) and "operators" (function constants for primitive values) so that primitive constant functions can be added without disturbing certain proofs related to the constant cases. However their typing rules, reduction rules, etc are defined in the same way.

Specifically, constants are defined through `p_const` and `p_op` in `WellTypedExp.thy`.

## 2.2 Expressions and Processes
Expressions `e` are defined by `p_exp` in `WellTypedExp.thy`. Notably, there is no specific case for memory values given. Memory location values are so similar to variables that they are both considered to be cases of `VarExp`, being differentiated based on `var_val_ref`, where `NoRef` corresponds to a variable and `SelfRef` and `OtherRef` correspond to memory locations (`SelfRef` assumes that a memory location value's owner is itself, which is useful to know syntactically for certain proofs).

Process sets are defined in their partial mapping form by `proc_set` in `ProcDef.thy`. It makes use of `gen_env`, a general datatype defined in `GenEnv.thy` for mapping strings to datatypes, in this case to expressions.

## 2.3 Values and Memory
Values `v` are defined by the predicate `is_value` in `WellTypedExp.thy`, where the `bin_op` function is formalized as `bin_const`. Another predicate `is_sexp` is defined as a useful superset of `is_value` that maintains most important typing properties of values.

Memory values `m` are defined as a datatype `mem_value` in `ReduceExp.thy`.

## 2.4 Semantics for Expressions

The semantics for reduction are defined by 



