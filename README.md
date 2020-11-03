# perm_lang_ax1

This repository contains Isabelle theory files that formalize the definitions and proofs given in "Types for Enforcing Mutual Exclusion in a Higher-Order Language."

Note that this set of theory files are given as a proof of concept that demonstrate the correctness of our results, however they have not been refactored to be human-readable. Definitions are generally not organized in the same way as they are in the paper, and in some cases differ from the definitions given in the paper (in ways that are either directly proven to be equivalent, or which can otherwise be shown to be equivalent). Some of this is to facilitate simpler proofs, some of it is as an artifact of how the proofs were constructed.

This document serves as an index describing where definitions from the paper correspond to definitions in the theory, as well as any differences that may exist.

# 1 Overview

This section gives a general guide to the organization of the theory files. Skip to Section 2 for how definitions and theorems from the paper correspond to theories.

## 1.1 General definitions
Contain general definitions of permissions, types, permission + type environments, and various properties and lemmas over them.

- GenEnv.thy: A generalized environment type used to define type environments and memories.
- PermEnv.thy: Basic permission and permission environment related definitions.
- GenSubEnv.thy: Definitions for whether environments have domains that are subsets of one another.
- PermEnvEq.thy: Lemmas about equality for permission environments operations.
- PermEnvLeq.thy: Lemmas about ordering for permission environments operations.
- LiftEnv.thy: Definition and lemmas of permission environment lifting.
- PermEnvMisc.thy: Lemmas about lifting and disjointness for permission environments operations.
- TypeEnv.thy: Definitions of types and type environments.

## 1.2 Type definitions
Definitions and lemmas for the type system.

- WTMiscEnv.thy: Miscellaneous definitions used for the typing rules, as well as lemmas concerning function affinity.
- WellTypedExp.thy: Contains rules for our type system that differ from the typing rules given in the paper.
- WellTypedAlt.thy: The rules of our type system exactly as given in the paper (and a proof that our two rule constructions are equivalent).
- WTLemma.thy: General lemmas about well-typedness.

## 1.3 Flat permissions lemma
Definitions which are used to prove the "flat permissions lemma" (`infl_sexp_wp` in `FlatLemma.thy`), an important lemma about values.

- NormEnv.thy: Defines `norm_use_env`, which restricts the domain of one permission environment to another.
- DropEnv.thy: Defines `drop_use_env`, which defines permission environment dropping, an operation analogous to permission environment lifting.
- FlatCutEnv.thy: Defines `cut_use_env`, which removes use permissions from a permission environment.
- FlatLemma.thy: The flat permission lemma.

## 1.4 Safe substitution type preservation lemma
Definitions for the proof that substitution maintains well-typedness.

- SubstExp.thy: Defines substitution and related concepts (free variables, lambda variables, etc).
- SubstDropEnv.thy: Lemmas about well-typedness and permission environment dropping.
- SubstTPX.thy: Defines the main inductive hypothesis for our safe substitution proof.
- SafeSubRename.thy: Proves that renaming an expression in safe ways maintains well-typedness.
- SuperNormEnv.thy: Defines `super_norm_use_env`, a stricter version of `norm_use_env`.
- SafeSubstTPX.thy: The main proof that substitution with "safe" renaming maintains well-typedness.

## 1.5 Safe reduction of expressions
Case analysis proving that expression reductions that don't involve holes preserve well-typedness.

- DerefVars.thy: Defines memory location ownership.
- ReduceExp.thy: Defines the rules for reduction besides reduction in holes.
- SRRead.thy: Proves that the re-labelling of memory location owners performed during array reads preserves well-typedness.
- SRUseEnv.thy: Auxiliary definitions used to define the induction hypothesis for safe reduction.
- SafeRedUnpack.thy: The case for pair unpacking of safe reduction.
- SafeRedCV.thy: The case for all partially applied constant functions of safe reduction (uses the unpacking case).
- ReduceRestrX.thy: Definitions for restricting type environments to specific domains.
- SafeRedCase.thy: The case for all constants of safe reduction.
- SARES.thy: The main proof that reduction of expressions maintains well-typedness.

## 1.6 Memory map definitions
General definitions for memory maps

- ResMap.thy: Defines memory maps and short lemmas.
- ResMapDisj.thy: Exclusivity related definitions for memory maps.
- ResMapValid.thy: Specialized definitions used for defining a well-typed system.

## 1.7 Safe reduction of process sets
Case analysis proving that process set reduction preserve well-typedness.

- SafeRedLemma.thy: Proves reduction preserves well-typedness for the case of reduction in a hole.
- ProcCVars.thy: Defines `np_dom_use_env` which generates a permission environment based on variables contained in expressions, and `full_dom_use_env` which generates a permission environment based on expression variables and the memory locations owned by them.
- ProcHoleVars.thy: Defines a notion of free variables for holes.
- ReduceWTS.thy: Defines well-typedness for memory.
- ProcDef.thy: Defines reduction and well-typedness for process sets.
- ProcSendCase.thy: The case for sending / receiving memory locations for safe reduction of process sets.
- ProcLemma.thy: The main proof that reduction of process sets maintains well-typedness.

## 1.8 Mutual Exclusion
Short proof for the correctness of mutual exclusion

- ExclLemma.thy: The proof of the correctness of mutual exclusion.

# 2 Language Syntax and Semantics

## 2.1 Constants
Constants `c` are split into "constants" (which include primitive constant values and special function constants) and "operators" (function constants for primitive values) so that primitive constant functions can be added without disturbing certain proofs related to the constant cases. However their typing rules, reduction rules, etc are defined in the same way.

Specifically, constants are defined through `p_const` and `p_op` in `WellTypedExp.thy`.

## 2.2 Expressions and Processes
Expressions `e` are defined by `p_exp` in `WellTypedExp.thy`. Notably, there is no specific case for memory values given. Memory location values are so similar to variables that they are both considered to be cases of `VarExp`, being differentiated based on `var_val_ref`, where `NoRef` corresponds to a variable and `SelfRef` and `OtherRef` correspond to memory locations (`SelfRef` assumes that a memory location value's owner is itself, which is useful to know syntactically for certain proofs).

Process sets are defined in their partial mapping form by `proc_set` in `ProcDef.thy`. It makes use of `gen_env`, a general datatype defined in `GenEnv.thy` for mapping strings to datatypes, in this case to expressions.

## 2.3 Values and Memory
Values `v` are defined by the predicate `is_value` in `WellTypedExp.thy`, where the `bin_op` function is formalized as `bin_const`. Another predicate `is_sexp` is defined as a useful superset of `is_value` that maintains most important typing properties of values.

Memory values `m` are defined as a datatype `mem_value` in `ReduceExp.thy`. Memories `M` are defined as `p_state` in `ReduceExp.thy`.

## 2.4 Semantics for Expressions

Holes `h` are defined by `p_hole` in `SafeRedLemma.thy`. The semantics for reduction are defined by `full_red_exp` in `SafeRedLemma.thy`. The definition of `full_red_exp` makes heavy use of `app_red_exp`, which defines every reduction rule besides the rule for reduction on holes. `app_red_exp` is defined in `ReduceExp.thy`.

The `set_own` function for array reads corresponds to `ack_full_exp` defined in `SRRead.thy`. Note that the definition for renaming memory location owners is substantially more complicated than the one given in our paper, owing to the fact that we use the same set of strings for memory locations and program variables, and so an extra step of renaming lambda variables is required.

## 2.5 Semantics for Process Sets

The semantics for reduction on process sets is given by `red_proc_set` in `ProcDef.thy`.

# 3 Type System

## 3.1 Permissions

Permissions `p` are defined by `p_perm` in `PermEnv.thy`. Our ordering on permissions is defined by `leq_perm`. Permissions composition is defined by `union_perm`. Permission environments are defined by `perm_use_env`.

Our ordering on permission environments is defined as `leq_use_env` and composition of permission environments is defined by `comp_use_env`. Subtraction of permission environments. Subtraction of permission environment is defined by `diff_use_env`. Subtraction of individual permissions is actually not (directly) defined because it is unnecessary (it can still be obtained from combining `minus_perm` and `neg_perm`). However inspection of the definition of `diff_use_env` shows that it gives the same definition as given in the paper. All of these definitions are also contained in `PermEnv.thy`.

## 3.2 Types and Typing Judgments

The definition of a type `tau` is given by `p_type` in `TypeEnv.thy`. One difference from the paper of the datatype `p_aff` instead of a permission (`p_perm`) to define the affinity of a function. There is a direct correlation between affinities and permissions given by `as_aff`. The distinction exists only to force explicit conversion when we compare an affinity to another permission.

## 3.3 Typing Expressions

The rules of our type system are given by `well_typed` in `WellTypedExp.thy`. Note that these rules are different from the rules given in the paper in that the rules for weakening / strengthening the end permissions / requirements are directly baked into the rules. A definition of the rules exactly as given in the paper is given by `well_typed_alt` in `WellTypedAlt.thy`, and a proof of their equivalence to each other is given through `well_typed_equiv1` and `well_typed_equiv2`.

The definition of constant type signatures is given through `const_type` and `op_type`, and the definition of `req` (the minimal permission environments for types) is given by `req_type`. These definitions are also in `WellTypedExp.thy`.

Disjointness of permission environments is given by `disj_use_env` in `PermEnv.thy`. Again disjointness of individual permissions is not defined directly, but it can be shown that the definition of `disj_use_env` matches the one given in the paper.

Lifting of permission environments is given by `lift_use_env` in `LiftEnv.thy`.

## 3.4 Typing Memory

Array permission maps are not given an official definition, since they are just partial maps. Permission environment exclusivity is defined by `strong_disj_use_env` in `ResMapDisj.thy`. Exclusivity of array permission maps is defined by `disj_res_list` in `ReduceWTS.thy`. The rules for typing memory values are given by `well_typed_mem_value` in `ReduceWTS.thy`.

A memory map `f` is defined by `res_map` in `ResMap.thy`. Although resource maps are treated as partial environments, they are implemented through a stack like data structure. Exclusivity for resource maps then specifically is defined by `disj_nres_map` in `ResMapDisj.thy`.

Permission environment containment in memory is defined by `sub_use_env` in `GenSubEnv.thy`. The `well_typed_mem` definition given in the paper is defined as `well_typed_state` in `ReduceWTS.thy`. This definition differs from the definition given in the paper in that it includes the requirement that memory values be proper.

## 3.5 Typing Process Sets and Systems

The `well_typed_pset` definition given in the paper is defined as `well_typed_proc_set` in `ProcDef.thy`. It differs from the definition given in the paper in that it also includes the requirement that process bodies are proper.

Separation of a permission environment from a memory map is defined by `sep_nres_map` in `ResMapDisj.thy`. Memory ownership is defined by `path_lookup` in `DerefVars.thy`. The definition of a proper expression is given by `proper_exp` in `DerefVars.thy`, and the definition of a proper memory value is given by `proper_mem_value` in `ReduceWTS.thy`. 

The `well_typed_sys` definition given in the paper is defined as `well_typed_system` in `ProcDef.thy`. Note that the requirements that the memory value and process bodies be proper were already included in `well_typed_state` and `well_typed_pset`, and the requirement that all permission environments be contained within the memory `M` is given by `sub_nres_map`, defined in `ResMapDisj.thy`.

## 3.6 Results

The proof of Theorem 1 (Mutual Exclusion) is given by `excl_safe_lemma` in `ExclLemma.thy`. This proof is relatively simple in concept, although it does make use of several additional auxiliary definitions. It is suggested that the proof of Theorem 2 is examined before looking at the proof of Theorem 1.

The bulk of our theory is the proof of Theorem 2 (Type Preservation) is given by `safe_red_proc_set` in `ProcLemma.thy`. One notable assumption it makes not given in the paper is the assumption that `valid_reduct app_red_exp`, which is proven by `sares_valid` in `SARES.thy`. (These proofs are separated from each other because the proof of `sares_valid` takes several minutes to load).

The proof of `sares_valid` is based on `safe_app_red_exp_strict`, a proof that reductions on expressions not involving holes preserves well-typedness (with respect to several inductive constraints). Two of its cases, proven in lemmas `sares_lam_case` and `sares_fix_case` make substantial use of the lemma `safe_subst_type_preserve_x` defined in `SafeSubTPX.thy`, which asserts that substitution (defined with variables renamed to prevent lambda capture) preserves well-typedness.

Several typing manipulations are required for the proof of `safe_subst_type_preserve_x`. The main inductive hypothesis of it is defined by `subst_type_preserve_x` defined in `SubstTPX.thy`.



