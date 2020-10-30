/-
Copyright (c) 2020 Kevin Lacker, Keeley Hoek, Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Keeley Hoek, Scott Morrison
-/

import tactic.nth_rewrite

/-!
# Types used in rewrite search.
-/

declare_trace rewrite_search

namespace tactic.rewrite_search

/-
`side` represents the side of an equation, either the left or the right.
-/
@[derive decidable_eq, derive inhabited]
inductive side
| L
| R

def side.other : side → side
| side.L := side.R
| side.R := side.L

meta def side.to_string : side → format
| side.L := "L"
| side.R := "R"

def side.to_xhs : side → string
| side.L := "lhs"
| side.R := "rhs"

meta instance side.has_to_format : has_to_format side := ⟨side.to_string⟩

/-
`how` contains information needed by the explainer to generate code for a rewrite.
-/
meta structure how := (rule_index : ℕ) (location : ℕ) (addr : option (list expr_lens.dir))

meta def how.to_string : how → format
| h := format!"rewrite {h.rule_index} {h.location} {h.addr.iget.to_string}"

meta instance how.has_to_format : has_to_format how := ⟨how.to_string⟩

/-
`rewrite` represents a single step of rewriting, that proves `exp` using `proof`.
-/
meta structure rewrite :=
(exp   : expr)
(proof : tactic expr) -- we defer constructing the proofs until they are needed
(how   : how)

/-
`proof_unit` represents a sequence of steps that can be applied to one side of the
equation to prove a particular expression.
-/
meta structure proof_unit :=
(proof : expr)
(side  : side)
(steps : list how)

/-
Configuration options for a rewrite search.
`max_iterations` controls how many vertices are expanded in the graph search.
`explain` generates Lean code to replace the call to `rewrite_search`.
`explain_using_conv` changes the nature of the explanation.
`inflate_rws` makes rewrite search consider more rewrites.
-/
meta structure config extends tactic.nth_rewrite.cfg :=
(max_iterations     : ℕ := 500)
(explain            : bool := ff)
(explain_using_conv : bool := tt)
(inflate_rws        : bool := ff)

meta def default_config : config := {}

/-
Split an equation (or an iff) into its left and right parts.
-/
meta def split_equation : expr → tactic (expr × expr)
| `(%%lhs = %%rhs) := return (lhs, rhs)
| `(%%lhs ↔ %%rhs) := return (lhs, rhs)
| _                := tactic.fail "target is not an equation or iff"

end tactic.rewrite_search

