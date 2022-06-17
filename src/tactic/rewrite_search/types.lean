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

/--
`side` represents the side of an equation, either the left or the right.
-/
@[derive decidable_eq, derive inhabited]
inductive side
| L
| R

/-- Convert a side to a human-readable string. -/
meta def side.to_string : side → format
| side.L := "L"
| side.R := "R"

/-- Convert a side to the string "lhs" or "rhs", for use in tactic name generation. -/
def side.to_xhs : side → string
| side.L := "lhs"
| side.R := "rhs"

meta instance side.has_to_format : has_to_format side := ⟨side.to_string⟩

/--
A `how` contains information needed by the explainer to generate code for a rewrite.
`rule_index` denotes which rule in the static list of rules is used.
`location` describes which match of that rule was used, to work with `nth_rewrite`.
`addr` is a list of "left" and "right" describing which subexpression is rewritten.
-/
meta structure how := (rule_index : ℕ) (location : ℕ) (addr : option (list expr_lens.dir))

/-- Convert a `how` to a human-readable string. -/
meta def how.to_string : how → format
| h := format!"rewrite {h.rule_index} {h.location} {h.addr.iget.to_string}"

meta instance how.has_to_format : has_to_format how := ⟨how.to_string⟩

/-- `rewrite` represents a single step of rewriting, that proves `exp` using `proof`. -/
meta structure rewrite :=
(exp   : expr)
(proof : tactic expr) -- we defer constructing the proofs until they are needed
(how   : how)

/--
`proof_unit` represents a sequence of steps that can be applied to one side of the
equation to prove a particular expression.
-/
meta structure proof_unit :=
(proof : expr)
(side  : side)
(steps : list how)

/--
Configuration options for a rewrite search.
`max_iterations` controls how many vertices are expanded in the graph search.
`explain` generates Lean code to replace the call to `rewrite_search`.
`explain_using_conv` changes the nature of the explanation.
-/
meta structure config extends tactic.nth_rewrite.cfg :=
(max_iterations     : ℕ := 5000)
(explain_using_conv : bool := tt)

end tactic.rewrite_search

