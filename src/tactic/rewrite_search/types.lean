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

@[derive decidable_eq, derive inhabited]
inductive side
| L
| R

def side.other : side → side
| side.L := side.R
| side.R := side.L

def side.to_string : side → string
| side.L := "L"
| side.R := "R"

def side.to_xhs : side → string
| side.L := "lhs"
| side.R := "rhs"

instance : has_to_string side := ⟨side.to_string⟩

meta structure how := (rule_index : ℕ) (location : ℕ) (addr : option (list expr_lens.dir))

meta def how.to_string : how → format
| h := format!"rewrite {h.rule_index} {h.location} {h.addr.iget.to_string}"

meta instance how.has_to_format : has_to_format how := ⟨how.to_string⟩

meta structure rewrite :=
(exp   : expr)
(proof : tactic expr) -- we defer constructing the proofs until they are needed
(how   : how)

meta structure proof_unit :=
(proof : expr)
(side : side)
(steps : list how)

/-
Configuration options for a rewrite search.
-/
meta structure config extends tactic.nth_rewrite.cfg :=
(max_iterations     : ℕ := 500)
(explain            : bool := ff)
(explain_using_conv : bool := tt)
(suggest            : list name := [])
(inflate_rws        : bool := ff)
(help_me            : bool := ff)

meta def split_equation : expr → tactic (expr × expr)
| `(%%lhs = %%rhs) := return (lhs, rhs)
| `(%%lhs ↔ %%rhs) := return (lhs, rhs)
| _                := tactic.fail "target is not an equation or iff"

end tactic.rewrite_search

