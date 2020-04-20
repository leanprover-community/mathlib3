/-
Copyright (c) 2018 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek, Scott Morrison
-/

import tactic.nth_rewrite.congr

/-!
# Advanced rewriting tactics

This file provides three interactive tactics
that give the user more control over where to perform a rewrite.

## Main definitions

* `nth_write n rules`: performs only the `n`th possible rewrite using the `rules`.
* `nth_rewrite_lhs`: as above, but only rewrites on the left hand side of an equation or iff.
* `nth_rewrite_rhs`: as above, but only rewrites on the right hand side of an equation or iff.

## Implementation details

There are two alternative backends, provided by `.congr` and `.kabstract`.
The kabstract backend is not currently available through mathlib.

The kabstract backend is faster, but if there are multiple identical occurences of the
same rewritable subexpression, all are rewritten simultaneously,
and this isn't always what we want.
(In particular, `rewrite_search` is much less capable on the `category_theory` library.)
-/

open tactic lean.parser interactive interactive.types

namespace tactic

/-- Returns the target of the goal when passed `none`,
otherwise, return the type of `h` in `some h`. -/
meta def target_or_hyp_type : option expr → tactic expr
| none     := target
| (some h) := infer_type h

/-- Replace the target, or a hypothesis, depending on whether `none` or `some h` is given as the
first argument. -/
meta def replace_in_state : option expr → expr → expr → tactic unit
| none     := tactic.replace_target
| (some h) := λ e p, tactic.replace_hyp h e p >> skip

open nth_rewrite nth_rewrite.congr nth_rewrite.tracked_rewrite
open tactic.interactive

/-- Preprocess a rewrite rule for use in `get_nth_rewrite`. -/
private meta def unpack_rule (p : rw_rule) : tactic (expr × bool) :=
do r ← to_expr p.rule tt ff,
   return (r, p.symm)

/-- Get the `n`th rewrite of rewrite rules `q` in expression `e`,
or fail if there are not enough such rewrites. -/
meta def get_nth_rewrite (n : ℕ) (q : rw_rules_t) (e : expr) : tactic tracked_rewrite :=
do rewrites ← q.rules.mmap $ λ r, unpack_rule r >>= nth_rewrite e,
   rewrites.join.nth n <|> fail "failed: not enough rewrites found"

private def rel_descent_instructions : option side → list side
| none := []
| (some side.L) := [side.L, side.R]
| (some side.R) := [side.R]

/-- Rewrite the `n`th occurence of the rewrite rules `q` (optionally on a side) of a hypothesis or
target `h` which is an application of a relation. -/
meta def get_nth_rewrite_in_rel
  (n : ℕ) (q : rw_rules_t) (s : option side) (h : option expr) : tactic tracked_rewrite :=
do e ← target_or_hyp_type h,
   (ln, new_e) ← expr_lens.entire.zoom (rel_descent_instructions s) e,
   rw ← get_nth_rewrite n q new_e,
   return ⟨ln.fill rw.exp, rw.proof >>= ln.congr, rw.addr.map $ λ l, s.to_list ++ l⟩

/-- Rewrite the `n`th occurence of the rewrite rules `q` (optionally on a side)
at all the locations `loc`. -/
meta def nth_rewrite_core (s : option side) (n : parse small_nat) (q : parse rw_rules)
  (l : parse location) : tactic unit :=
do let fn := λ h, get_nth_rewrite_in_rel n q s h >>= λ rw, rw.proof >>= replace_in_state h rw.exp,
   match l with
   | loc.wildcard := l.try_apply (fn ∘ some) (fn none)
   | _            := l.apply     (fn ∘ some) (fn none)
   end,
   tactic.try (tactic.reflexivity reducible),
   (returnopt q.end_pos >>= save_info <|> skip)

namespace interactive

/-- `nth_write n rules` performs only the `n`th possible rewrite using the `rules`.

The core `rewrite` has a `occs` configuration setting intended to achieve a similar
purpose, but this doesn't really work. (If a rule matches twice, but with different
values of arguments, the second match will not be identified.)

See also: `nth_rewrite_lhs` and `nth_rewrite_rhs` -/
meta def nth_rewrite
  (n : parse small_nat) (q : parse rw_rules) (l : parse location) : tactic unit :=
nth_rewrite_core none n q l

/-- `nth_write_lhs n rules` performs only the `n`th possible rewrite using the `rules`,
but only working on the left hand side.

The core `rewrite` has a `occs` configuration setting intended to achieve a similar
purpose, but this doesn't really work. (If a rule matches twice, but with different
values of arguments, the second match will not be identified.)

See also: `nth_rewrite` and `nth_rewrite_rhs` -/
meta def nth_rewrite_lhs (n : parse small_nat) (q : parse rw_rules) (l : parse location) : tactic unit :=
nth_rewrite_core (some side.L) n q l

/-- `nth_write_rhs n rules` performs only the `n`th possible rewrite using the `rules`,
but only working on the right hand side.

The core `rewrite` has a `occs` configuration setting intended to achieve a similar
purpose, but this doesn't really work. (If a rule matches twice, but with different
values of arguments, the second match will not be identified.)

See also: `nth_rewrite` and `nth_rewrite_lhs` -/
meta def nth_rewrite_rhs (n : parse small_nat) (q : parse rw_rules) (l : parse location) : tactic unit :=
nth_rewrite_core (some side.R) n q l

end interactive
end tactic
