/-
Copyright (c) 2018 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek, Scott Morrison
-/

import tactic.rewrite_all.congr

/-!
# Advanced rewriting tactics

This file provides three interactive tactics
that give the user more control over where to perform a rewrite.

## Main definitions

* `perform_nth_write n rules`: performs only the `n`th possible rewrite using the `rules`.
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

open tactic
open lean.parser
open interactive
open interactive.types

namespace tactic

open rewrite_all rewrite_all.congr

/--
Returns a lazy list of (t, n, k) where
* `t` is a `tracked_rewrite` (i.e. a pair `(e' : expr, prf : e = e')`)
* `n` is the index of the rule `r` used from `rs`, and
* `k` is the index of `t` in `all_rewrites r e`.
-/
meta def all_rewrites
  (rs : list (expr × bool)) (e : expr)
  (cfg : rewrite_all.cfg := {md := semireducible}) :
  mllist tactic (tracked_rewrite × ℕ × ℕ) :=
(mllist.of_list rs).enum.bind_ $ λ r,
   ((rewrite_all_lazy e r.2 cfg).enum).map (λ p, (p.2, p.1, r.1))

meta def get_nth_rewrite (r : expr × bool) (n : ℕ) : tactic tracked_rewrite :=
do e ← target,
   rewrites ← rewrite_all e r,
   rewrites.nth n

meta def nth_rewrite (r : expr × bool) (n : ℕ) : tactic unit :=
get_nth_rewrite r n >>= tracked_rewrite.replace_target

meta def all_rewrites_using (a : name) (e : expr) :
  tactic (list tracked_rewrite) :=
do names ← attribute.get_instances a,
   rules ← names.mmap mk_const,
   let pairs := rules.map (λ e, (e, ff)) ++ rules.map (λ e, (e, tt)),
   results ← pairs.mmap $ rewrite_all e,
   pure results.join

namespace interactive

private meta def unpack_rule (p : rw_rule) : tactic (expr × bool) :=
do r ← to_expr p.rule tt ff,
   return (r, p.symm)

private meta def get_nth_rewrite' (n : ℕ) (q : rw_rules_t) (e : expr) :
  tactic tracked_rewrite :=
do rewrites ← q.rules.mmap $ λ r, unpack_rule r >>= rewrite_all e,
   rewrites.join.nth n <|> fail format!"failed: not enough rewrites found"

meta def nth_rw_hyp (n : parse small_nat) (q : parse rw_rules) (h : expr) : tactic unit :=
do e ← infer_type h, get_nth_rewrite' n q e >>= tracked_rewrite.replace_hyp h

-- TODO (also allow (%%lhs ↔ %%_))
meta def nth_rw_hyp_lhs (n : parse small_nat) (q : parse rw_rules) (h : expr) : tactic unit :=
do `(%%lhs = %%_) ← infer_type h, get_nth_rewrite' n q lhs >>= tracked_rewrite.replace_hyp_lhs h

meta def nth_rw_hyp_rhs (n : parse small_nat) (q : parse rw_rules) (h : expr) : tactic unit :=
do `(%%_ = %%rhs) ← infer_type h, get_nth_rewrite' n q rhs >>= tracked_rewrite.replace_hyp_rhs h

meta def nth_rw_goal (n : parse small_nat) (q : parse rw_rules) : tactic unit :=
do e ← target, get_nth_rewrite' n q e >>= tracked_rewrite.replace_target

meta def nth_rw_goal_lhs (n : parse small_nat) (q : parse rw_rules) : tactic unit :=
do `(%%lhs = %%_) ← target, get_nth_rewrite' n q lhs >>= tracked_rewrite.replace_target_lhs

meta def nth_rw_goal_rhs (n : parse small_nat) (q : parse rw_rules) : tactic unit :=
do `(%%_ = %%rhs) ← target, get_nth_rewrite' n q rhs >>= tracked_rewrite.replace_target_rhs

/-- `perform_nth_write n rules` performs only the `n`th possible rewrite using the `rules`.

The core `rewrite` has a `occs` configuration setting intended to achieve a similar
purpose, but this doesn't really work. (If a rule matches twice, but with different
values of arguments, the second match will not be identified.)

See also: `nth_rewrite_lhs` and `nth_rewrite_rhs` -/
meta def nth_rewrite
  (n : parse small_nat) (q : parse rw_rules) (l : parse location) : tactic unit :=
match l with
| loc.wildcard := l.try_apply (nth_rw_hyp n q) (nth_rw_goal n q)
| _            := l.apply     (nth_rw_hyp n q) (nth_rw_goal n q)
end >> tactic.try (tactic.reflexivity reducible)
    >> (returnopt q.end_pos >>= save_info <|> skip)

/-- `nth_write_lhs n rules` performs only the `n`th possible rewrite using the `rules`,
but only working on the left hand side.

The core `rewrite` has a `occs` configuration setting intended to achieve a similar
purpose, but this doesn't really work. (If a rule matches twice, but with different
values of arguments, the second match will not be identified.)

See also: `nth_rewrite` and `nth_rewrite_rhs` -/
meta def nth_rewrite_lhs (n : parse small_nat) (q : parse rw_rules) (l : parse location) : tactic unit :=
match l with
| loc.wildcard := l.try_apply (nth_rw_hyp_lhs n q) (nth_rw_goal_lhs n q)
| _            := l.apply     (nth_rw_hyp_lhs n q) (nth_rw_goal_lhs n q)
end >> tactic.try (tactic.reflexivity reducible)
    >> (returnopt q.end_pos >>= save_info <|> skip)

/-- `nth_write_rhs n rules` performs only the `n`th possible rewrite using the `rules`,
but only working on the right hand side.

The core `rewrite` has a `occs` configuration setting intended to achieve a similar
purpose, but this doesn't really work. (If a rule matches twice, but with different
values of arguments, the second match will not be identified.)

See also: `nth_rewrite` and `nth_rewrite_lhs` -/
meta def nth_rewrite_rhs (n : parse small_nat) (q : parse rw_rules) (l : parse location) : tactic unit :=
match l with
| loc.wildcard := l.try_apply (nth_rw_hyp_rhs n q) (nth_rw_goal_rhs n q)
| _            := l.apply     (nth_rw_hyp_rhs n q) (nth_rw_goal_rhs n q)
end >> tactic.try (tactic.reflexivity reducible)
    >> (returnopt q.end_pos >>= save_info <|> skip)

end interactive
end tactic
