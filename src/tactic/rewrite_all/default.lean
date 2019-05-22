-- Copyright (c) 2018 Keeley Hoek. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Keeley Hoek, Scott Morrison

-- There are two alternative backends, provided by `.congr` and `.kabstract`.
--
-- The kabstract backend is faster, but if there are multiple identical occurences of the
-- same rewritable subexpression, all are rewritten simultaneously, and this isn't always
-- what we want.
-- (In particular, rewrite_search is much less capable on the category_theory library.)
import tactic.rewrite_all.congr tactic.rewrite_all.kabstract

open tactic
open lean.parser
open interactive

namespace tactic

open rewrite_all rewrite_all.congr

/--
return a lazy list of (t, n, k) where
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

meta def perform_nth_rewrite (r : expr × bool) (n : ℕ) : tactic unit :=
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

/--
`perform_nth_write n rules` performs only the `n`th possible rewrite using the `rules`.

The core `rewrite` has a `occs` configuration setting intended to achieve a similar
purpose, but this doesn't really work. (If a rule matches twice, but with different
values of arguments, the second match will not be identified.)
-/
meta def perform_nth_rewrite
  (n : parse small_nat) (q : parse rw_rules) : tactic unit :=
do e ← target,
   get_nth_rewrite' n q e >>= tracked_rewrite.replace_target,
   tactic.try tactic.reflexivity

/-- As for `perform_nth_rewrite`, but only working on the left hand side. -/
meta def nth_rewrite_lhs (n : parse small_nat) (q : parse rw_rules) : tactic unit :=
do `(%%lhs = %%_) ← target,
   get_nth_rewrite' n q lhs >>= tracked_rewrite.replace_target_lhs,
   tactic.try tactic.reflexivity

/-- As for `perform_nth_rewrite`, but only working on the right hand side. -/
meta def nth_rewrite_rhs (n : parse small_nat) (q : parse rw_rules) : tactic unit :=
do `(%%_ = %%rhs) ← target,
   get_nth_rewrite' n q rhs >>= tracked_rewrite.replace_target_rhs,
   tactic.try tactic.reflexivity

end interactive
end tactic
