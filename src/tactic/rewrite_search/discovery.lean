/-
Copyright (c) 2018 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek
-/

import tactic.core

/-!
This file provides `find_all_rewrites`, a tactic for collecting all available
rewrites from the current environment (as well as some utility functions for
deciding if lemmas and hypotheses are usable as rewrites).

(It was originally written as part of `rewrite_search`, which we still haven't found
time to PR to mathlib, but I'm leaving this in the otherwise empty `rewrite_search`
folder on the presumption we'll eventually get there.)
-/

namespace tactic.rewrite_search.discovery

open tactic tactic.interactive

/--
Decide if a type represents a usable rewrite rule, in the forward and backward directions.

First, this checks that after binders the type is an `=` or an `↔`.
Second, we don't rewrite numerals.
-/
meta def is_acceptable_rewrite : expr → bool × bool
| (expr.pi n bi d b) := is_acceptable_rewrite b
| `(%%a = %%b)       := (a.to_nat.is_none, b.to_nat.is_none)
| `(%%a ↔ %%b)       := (a.to_nat.is_none, b.to_nat.is_none)
| _                  := (ff, ff)

/-- Check if a hypothesis can be used for rewriting. -/
meta def is_acceptable_hyp (r : expr) : tactic (bool × bool) :=
do t ← infer_type r >>= whnf, return $ if t.has_meta_var then (ff, ff) else is_acceptable_rewrite t

/-- Convert a list of `rw_rule`s into a list of pairs `expr × bool`,
representing the underlying rule, and
whether it should be used to rewrite in the reverse direction. -/
meta def rewrite_list_from_rw_rules (rws : list rw_rule) : tactic (list (expr × bool)) :=
rws.mmap (λ r, do e ← to_expr' r.rule, pure (e, r.symm))

/-- For each lemma `expr`, we try using it in both directions as a rewrite rule. -/
meta def rewrite_list_from_lemmas (l : list (expr × bool × bool)) : list (expr × bool) :=
(l.map (λ p : expr × bool × bool, match (p.2.1, p.2.2) with
  | (ff, ff) := []
  | (tt, ff) := [(p.1, ff)]
  | (ff, tt) := [(p.1, tt)]
  | (tt, tt) := [(p.1, ff), (p.1, tt)]
  end)).join

/--
Collect the local hypotheses which are usable as rewrite rules,
for each one recording that it can be used in both directions.
-/
meta def rewrite_list_from_hyps : tactic (list (expr × bool)) :=
do
  hyps ← local_context,
  acceptable_hyps ← hyps.mmap (λ h, do a ← is_acceptable_hyp h, return (h, a)),
  return $ rewrite_list_from_lemmas acceptable_hyps

/-- Test if a declaration can be used as a rewrite rule. -/
-- We signal success using `option` so this can be passed to `env.decl_filter_map`.
meta def is_rewrite_lemma (d : declaration) : option (declaration × bool × bool) :=
let a := is_acceptable_rewrite d.type in if ¬d.to_name.is_internal ∧ (a.1 ∨ a.2) then some (d, a) else none

/--
Obtain a list of all rewrite rules available in the current environment
(declarations and local hypothesis). Each element is a `expr` which can be
used to rewrite, along with a `bool` indicating whether it should be used in reverse.
-/
meta def find_all_rewrites : tactic (list (expr × bool)) :=
do
  e ← get_env,
  hyps ← rewrite_list_from_hyps,
  lemmas ← rewrite_list_from_lemmas <$>
    ((e.decl_filter_map is_rewrite_lemma).mmap (λ d, do n ← mk_const d.1.to_name, return (n, d.2))),
  return $ hyps ++ lemmas

end tactic.rewrite_search.discovery
