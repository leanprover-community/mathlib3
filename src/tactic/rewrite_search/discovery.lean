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

/-- Decide if a type represents a usable rewrite rule. -/
meta def is_acceptable_rewrite (t : expr) : bool :=
t.is_eq_or_iff_after_binders

/-- Check if a hypothesis can be used for rewriting. -/
meta def is_acceptable_hyp (r : expr) : tactic bool :=
do t ← infer_type r >>= whnf, return $ is_acceptable_rewrite t ∧ ¬t.has_meta_var

/-- Convert a list of `rw_rule`s into a list of pairs `expr × bool`,
representing the underlying rule, and
whether it should be used to rewrite in the reverse direction. -/
meta def rewrite_list_from_rw_rules (rws : list rw_rule) : tactic (list (expr × bool)) :=
rws.mmap (λ r, do e ← to_expr' r.rule, pure (e, r.symm))

/-- For each lemma `expr`, we try using it in both directions as a rewrite rule. -/
meta def rewrite_list_from_lemmas (l : list expr) : list (expr × bool) :=
l.map (λ e, (e, ff)) ++ l.map (λ e, (e, tt))

/--
Collect the local hypotheses which are usable as rewrite rules,
for each one recording that it can be used in both directions.
-/
meta def rewrite_list_from_hyps : tactic (list (expr × bool)) :=
do
  hyps ← local_context,
  rewrite_list_from_lemmas <$> hyps.mfilter is_acceptable_hyp

/-- Test if a declaration can be used as a rewrite rule. -/
-- We signal success using `option` so this can be passed to `env.decl_filter_map`.
meta def is_rewrite_lemma (d : declaration) : option declaration :=
if ¬d.to_name.is_internal ∧ is_acceptable_rewrite d.type then some d else none

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
    (e.decl_filter_map is_rewrite_lemma).mmap (λ d, mk_const d.to_name),
  return $ hyps ++ lemmas

end tactic.rewrite_search.discovery
