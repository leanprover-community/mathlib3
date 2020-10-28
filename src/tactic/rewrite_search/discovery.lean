/-
Copyright (c) 2020 Kevin Lacker, Keeley Hoek, Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Keeley Hoek, Scott Morrison
-/
import tactic.nth_rewrite
import tactic.rewrite_search.common

/-!
# Generating a list of rewrites to use as steps in rewrite search.
-/

namespace tactic.rewrite_search.discovery

open tactic tactic.interactive tactic.rewrite_search

meta def assert_acceptable_lemma (r : expr) : tactic unit := do
  ret ← pure tt,
  if ret then return ()
  else do
    pp ← pp r,
    fail format!"\"{pp}\" is not a valid rewrite lemma!"

meta def load_attr_list : list name → tactic (list name)
| [] := return []
| (a :: rest) := do
  names ← attribute.get_instances a,
  l ← load_attr_list rest,
  return $ names ++ l

meta def load_names (l : list name) : tactic (list expr) :=
  l.mmap mk_const

meta def rewrite_list_from_rw_rules (rws : list rw_rule) : tactic (list (expr × bool)) :=
  rws.mmap (λ r, do e ← to_expr' r.rule, pure (e, r.symm))

meta def rewrite_list_from_lemmas (l : list expr) : list (expr × bool) :=
  l.map (λ e, (e, ff)) ++ l.map (λ e, (e, tt))

meta def rewrite_list_from_lemma (e : expr) : list (expr × bool) :=
  rewrite_list_from_lemmas [e]

/-- Returns true if expression is an equation or iff. -/
meta def is_acceptable_rewrite : expr → bool
| (expr.pi n bi d b) := is_acceptable_rewrite b
| `(%%a = %%b)       := tt
| `(%%a ↔ %%b)       := tt
| _                  := ff

/-- Returns true if the type of expression is an equation or iff
and does not contain metavariables. -/
meta def is_acceptable_hyp (r : expr) : tactic bool :=
  do t ← infer_type r >>= whnf, return $ is_acceptable_rewrite t ∧ ¬t.has_meta_var

meta def rewrite_list_from_hyps : tactic (list (expr × bool)) := do
  hyps ← local_context,
  rewrite_list_from_lemmas <$> hyps.mfilter is_acceptable_hyp

-- TODO mk_apps recursively
meta def inflate_under_apps (locals : list expr) : expr → tactic (list expr)
| e := do
  rws ← list.map prod.fst <$> mk_apps e locals,
  rws_extras ← list.join <$> rws.mmap inflate_under_apps,
  return $ e :: (rws ++ rws_extras)

meta def inflate_rw (locals : list expr) : expr × bool → tactic (list (expr × bool))
| (e, sy) := do
  as ← inflate_under_apps locals e,
  return $ as.map $ λ a, (a, sy)

meta def is_rewrite_lemma (d : declaration) : option (name × expr) :=
  let t := d.type in if is_acceptable_rewrite t then some (d.to_name, t) else none

meta def find_all_rewrites : tactic (list (name × expr)) := do
  e ← get_env,
  return $ e.decl_filter_map is_rewrite_lemma

@[user_attribute]
meta def search_attr : user_attribute := {
  name := `search,
  descr := "declare that this definition should be considered by `rewrite_search`",
}

meta def collect (extra_names : list name) : tactic (list (expr × bool)) :=
do names ← attribute.get_instances `search,
   exprs ← load_names $ names ++ extra_names,
   exprs.mmap assert_acceptable_lemma,
   return $ rewrite_list_from_lemmas exprs

meta def collect_rw_lemmas (cfg : config) (extra_names : list name)
(extra_rws : list (expr × bool)) : tactic (list (expr × bool)) :=
do rws ← collect extra_names,
   hyp_rws ← rewrite_list_from_hyps,
   let rws := rws ++ extra_rws ++ hyp_rws,

   locs ← local_context,
   if cfg.inflate_rws then list.join <$> (rws.mmap $ inflate_rw locs)
   else pure rws

end tactic.rewrite_search.discovery
