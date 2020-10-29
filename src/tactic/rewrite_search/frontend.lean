/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek, Scott Morrison
-/

import tactic.rewrite_search.discovery
import tactic.rewrite_search.search

/-!
# Interactive versions of rewrite tactics and documentation
-/

namespace tactic.rewrite_search
open tactic.rewrite_search

meta def default_config : config := {}
meta def pick_default_config : tactic unit := `[exact tactic.rewrite_search.default_config]

meta def try_search (cfg : config) (rs : list (expr × bool)) (lhs : expr) (rhs : expr) :
tactic string :=
do i ← mk_search_state cfg rs lhs rhs,
  (i, result) ← i.search_until_solved,
  match result with
    | search_result.failure reason := tactic.fail reason
    | search_result.success proof steps := tactic.exact proof >> (i.explain proof steps)
  end

meta def rewrite_search_target (cfg : config) (extra_names : list name)
  (extra_rws : list (expr × bool)) : tactic string :=
do t ← tactic.target,
  if t.has_meta_var then
    tactic.fail "rewrite_search is not suitable for goals containing metavariables"
  else tactic.skip,

  rws ← collect_rw_lemmas cfg extra_names extra_rws,

  (lhs, rhs) ← rw_equation.split t,
  try_search cfg rws lhs rhs

end tactic.rewrite_search

namespace tactic.interactive

open lean.parser interactive interactive.types
open tactic.rewrite_search

/-- Search for a chain of rewrites to prove equations or iffs. -/
meta def rewrite_search (try_harder : parse $ optional (tk "!"))
  (cfg : config . pick_default_config) : tactic string :=
  rewrite_search_target cfg [] []

add_tactic_doc
{ name        := "rewrite_search",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.rewrite_search],
  tags        := ["rewrite", "automation"] }

meta def rewrite_search_with (try_harder : parse $ optional (tk "!")) (rs : parse rw_rules)
  (cfg : config . pick_default_config) : tactic string :=
do extra_rws ← rewrite_list_from_rw_rules rs.rules,
   rewrite_search_target cfg [] extra_rws  

-- Uncomment this after adding a docstring.
-- add_tactic_doc
-- { name        := "rewrite_search_with",
--   category    := doc_category.tactic,
--   decl_names  := [`tactic.interactive.rewrite_search_with],
--   tags        := ["rewrite", "automation"] }

meta def rewrite_search_using (try_harder : parse $ optional (tk "!")) (as : list name)
  (cfg : config . pick_default_config) : tactic string :=
do extra_names ← load_attr_list as,
   rewrite_search_target cfg extra_names []

-- Uncomment this after adding a docstring.
-- add_tactic_doc
-- { name        := "rewrite_search_using",
--   category    := doc_category.tactic,
--   decl_names  := [`tactic.interactive.rewrite_search_using],
--   tags        := ["rewrite", "automation"] }

end tactic.interactive
