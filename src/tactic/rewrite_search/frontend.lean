/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek, Scott Morrison
-/

import tactic.rewrite_search.explain
import tactic.rewrite_search.discovery
import tactic.rewrite_search.search

/-!
# Interactive versions of rewrite tactics and documentation
-/

namespace tactic.rewrite_search
open tactic.rewrite_search

meta def default_config : config := {}
meta def pick_default_config : tactic unit := `[exact tactic.rewrite_search.default_config]

meta def rewrite_search_target (cfg : config) (extra_names : list name)
  (extra_rws : list (expr × bool)) : tactic string :=
do t ← tactic.target,
  if t.has_meta_var then
    tactic.fail "rewrite_search is not suitable for goals containing metavariables"
  else tactic.skip,

  rules ← collect_rw_lemmas cfg extra_names extra_rws,

  g ← mk_graph cfg rules t,
  (_, proof, steps) ← g.find_proof,
  tactic.exact proof >> (explain_search_result cfg rules proof steps)

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
