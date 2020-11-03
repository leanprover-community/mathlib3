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

namespace tactic.interactive

open lean.parser interactive interactive.types tactic.rewrite_search

/--
Collects rewrite rules, runs a graph search to find a chain of rewrites to prove the
current target, and generates a string explanation for it.
-/
private meta def rewrite_search_target (cfg : config) (rws : list rw_rule) :
  tactic string :=
do t ← tactic.target,
  if t.has_meta_var then
    tactic.fail "rewrite_search is not suitable for goals containing metavariables"
  else tactic.skip,
  rules ← collect_rules rws,
  g ← mk_graph cfg rules t,
  (_, proof, steps) ← g.find_proof,
  tactic.exact proof >> (explain_search_result cfg rules proof steps)

/-- A tactic to pick the default config. -/
meta def pick_default : tactic unit := `[exact tactic.rewrite_search.default_config]

/-- Search for a chain of rewrites to prove an equation or iff statement. -/
meta def rewrite_search (try_harder : parse $ optional (tk "!"))
  (cfg : config . pick_default) : tactic string :=
rewrite_search_target cfg []

add_tactic_doc
{ name        := "rewrite_search",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.rewrite_search],
  tags        := ["rewrite", "automation"] }

/--
Search for a chain of rewrites to prove an equation or iff statement.
Includes the rewrite rules specified in the same way as the `rw` tactic accepts.
-/
meta def rewrite_search_with (try_harder : parse $ optional (tk "!")) (rs : parse rw_rules)
  (cfg : config . pick_default) : tactic string :=
rewrite_search_target cfg rs.rules

add_tactic_doc
{ name        := "rewrite_search_with",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.rewrite_search_with],
  tags        := ["rewrite", "automation"] }

end tactic.interactive
