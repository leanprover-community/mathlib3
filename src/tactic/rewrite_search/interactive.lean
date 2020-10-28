/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek, Scott Morrison
-/

import tactic.rewrite_search.module
import tactic.rewrite_search.discovery

/-!
# Interactive versions of rewrite tactics and documentation
-/

namespace tactic.rewrite_search

meta def rewrite_search_pair (cfg : config) (rs : list (expr × bool))
(eqn : sided_pair expr) : tactic string :=
do result ← try_search cfg rs eqn,
match result with
  | some str := return str
  | none := tactic.fail "Could not initialize rewrite_search instance."
end

meta def rewrite_search_target (cfg : config) (try_harder : bool)
  (extra_names : list name) (extra_rws : list (expr × bool)) : tactic string :=
do let cfg := if ¬try_harder then cfg
              else { cfg with try_simp := tt },
   t ← tactic.target,
   if t.has_meta_var then
     tactic.fail "rewrite_search is not suitable for goals containing metavariables"
   else tactic.skip,

   rws ← discovery.collect_rw_lemmas cfg extra_names extra_rws,

   (lhs, rhs) ← rw_equation.split t,
   rewrite_search_pair cfg rws ⟨lhs, rhs⟩

end tactic.rewrite_search

namespace tactic.interactive

open lean.parser interactive interactive.types
open tactic.rewrite_search

/-- Search for a chain of rewrites to prove equations or iffs. -/
meta def rewrite_search (try_harder : parse $ optional (tk "!"))
  (cfg : config . pick_default_config) : tactic string :=
  rewrite_search_target cfg try_harder.is_some [] []

add_tactic_doc
{ name        := "rewrite_search",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.rewrite_search],
  tags        := ["rewrite", "automation"] }

meta def rewrite_search_with (try_harder : parse $ optional (tk "!")) (rs : parse rw_rules)
  (cfg : config . pick_default_config) : tactic string :=
do extra_rws ← discovery.rewrite_list_from_rw_rules rs.rules,
   rewrite_search_target cfg try_harder.is_some [] extra_rws  

-- Uncomment this after adding a docstring.
-- add_tactic_doc
-- { name        := "rewrite_search_with",
--   category    := doc_category.tactic,
--   decl_names  := [`tactic.interactive.rewrite_search_with],
--   tags        := ["rewrite", "automation"] }

meta def rewrite_search_using (try_harder : parse $ optional (tk "!")) (as : list name)
  (cfg : config . pick_default_config) : tactic string :=
do extra_names ← discovery.load_attr_list as,
   rewrite_search_target cfg try_harder.is_some extra_names []

-- Uncomment this after adding a docstring.
-- add_tactic_doc
-- { name        := "rewrite_search_using",
--   category    := doc_category.tactic,
--   decl_names  := [`tactic.interactive.rewrite_search_using],
--   tags        := ["rewrite", "automation"] }

end tactic.interactive
