/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek, Scott Morrison
-/

import tactic.rewrite_search.tactic

/-!
# Interactive versions of rewrite tactics and documentation
-/

namespace tactic.interactive

open lean.parser interactive interactive.types
open tactic.rewrite_search

variables {α β γ δ : Type}

/-- Search for a chain of rewrites to prove equations or iffs. -/
meta def rewrite_search (try_harder : parse $ optional (tk "!"))
  (cfg : config α β γ δ . pick_default_config) : tactic string :=
  tactic.rewrite_search cfg try_harder.is_some

add_tactic_doc
{ name        := "rewrite_search",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.rewrite_search],
  tags        := ["rewrite", "automation"] }

meta def rewrite_search_with (try_harder : parse $ optional (tk "!")) (rs : parse rw_rules)
  (cfg : config α β γ δ . pick_default_config) : tactic string :=
  tactic.rewrite_search_with rs.rules cfg try_harder.is_some

-- Uncomment this after adding a docstring.
-- add_tactic_doc
-- { name        := "rewrite_search_with",
--   category    := doc_category.tactic,
--   decl_names  := [`tactic.interactive.rewrite_search_with],
--   tags        := ["rewrite", "automation"] }

meta def rewrite_search_using (try_harder : parse $ optional (tk "!")) (as : list name)
  (cfg : config α β γ δ . pick_default_config) : tactic string :=
  tactic.rewrite_search_using as cfg try_harder.is_some

-- Uncomment this after adding a docstring.
-- add_tactic_doc
-- { name        := "rewrite_search_using",
--   category    := doc_category.tactic,
--   decl_names  := [`tactic.interactive.rewrite_search_using],
--   tags        := ["rewrite", "automation"] }

end tactic.interactive
