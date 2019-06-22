-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Keeley Hoek, Scott Morrison

import .tactic
import .discovery

namespace tactic.interactive

open lean.parser interactive interactive.types
open tactic.rewrite_search

variables {α β γ δ : Type}

meta def rewrite_search (try_harder : parse $ optional (tk "!"))
  (cfg : config α β γ δ) : tactic string :=
  tactic.rewrite_search cfg try_harder.is_some

meta def rewrite_search_with (try_harder : parse $ optional (tk "!")) (rs : parse rw_rules)
  (cfg : config α β γ δ . pick_default_config) : tactic string :=
  tactic.rewrite_search_with rs.rules cfg try_harder.is_some

meta def rewrite_search_using (try_harder : parse $ optional (tk "!")) (as : list name)
  (cfg : config α β γ δ . pick_default_config) : tactic string :=
  tactic.rewrite_search_using as cfg try_harder.is_some

meta def simp_search (cfg : collect_cfg := {}) : tactic unit :=
  tactic.simp_search cfg

meta def simp_search_with (rs : parse rw_rules) (cfg : collect_cfg := {}) : tactic unit :=
  tactic.simp_search_with rs.rules cfg

end tactic.interactive
