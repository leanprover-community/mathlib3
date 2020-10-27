/-
Copyright (c) 2020 Kevin Lacker, Keeley Hoek, Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Keeley Hoek, Scott Morrison
-/

import tactic.rewrite_search.common
import tactic.rewrite_search.engine
import tactic.rewrite_search.types

/-!
# Configuration and wrapper functions for rewrite search.
-/

namespace tactic.rewrite_search

meta def default_config : config := {}
meta def pick_default_config : tactic unit := `[exact tactic.rewrite_search.default_config]

meta def mk_search_state (conf : config) (rs : list (expr × bool)) (eqn : sided_pair expr) :
tactic search_state :=
do let g : search_state := ⟨conf, rs, bfs_init [], buffer.nil, buffer.nil, none⟩,
   (g, vl) ← g.add_root_vertex eqn.l side.L,
   (g, vr) ← g.add_root_vertex eqn.r side.R,
   return $ g.mutate_strat $ bfs_init [vl.id, vr.id, none]

meta def try_search (cfg : config) (rs : list (expr × bool)) (eqn : sided_pair expr) :
tactic (option string) :=
do i ← mk_search_state cfg rs eqn,
(i, result) ← i.search_until_solved,
match result with
  | search_result.failure reason := tactic.fail reason
  | search_result.success proof steps := tactic.exact proof >> some <$> i.explain proof steps
end

end tactic.rewrite_search
