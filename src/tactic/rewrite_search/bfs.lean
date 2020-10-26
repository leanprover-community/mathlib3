/-
Copyright (c) 2020 Kevin Lacker, Keeley Hoek, Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Keeley Hoek, Scott Morrison
-/
import tactic.rewrite_search.core

/-!
# A breadth-first-search algorithm for rewrite search.
-/

namespace tactic.rewrite_search

variables (g : search_state)

meta def bfs_init : tactic (init_result bfs_state) :=
init_result.pure ⟨{}, 1, []⟩

meta def bfs_startup (cfg : bfs_config) (g : search_state) (l r : vertex) :
tactic search_state :=
return $ g.mutate_strat ⟨cfg, 1, [l.id, r.id, none]⟩

meta def bfs_step (g : search_state) : tactic (search_state × status) := do
  let state := g.strat_state,
  if state.curr_depth > g.strat_state.conf.max_depth then
    return (g, status.abort "max bfs depth reached!")
  else match state.queue with
  | [] := return (g, status.abort "all vertices exhausted!")
  | (none :: rest) := do
    return (g.mutate_strat {state with queue := rest.concat none, curr_depth :=
                            state.curr_depth + 1}, status.repeat)
  | (some v :: rest) := do
    v ← g.vertices.get v,
    (g, it) ← g.visit_vertex v,
    (g, it, adjs) ← it.exhaust g,
    let adjs := adjs.filter $ λ u, ¬u.1.visited,
    return (g.mutate_strat {state with queue := rest.append $ adjs.map $ λ u, some u.1.id},
            status.continue)
  end

meta def bfs (conf : bfs_config := {}) : strategy :=
strategy.mk bfs_init (bfs_startup conf) bfs_step

end tactic.rewrite_search
