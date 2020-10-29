/-
Copyright (c) 2020 Kevin Lacker, Keeley Hoek, Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Keeley Hoek, Scott Morrison
-/

import tactic.rewrite_search.backtrack
import tactic.rewrite_search.discovery
import tactic.rewrite_search.explain
import tactic.rewrite_search.types

/-!
# The core algorithm underlying rewrite search.
-/

universe u

open tactic

namespace tactic.rewrite_search

meta def mk_search_state (conf : config) (rs : list (expr × bool)) (lhs : expr) (rhs : expr) :
tactic search_state :=
do lhs_pp ← to_string <$> tactic.pp lhs,
rhs_pp ← to_string <$> tactic.pp rhs,
let left_root : vertex  := ⟨0, lhs, lhs_pp, side.L, none⟩,
let right_root : vertex := ⟨1, rhs, rhs_pp, side.R, none⟩,
return ⟨conf, rs, [left_root, right_root].to_buffer, 0, none⟩

variables (g : search_state)

namespace search_state

private meta def vertex_finder (pp : string) (left : vertex) (right : option vertex) :
option vertex :=
match right with
| some v := some v
| none   := if left.pp = pp then some left else none
end

-- Find the vertex with the given (e : expr), or return the null vertex if not found.
meta def find_vertex (e : expr) : tactic (option vertex) := do
  pp ← to_string <$> tactic.pp e,
  return (g.vertices.foldl none (vertex_finder pp))

meta def add_rewrite (v : vertex) (rw : rewrite) : tactic search_state :=
do maybe_v ← g.find_vertex rw.e,
match maybe_v with
  | some new_vertex := if vertex.same_side v new_vertex then return g
    else return { g with solving_edge := some ⟨v.id, new_vertex.id, rw.prf, rw.how⟩ }
  | none := do
    let new_vertex_id := g.vertices.size,
    let new_edge : edge := ⟨v.id, new_vertex_id, rw.prf, rw.how⟩,
    do pp ← to_string <$> tactic.pp rw.e,
    let new_vertex : vertex := ⟨new_vertex_id, rw.e, pp, v.s, (some new_edge)⟩,
    when_tracing `rewrite_search (trace format!"new edge: {v.pp} → {new_vertex.pp}"),
    return { g with vertices := g.vertices.push_back new_vertex }
end

meta def visit_vertex (v : vertex) : tactic search_state :=
do rws ← get_rewrites g.rs v.exp g.conf,
list.mfoldl (λ g rw, g.add_rewrite v rw) g rws.to_list

meta inductive status
| continue : status
| done : edge → status
| abort : string → status

meta def bfs_step : tactic (search_state × status) :=
if h : g.next_vertex < g.vertices.size then
  do let v := g.vertices.read' g.next_vertex,
  g ← g.visit_vertex v,
  return ({g with next_vertex := g.next_vertex + 1}, status.continue)
else return (g, status.abort "all vertices explored")

meta def step_once (itr : ℕ) : tactic (search_state × status) :=
match g.solving_edge with
| some e := return (g, status.done e)
| none := do
  if itr > g.conf.max_iterations then
    return (g, status.abort "max iterations reached")
  else g.bfs_step
end

meta def finish_search : tactic (search_state × search_result) :=
do (proof, units) ← build_proof g,
  return (g, search_result.success proof units)

meta def search_until_solved_aux : search_state → ℕ → tactic (search_state × search_result)
| g itr := do
  (g, s) ← g.step_once itr,
  match s with
  | status.continue := search_until_solved_aux g (itr + 1)
  | status.abort r  := return (g, search_result.failure ("aborted: " ++ r))
  | status.done e   := g.finish_search
  end

meta def search_until_solved : tactic (search_state × search_result) :=
g.search_until_solved_aux 0

meta def explain (proof : expr) (steps : list proof_unit) : tactic string :=
  explain_search_result g.conf g.rs proof steps

end search_state

end tactic.rewrite_search
