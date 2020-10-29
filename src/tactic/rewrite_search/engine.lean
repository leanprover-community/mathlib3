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

-- Forcibly add a new vertex to the vertex buffer. You probably actually want to call
-- add_vertex, which will check that we haven't seen the vertex before first.
meta def alloc_vertex (e : expr) (root : bool) (s : side) : tactic (search_state × vertex) :=
do pp ← tactic.pp e,
let v : vertex := vertex.create g.vertices.size e (to_string pp) root s,
return ({ g with vertices := g.vertices.push_back v }, v)

-- Look up the given vertex associated to (e : expr), or create it if it is
-- not already present.
meta def add_vertex_aux (e : expr) (root : bool) (s : side) : tactic (search_state × vertex) :=
do maybe_v ← g.find_vertex e,
   match maybe_v with
   | none := do
     (g, v) ← g.alloc_vertex e root s,
     when_tracing `rewrite_search (trace format!"addV({to_string v.id}): {v.pp}"),
     return (g, v)
   | (some v) := return (g, v)
   end

meta def add_vertex (e : expr) (s : side) :=
g.add_vertex_aux e ff s

meta def add_root_vertex (e : expr) (s : side) :=
g.add_vertex_aux e tt s

meta def register_solved (e : edge) : search_state :=
{ g with solving_edge := some e }

meta def publish_parent (f t : vertex) (e : edge) : search_state × vertex :=
if t.root then
  (g, t)
else
  match t.parent with
  | some parent := (g, t)
  | none := g.set_vertex { t with parent := some e }
  end

meta def add_edge (f t : vertex) (proof : tactic expr) (how : how) :
tactic (search_state × edge) :=
do let new_edge : edge := ⟨ f.id, t.id, proof, how ⟩,
   when_tracing `rewrite_search
     (trace format!"addE: {to_string new_edge.f}→{to_string new_edge.t}"),
   let (g, t) := g.publish_parent f t new_edge,
   if ¬(vertex.same_side f t) then
     return (g.register_solved new_edge, new_edge)
   else
     return (g, new_edge)

meta def add_rewrite (v : vertex) (rw : rewrite) : tactic search_state :=
do (g, new_vertex) ← g.add_vertex rw.e v.s,
(g, e) ← g.add_edge v new_vertex rw.prf rw.how,
return g

meta def visit_vertex (v : vertex) : tactic search_state :=
if v.visited then return g else
do rws ← get_rewrites g.rs v.exp g.conf,
let (g, v) := g.set_vertex { v with visited := tt },
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

meta def mk_search_state (conf : config) (rs : list (expr × bool)) (lhs : expr) (rhs : expr) :
tactic search_state :=
do let g : search_state := ⟨conf, rs, buffer.nil, 0, none⟩,
   (g, vl) ← g.add_root_vertex lhs side.L,
   (g, vr) ← g.add_root_vertex rhs side.R,
   return g

end tactic.rewrite_search
