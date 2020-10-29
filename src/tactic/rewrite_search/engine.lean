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

private meta def read_option {α : Type u} (buf : buffer α) (i : ℕ) : option α :=
if h : i < buf.size then some (buf.read (fin.mk i h)) else none

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

meta def add_adj (v : vertex) (e : edge) : search_state × vertex :=
g.set_vertex { v with adj := v.adj.push_back e }

meta def publish_parent (f t : vertex) (e : edge) : search_state × vertex :=
if t.root then
  (g, t)
else
  match t.parent with
  | some parent := (g, t)
  | none := g.set_vertex { t with parent := some e }
  end

meta def add_edge (f t : vertex) (proof : tactic expr) (how : how) :
tactic (search_state × vertex × vertex × edge) :=
do let new_edge : edge := ⟨ f.id, t.id, proof, how ⟩,
   when_tracing `rewrite_search
     (trace format!"addE: {to_string new_edge.f}→{to_string new_edge.t}"),
   let (g, f) := g.add_adj f new_edge,
   let (g, t) := g.add_adj t new_edge,
   let (g, t) := g.publish_parent f t new_edge,
   if ¬(vertex.same_side f t) then
     return (g.register_solved new_edge, f, t, new_edge)
   else
     return (g, f, t, new_edge)

meta def commit_rewrite (f : vertex) (r : rewrite) :
tactic (search_state × vertex × (vertex × edge)) :=
do (g, v) ← g.add_vertex r.e f.s,
  (g, f, v, e) ← g.add_edge f v r.prf r.how,
  return (g, f, (v, e))

meta def reveal_more_adjs (v : vertex) : tactic (search_state × option (vertex × edge)) :=
match read_option v.rws v.rw_front with
  | none := return (g, none)
  | some rw := do
    (g, v, pair) ← g.commit_rewrite v rw,
    (g, v) ← pure $ g.set_vertex {v with rw_front := v.rw_front + 1},
    return (g, some pair)
end

meta def process (orig : ℕ) (front : ℕ) : tactic (search_state × ℕ × option (vertex × edge)) :=
do let o := g.vertices.read' orig,
match read_option o.adj front with
  | some e := do
    let v := g.vertices.read' e.t,
    return (g, front + 1, some (v, e))
  | none := do
    (g, ret) ← g.reveal_more_adjs o,
    match ret with
    | some (v, e) := return (g, front + 1, some (v, e))
    | none := return (g, front, none)
    end
  end

meta def exhaust : search_state → vertex → ℕ → tactic (search_state  × list (vertex × edge))
| g v edge_idx := do
  (g, edge_idx, ret) ← g.process v.id edge_idx,
  match ret with
  | none := return (g, [])
  | some pair := do
    (g, rest) ← g.exhaust v edge_idx,
    return (g, (pair :: rest))
  end

meta def visit_vertex (v : vertex) : tactic (search_state × list (vertex × edge)) :=
if v.visited then return (g, []) else
do rws ← get_rewrites g.rs v.exp g.conf,
let (g, v) := g.set_vertex { v with rws := rws, visited := tt },
g.exhaust v 0

meta inductive status
| continue : status
| done : edge → status
| abort : string → status

meta def bfs_step : tactic (search_state × status) :=
match g.queue with
  | [] := return (g, status.abort "all vertices exhausted!")
  | (v :: rest) := do
    let v := g.vertices.read' v,
    (g, adjs) ← g.visit_vertex v,
    return (g.set_queue $ rest.append $ adjs.map $ λ u, u.1.id, status.continue)
end

meta def step_once (itr : ℕ) : tactic (search_state × status) :=
match g.solving_edge with
| some e := return (g, status.done e)
| none := do
  if itr > g.conf.max_iterations then
    return (g, status.abort "max iterations reached!")
  else do
    (g, s) ← g.bfs_step,
    return (g, s)
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
