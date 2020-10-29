/-
Copyright (c) 2020 Kevin Lacker, Keeley Hoek, Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Keeley Hoek, Scott Morrison
-/

import meta.rb_map
import tactic.rewrite_search.discovery
import tactic.rewrite_search.types

/-!
# The core algorithm underlying rewrite search.
-/

open tactic

namespace tactic.rewrite_search

meta structure edge :=
(fr to : ℕ)
(proof : tactic expr)
(how   : how)

meta def edge.to_string : edge → format
| e := format!"{e.fr} → {e.to}"

meta instance edge.has_to_format : has_to_format edge := ⟨edge.to_string⟩

meta structure vertex :=
(id     : ℕ)
(exp    : expr)
(pp     : string)
(side   : side)
(parent : option edge)

meta structure graph :=
(conf         : config)
(rules        : list (expr × bool))
(vertices     : buffer vertex)
(vmap         : native.rb_map string ℕ)
(solving_edge : option edge)

def LHS_VERTEX_ID : ℕ := 0
def RHS_VERTEX_ID : ℕ := 1

meta def mk_graph (conf : config) (rules : list (expr × bool)) (equation : expr) :
tactic graph :=
do (lhs, rhs) ← split_equation equation,
lhs_pp ← to_string <$> tactic.pp lhs,
rhs_pp ← to_string <$> tactic.pp rhs,
let lhs_vertex : vertex := ⟨0, lhs, lhs_pp, side.L, none⟩,
let rhs_vertex : vertex := ⟨1, rhs, rhs_pp, side.R, none⟩,
return ⟨conf, rules, [lhs_vertex, rhs_vertex].to_buffer,
        native.rb_map.of_list [(lhs_pp, 0), (rhs_pp, 1)], none⟩

variables (g : graph)

namespace graph

meta def get_vertex (i : ℕ) : tactic vertex :=
if h : i < g.vertices.size then return $ g.vertices.read (fin.mk i h)
else fail "invalid vertex access"

-- note: the returned edges are backwards
private meta def walk_up_parents : option edge → tactic (list edge)
| none     := return []
| (some e) := do
  trace format!"walking up edge {e}",
  v ← g.get_vertex e.fr,
  edges ← walk_up_parents v.parent,
  return (e :: edges)

-- Returns two lists. The first is a path from LHS to some interior vertex,
-- the second is a path from that interior vertex to the RHS.
-- On the second path, all the edges are backwards, since we originally found them
-- via searching backwards.
private meta def solution_paths : tactic (list edge × list edge) :=
do e ← g.solving_edge,
  v ← g.get_vertex e.to,
  path1 ← walk_up_parents g e,
  path2 ← walk_up_parents g v.parent,
  match v.side with
    | side.L := return (path2.reverse, path1)
    | side.R := return (path1.reverse, path2)
  end

private meta def add_rewrite (v : vertex) (rw : rewrite) : tactic graph :=
do pp ← to_string <$> tactic.pp rw.exp,
let maybe_id := g.vmap.find pp,
match maybe_id with
  | (some id) := do
    existing_vertex ← g.get_vertex id,
    if v.side = existing_vertex.side then return g
    else return { g with solving_edge := some ⟨v.id, existing_vertex.id, rw.proof, rw.how⟩ }
  | none := do
    let new_vertex_id := g.vertices.size,
    let new_edge : edge := ⟨v.id, new_vertex_id, rw.proof, rw.how⟩,
    let new_vertex : vertex := ⟨new_vertex_id, rw.exp, pp, v.side, (some new_edge)⟩,
    trace_if_enabled `rewrite_search format!"new edge: {v.pp} → {new_vertex.pp}",
    return { g with vertices := g.vertices.push_back new_vertex,
                    vmap := g.vmap.insert pp new_vertex_id }
end

private meta def expand_vertex (v : vertex) : tactic graph :=
do rws ← get_rewrites g.rules v.exp g.conf,
list.mfoldl (λ g rw, add_rewrite g v rw) g rws.to_list

private meta def find_solving_edge : graph → ℕ → tactic graph
| g vertex_id :=
if vertex_id ≥ g.conf.max_iterations then fail "search failed: max iterations reached"
else if h : vertex_id < g.vertices.size then
  do let v := g.vertices.read (fin.mk vertex_id h),
  g ← expand_vertex g v,
  match g.solving_edge with
    | some _ := return g
    | none   := find_solving_edge g (vertex_id + 1)
  end
else fail "search failed: all vertices explored"

private meta def proofs_for_edges (edges : list edge) : tactic (list expr) :=
edges.mmap (λ e, e.proof)

private meta def hows_for_edges (edges : list edge) : list how :=
edges.map (λ e, e.how)

private meta def flip_proofs (proofs : tactic (list expr)) : tactic (list expr) :=
do ps ← proofs, ps.mmap mk_eq_symm

-- Fails if the list is empty
private meta def combine_proofs (proofs : list expr) : tactic expr :=
match proofs with
  | []              := fail "programming error. cannot combine empty proof list"
  | (proof :: rest) := list.mfoldl mk_eq_trans proof rest
end

--- TODO: remove down to other TODO

private meta def orient_proof : side → tactic expr → tactic expr
| side.L proof := proof
| side.R proof := proof >>= mk_eq_symm

private meta def edges_to_unit_aux (s : side) : expr → list how → list edge → tactic proof_unit
| proof hows [] := return ⟨proof, s, hows⟩
| proof hows (e :: rest) := do
  new_proof ← orient_proof s e.proof >>= mk_eq_trans proof,
  edges_to_unit_aux new_proof (if s = side.L then hows ++ [e.how] else [e.how] ++ hows) rest

private meta def edges_to_unit : side × list edge → tactic proof_unit
| (_, []) := fail "empty edge list for unit!"
| (s, (e :: rest)) := do
  proof ← orient_proof s e.proof,
  edges_to_unit_aux s proof [e.how] rest

private meta def build_units : tactic (list proof_unit) :=
do (left_edges, right_edges) ← solution_paths g,
let chopped : list (side × list edge) := [⟨side.L, left_edges⟩, ⟨side.R, right_edges⟩],
let chopped := chopped.filter (λ pair, ¬ pair.2.empty),
chopped.mmap edges_to_unit

--- TODO: remove up to other TODO

private meta def build_proof : tactic (expr × list proof_unit) :=
do trace_if_enabled `rewrite_search "success!",
  units ← build_units g,
  proof ← combine_proofs $ units.map $ λ u, u.proof,
  return (proof, units)

meta def find_proof : tactic (graph × expr × list proof_unit) :=
do g ← find_solving_edge g 0,
(proof, units) ← build_proof g,
return (g, proof, units)

end graph

end tactic.rewrite_search
