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

meta def mk_graph (conf : config) (rules : list (expr × bool)) (lhs : expr) (rhs : expr) :
tactic graph :=
do lhs_pp ← to_string <$> tactic.pp lhs,
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

private meta def walk_up_parents : option edge → tactic (list edge)
| none     := return []
| (some e) := do
  w ← g.get_vertex e.fr,
  edges ← walk_up_parents w.parent,
  return (e :: edges)

meta def backtrack : tactic (list edge) :=
do e ← g.solving_edge,
  v ← g.get_vertex e.to,
  vts ← walk_up_parents g e,
  vfs ← walk_up_parents g v.parent,
  match v.side with
    | side.L := return (vfs.reverse ++ vts)
    | side.R := return (vts.reverse ++ vfs)
  end

private meta def add_rewrite (v : vertex) (rw : rewrite) : tactic graph :=
do pp ← to_string <$> tactic.pp rw.e,
let maybe_id := g.vmap.find pp,
match maybe_id with
  | (some id) := do
    existing_vertex ← g.get_vertex id,
    if v.side = existing_vertex.side then return g
    else return { g with solving_edge := some ⟨v.id, existing_vertex.id, rw.prf, rw.how⟩ }
  | none := do
    let new_vertex_id := g.vertices.size,
    let new_edge : edge := ⟨v.id, new_vertex_id, rw.prf, rw.how⟩,
    let new_vertex : vertex := ⟨new_vertex_id, rw.e, pp, v.side, (some new_edge)⟩,
    when_tracing `rewrite_search (trace format!"new edge: {v.pp} → {new_vertex.pp}"),
    return { g with vertices := g.vertices.push_back new_vertex,
                    vmap := g.vmap.insert pp new_vertex_id }
end

meta def expand_vertex (v : vertex) : tactic graph :=
do rws ← get_rewrites g.rules v.exp g.conf,
list.mfoldl (λ g rw, add_rewrite g v rw) g rws.to_list

meta def find_solving_edge : graph → ℕ → tactic (graph × edge)
| g vertex_id :=
if vertex_id ≥ g.conf.max_iterations then fail "search failed: max iterations reached"
else if h : vertex_id < g.vertices.size then
  do let v := g.vertices.read (fin.mk vertex_id h),
  g ← g.expand_vertex v,
  match g.solving_edge with
    | some e := return (g, e)
    | none   := find_solving_edge g (vertex_id + 1)
  end
else fail "search failed: all vertices explored"

private meta def chop_into_units : list edge → list (side × list edge)
| [] := []
| [e] := [(if e.fr = RHS_VERTEX_ID then side.R else side.L, [e])]
| (e₁ :: (e₂ :: rest)) :=
  match chop_into_units (e₂ :: rest) with
  | ((s, u) :: us) := if e₁.to = e₂.fr ∨ e₁.fr = e₂.to then
                        ((s, e₁ :: u) :: us)
                      else
                        ((s.other, [e₁]) :: ((s, u) :: us))
  | _ := [] -- Unreachable
  end

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

private meta def build_units (l : list edge) : tactic (list proof_unit) :=
  (chop_into_units l).mmap edges_to_unit

private meta def combine_units : list proof_unit → tactic (option expr)
| [] := return none
| (u :: rest) := do
  rest_proof ← combine_units rest,
  match rest_proof with
  | none            := return u.proof
  | some rest_proof := some <$> mk_eq_trans u.proof rest_proof
  end

meta def build_proof : tactic (expr × list proof_unit) :=
do edges ← g.backtrack,
  trace_if_enabled `rewrite_search "Done!",
  units ← build_units edges,
  proof ← combine_units units,
  proof ← proof <|> fail "could not combine proof units!",
  return (proof, units)

meta def find_proof : tactic (graph × expr × list proof_unit) :=
do (g, e) ← g.find_solving_edge 0,
(proof, units) ← g.build_proof,
return (g, proof, units)

end graph

end tactic.rewrite_search
