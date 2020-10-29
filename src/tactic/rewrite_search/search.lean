/-
Copyright (c) 2020 Kevin Lacker, Keeley Hoek, Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Keeley Hoek, Scott Morrison
-/

import tactic.rewrite_search.discovery
import tactic.rewrite_search.types

/-!
# The core algorithm underlying rewrite search.
-/

universe u

open tactic

namespace tactic.rewrite_search

meta structure edge :=
(f t   : ℕ)
(proof : tactic expr)
(how   : how)

meta structure vertex :=
(id       : ℕ)
(exp      : expr)
(pp       : string)
(s        : side)
(parent   : option edge)

namespace vertex

meta def same_side (a b : vertex) : bool := a.s = b.s
meta def to_string (v : vertex) : string := v.s.to_string ++ v.pp

meta def create (id : ℕ) (e : expr) (pp : string) (s : side) (parent : option edge) : vertex :=
⟨ id, e, pp, s, parent ⟩

meta def null : vertex := vertex.create invalid_index (default expr) "__NULLEXPR" side.L none

meta instance inhabited : inhabited vertex := ⟨null⟩
meta instance has_to_format : has_to_format vertex := ⟨λ v, v.pp⟩

end vertex

meta structure search_state :=
(conf         : config)
(rs           : list (expr × bool))
(vertices     : buffer vertex)
(next_vertex  : ℕ)
(solving_edge : option edge)

def LHS_VERTEX_ID : ℕ := 0
def RHS_VERTEX_ID : ℕ := 1

meta def mk_search_state (conf : config) (rs : list (expr × bool)) (lhs : expr) (rhs : expr) :
tactic search_state :=
do lhs_pp ← to_string <$> tactic.pp lhs,
rhs_pp ← to_string <$> tactic.pp rhs,
let left_root : vertex  := ⟨0, lhs, lhs_pp, side.L, none⟩,
let right_root : vertex := ⟨1, rhs, rhs_pp, side.R, none⟩,
return ⟨conf, rs, [left_root, right_root].to_buffer, 0, none⟩

variables (g : search_state)

namespace search_state

private meta def walk_up_parents : option edge → tactic (list edge)
| none     := return []
| (some e) := do
  let w := g.vertices.read' e.f,
  edges ← walk_up_parents w.parent,
  return (e :: edges)

meta def backtrack : tactic (list edge) :=
do e ← g.solving_edge,
  let v := g.vertices.read' e.t,
  vts ← walk_up_parents g e,
  vfs ← walk_up_parents g v.parent,
  match v.s with
    | side.L := return (vfs.reverse ++ vts)
    | side.R := return (vts.reverse ++ vfs)
  end

private meta def vertex_finder (pp : string) (left : vertex) (right : option vertex) :
option vertex :=
match right with
  | some v := some v
  | none   := if left.pp = pp then some left else none
end

meta def find_vertex (e : expr) : tactic (option vertex) := do
  pp ← to_string <$> tactic.pp e,
  return (g.vertices.foldl none (vertex_finder pp))

private meta def add_rewrite (v : vertex) (rw : rewrite) : tactic search_state :=
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

meta def expand_vertex (v : vertex) : tactic search_state :=
do rws ← get_rewrites g.rs v.exp g.conf,
list.mfoldl (λ g rw, add_rewrite g v rw) g rws.to_list

meta def find_solving_edge : search_state → ℕ → tactic (search_state × edge)
| g vertex_idx :=
if vertex_idx ≥ g.conf.max_iterations then fail "search failed: max iterations reached"
else if h : vertex_idx < g.vertices.size then
  do let v := g.vertices.read (fin.mk vertex_idx h),
  g ← g.expand_vertex v,
  match g.solving_edge with
    | some e := return (g, e)
    | none   := find_solving_edge g (vertex_idx + 1)
  end
else fail "search failed: all vertices explored"

private meta def chop_into_units : list edge → list (side × list edge)
| [] := []
| [e] := [(if e.f = RHS_VERTEX_ID then side.R else side.L, [e])]
| (e₁ :: (e₂ :: rest)) :=
  match chop_into_units (e₂ :: rest) with
  | ((s, u) :: us) := if e₁.t = e₂.f ∨ e₁.f = e₂.t then
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

meta def find_proof : tactic (search_state × expr × list proof_unit) :=
do (g, e) ← g.find_solving_edge 0,
(proof, units) ← g.build_proof,
return (g, proof, units)

end search_state

end tactic.rewrite_search
