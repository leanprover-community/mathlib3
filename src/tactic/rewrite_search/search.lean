/-
Copyright (c) 2020 Kevin Lacker, Keeley Hoek, Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Keeley Hoek, Scott Morrison
-/

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
return $ match v.s with
           | side.L := vfs.reverse ++ vts
           | side.R := vts.reverse ++ vfs
end

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
  do let v := g.vertices.read (fin.mk g.next_vertex h),
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

meta def explain (proof : expr) (units : list proof_unit) : tactic string :=
  explain_search_result g.conf g.rs proof units

end search_state

end tactic.rewrite_search
