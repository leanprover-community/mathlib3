/-
Copyright (c) 2020 Kevin Lacker, Keeley Hoek, Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Keeley Hoek, Scott Morrison
-/

import tactic.rewrite_search.types

/-!
# The backtracking component of rewrite search.
-/

open tactic

namespace tactic.rewrite_search

variables (g : search_state)

private meta def search_step (me : ℕ) :
buffer (option edge) → list edge → tactic (buffer (option edge) × list ℕ)
| been [] := return (been, [])
| been (e :: rest) :=
  match e.other me with
  | none := fail "bad edge in adjacency buffer!"
  | some id := do
    (been, queue_head) ← pure $
      if (been.read' id).is_some ∨ id = LHS_VERTEX_ID then (been, [])
      else (been.write' id (some e), [id]),
    (been, queue) ← search_step been rest,
    return (been, queue_head ++ queue)
  end

private meta def search_aux : buffer (option edge) → list ℕ → tactic (buffer (option edge))
| been [] := fail "bug: bfs could not find the path LHS -> RHS!"
| been (t :: rest) :=
do let child := g.vertices.read' t,
  if child.id = RHS_VERTEX_ID then
    return been
  else do
    (been, new_es) ← search_step child.id been child.adj.to_list,
    search_aux been (rest ++ new_es)

private meta def search : tactic (buffer (option edge)) :=
  search_aux g ⟨g.vertices.size, mk_array g.vertices.size none⟩ [LHS_VERTEX_ID]

private meta def crawl (t : buffer (option edge)) : ℕ → tactic (list edge)
| id :=
  if id = LHS_VERTEX_ID then return [] else do
  match t.read' id with
  | none := fail "bug: broken chain while bfs crawling!"
  | some e :=
    match e.other id with
    | none := fail "bug: bad chain while bfs crawling!"
    | some oid := do
      rest ← crawl oid,
      return (e :: rest)
    end
  end

private meta def backtrack : tactic (list edge) :=
do tab ← search g,
   list.reverse <$> crawl tab RHS_VERTEX_ID

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
do edges ← backtrack g,
  trace_if_enabled `rewrite_search "Done!",
  units ← build_units edges,
  proof ← combine_units units,
  proof ← proof <|> fail "could not combine proof units!",
  return (proof, units)

end tactic.rewrite_search
