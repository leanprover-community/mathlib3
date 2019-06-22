import .types
import .debug

open tactic

namespace tactic.rewrite_search

variables {α β γ δ : Type} (i : inst α β γ δ)

namespace backtrack

meta def backtrack_fn := inst α β γ δ → edge → tactic (list edge)

namespace naive

meta def walk_up_parents : vertex → option edge → tactic (list edge)
| v none     := return []
| v (some e) := do
                 w ← i.g.vertices.get e.f,
                 edges ← walk_up_parents w w.parent,
                 return (e :: edges)

meta def backtrack : backtrack_fn := λ (i : inst α β γ δ) (e : edge), do
  v ← i.g.vertices.get e.t,

  vts ← walk_up_parents i v e,
  vfs ← walk_up_parents i v v.parent,

  return $ match v.s with
              | side.L := vfs.reverse ++ vts
              | side.R := vts.reverse ++ vfs
              end

end naive

namespace bfs

meta def search_step (me : table_ref) : table edge → list edge → tactic (table edge × list table_ref)
| been [] := return (been, [])
| been (e :: rest) :=
  match e.other me with
  | none := fail "bad edge in adjacency table!"
  | some id := do
    (been, queue_head) ← pure $
      if been.present id ∨ id = LHS_VERTEX_ID then (been, [])
      else (been.set id e, [id]),
    (been, queue) ← search_step been rest,
    return (been, queue_head ++ queue)
  end

meta def search_aux : table edge → list table_ref → tactic (table edge)
| been [] := fail "bug: bfs could not find the path LHS -> RHS!"
| been (t :: rest) := do
  child ← i.g.vertices.get t,
  if child.id = RHS_VERTEX_ID then
    return been
  else do
    (been, new_es) ← search_step child.id been child.adj.to_list,
    search_aux been (rest ++ new_es)

meta def search : tactic (table edge) :=
  search_aux i (table.create i.g.vertices.length) [LHS_VERTEX_ID]

meta def crawl (t : table edge) : table_ref → tactic (list edge)
| id :=
  if id = LHS_VERTEX_ID then return [] else do
  match t.at_ref id with
  | none := fail "bug: broken chain while bfs crawling!"
  | some e :=
    match e.other id with
    | none := fail "bug: bad chain while bfs crawling!"
    | some oid := do
      rest ← crawl oid,
      return (e :: rest)
    end
  end

meta def backtrack : backtrack_fn := λ (i : inst α β γ δ) (_ : edge), do
-- We just disregard the "finishing edge" we are passed, looking for the
-- shortest path whatever instead.
  tab ← search i,
  list.reverse <$> crawl tab RHS_VERTEX_ID

end bfs

meta def chop_into_units : list edge → list (side × list edge)
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

meta def edges_to_unit : side × list edge → tactic proof_unit
| (_, []) := fail "empty edge list for unit!"
| (s, (e :: rest)) := do
  proof ← orient_proof s e.proof,
  edges_to_unit_aux s proof [e.how] rest

meta def build_units (l : list edge) : tactic (list proof_unit) :=
  (chop_into_units l).mmap edges_to_unit

meta def combine_units : list proof_unit → tactic (option expr)
| [] := return none
| (u :: rest) := do
  rest_proof ← combine_units rest,
  match rest_proof with
  | none            := return u.proof
  | some rest_proof := some <$> mk_eq_trans u.proof rest_proof
  end

meta def build_proof (e : edge) : tactic (expr × list proof_unit) := do
  let bt := if i.g.conf.optimal then bfs.backtrack i else naive.backtrack i,
  edges ← bt e,

  i.g.tracer_search_finished edges,

  units ← build_units edges,
  proof ← combine_units units,
  proof ← proof <|> fail "could not combine proof units!",

  if i.g.conf.trace_summary then do
    let vl := i.g.vertices.to_list,
    let saw := vl.length,
    let visited := (vl.filter (λ v : vertex, v.visited)).length,
    name ← decl_name,
    tactic.trace format!"rewrite_search (saw/visited/used) {saw}/{visited}/{edges.length} expressions during proof of {name}"
  else skip,

  return (proof, units)

end backtrack

end tactic.rewrite_search