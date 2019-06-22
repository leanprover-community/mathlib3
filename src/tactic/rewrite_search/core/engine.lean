import lib.string

import .types
import .debug
import .backtrack
import .explain

universe u

namespace tactic.rewrite_search

variables {α β γ δ : Type} (i : inst α β γ δ) (g : search_state α β γ δ) (m : metric α β γ δ)

private meta def chop : list char → list string → list string
| [] l := l
| (c :: rest) l := chop rest $ list.join $ l.map $ string.split_on c

meta def tokenise_expr (e : expr) : tactic (string × list string) := do
  pp ← to_string <$> tactic.pp e,
  pure (pp, chop [' '/-, '(', ')'-/] [pp])

namespace search_state

meta def unmark_all_visited : tactic (search_state α β γ δ) := do
  return { g with vertices := g.vertices.map $ λ v, {v with visited := ff} }

meta def reset_estimate (init : init_bound_fn α β γ δ) (de : dist_estimate γ) : tactic (dist_estimate γ) := do
  (vl, vr) ← g.get_estimate_verts de,
  return de

meta def reset_all_estimates (init : init_bound_fn α β γ δ) : tactic (search_state α β γ δ) := do
  new_estimates ← g.estimates.mmap $ g.reset_estimate init,
  return { g with estimates := new_estimates }

private meta def register_tokens_aux (s : side) : table token → list string → table token × list table_ref
| tokens [] := (tokens, [])
| tokens (tstr :: rest) := do
  let (tokens, t) := find_or_create_token tokens s tstr,
  let (tokens, l) := register_tokens_aux tokens rest,
  (tokens, t.id :: l)

meta def register_tokens (s : side) (strs : list string) : search_state α β γ δ × list table_ref :=
  let (new_tokens, refs) := register_tokens_aux s g.tokens strs in
  ({g with tokens := new_tokens}, refs)

private meta def find_vertex_aux (pp : string) : list vertex → option vertex
| [] := none
| (a :: rest) := if a.pp = pp then some a else find_vertex_aux rest

-- Find the vertex with the given (e : expr), or return the null verterx if not
-- found.
meta def find_vertex (e : expr) : tactic (option vertex) := do
  pp ← to_string <$> tactic.pp e,
  return (g.vertices.find_key pp)

-- Forcibly add a new vertex to the vertex table. You probably actually want to call
-- add_vertex, which will check that we haven't seen the vertex before first.
meta def alloc_vertex (e : expr) (root : bool) (s : side) : tactic (search_state α β γ δ × vertex) :=
do (pp, tokens) ← tokenise_expr e,
   let (g, token_refs) := g.register_tokens s tokens,
   let v : vertex := vertex.create g.vertices.next_id e pp token_refs root s,
   return ({ g with vertices := g.vertices.alloc v }, v)

-- Look up the given vertex associated to (e : expr), or create it if it is
-- not already present.
meta def add_vertex_aux (e : expr) (root : bool) (s : side) : tactic (search_state α β γ δ × vertex) :=
do maybe_v ← g.find_vertex e,
   match maybe_v with
   | none := do
     (g, v) ← g.alloc_vertex e root s,
     g.tracer_vertex_added v,
     return (g, v)
   | (some v) := return (g, v)
   end

meta def add_vertex (e : expr) (s : side) :=
g.add_vertex_aux e ff s

meta def add_root_vertex (e : expr) (s : side) :=
g.add_vertex_aux e tt s

meta def register_solved (e : edge) : search_state α β γ δ :=
{ g with solving_edge := some e }

meta def add_adj (v : vertex) (e : edge) : search_state α β γ δ × vertex :=
g.set_vertex { v with adj := v.adj.alloc e }

meta def publish_parent (f t : vertex) (e : edge) : search_state α β γ δ × vertex :=
if t.root then
  (g, t)
else
  match t.parent with
  | some parent := (g, t)
  | none := g.set_vertex { t with parent := some e }
  end

meta def mark_vertex_visited (v : vertex) : tactic (search_state α β γ δ × vertex) := do
  return $ g.set_vertex { v with visited := tt }

meta def add_edge (f t : vertex) (proof : tactic expr) (how : how) : tactic (search_state α β γ δ × vertex × vertex × edge) :=
do let new_edge : edge := ⟨ f.id, t.id, proof, how ⟩,
   g.tracer_edge_added new_edge,
   let (g, f) := g.add_adj f new_edge,
   let (g, t) := g.add_adj t new_edge,
   let (g, t) := g.publish_parent f t new_edge,
   if ¬(vertex.same_side f t) then
     return (g.register_solved new_edge, f, t, new_edge)
   else
     return (g, f, t, new_edge)

meta def commit_rewrite (f : vertex) (r : rewrite) : tactic (search_state α β γ δ × vertex × (vertex × edge)) := do
  (g, v) ← g.add_vertex r.e f.s,
  (g, f, v, e) ← g.add_edge f v r.prf r.how,
  return (g, f, (v, e))

meta def reveal_more_rewrites (v : vertex) : tactic (search_state α β γ δ × vertex × option rewrite) := do
  (rw_prog, new_rws) ← discover_more_rewrites g.rs v.exp g.rwall_conf v.s v.rw_prog,
  (g, v) ← pure $ g.set_vertex {v with rw_prog := rw_prog, rws := v.rws.alloc_list new_rws},
  return (g, v, new_rws.nth 0)

-- TODO implement a table-backed queue?
meta def reveal_more_adjs (o : vertex) : tactic (search_state α β γ δ × vertex × option (vertex × edge)) := do
  (g, o, rw) ← match o.rws.at_ref o.rw_front with
  | none := g.reveal_more_rewrites o
  | some rw := pure (g, o, some rw)
  end,
  match rw with
  | none := return (g, o, none)
  | some rw := do
    (g, o, (v, e)) ← g.commit_rewrite o rw,
    (g, o) ← pure $ g.set_vertex {o with rw_front := o.rw_front.next},
    return (g, o, some (v, e))
  end

meta def visit_vertex (v : vertex) : tactic (search_state α β γ δ × rewriterator) :=
do
  (g, v) ← if ¬v.visited then do
        g.tracer_visited v,
        g.mark_vertex_visited v
      else
        pure (g, v),
  return ⟨g, ⟨v.id, table_ref.first⟩⟩

meta def improve_estimate_over (threshold : dnum) (de : dist_estimate γ) : tactic (search_state α β γ δ × dist_estimate γ) := do
  (vl, vr) ← g.get_estimate_verts de,
  let new_bnd := m.improve_estimate_over g threshold vl vr de.bnd,
  let new_de := {de with bnd := new_bnd},
  return ({g with estimates := g.estimates.update new_de}, new_de)

meta def alloc_estimate (p : pair) : tactic (search_state α β γ δ × table_ref) := do
  (vl, vr) ← g.lookup_pair p,
  let ref := g.estimates.next_id,
  let new_estimates := g.estimates.alloc ⟨p, ref, m.init_bound g vl vr⟩,
  return ({g with estimates := new_estimates}, ref)

/-- Check if `eq.refl _` suffices to prove the two sides are equal. -/
meta def try_unify (p : pair) : tactic (search_state α β γ δ × bool) := do
  (lhs, rhs) ← g.lookup_pair p,
  prf ← tactic.try_core $ tactic.attempt_refl lhs.exp rhs.exp,
  match prf with
  | none := return (g, ff)
  | some prf := do
    (g, _) ← g.add_edge lhs rhs (pure prf) how.defeq,
    return (g, tt)
  end

-- Currently, we guarentee that if the boolean we return is true, then there
-- is at least new rewrite possible in the environment which was not accessible
-- before. This follows here since it is (currently) guaranteed that each
-- element of `discovery.more_candidates` has an application *somewhere*.
meta def be_desperate (goals : list pair) : tactic (search_state α β γ δ × bool) :=
-- TODO merge the lemma discovery functionality
return (g, ff)

end search_state

namespace rewriterator

private meta def advance (it : rewriterator) : rewriterator :=
{it with front := it.front.next}

meta def next (it : rewriterator) (g : search_state α β γ δ) : tactic (search_state α β γ δ × rewriterator × option (vertex × edge)) := do
  o ← g.vertices.get it.orig,
  match o.adj.at_ref it.front with
  | some e := do
    v ← g.vertices.get e.t,
    return (g, advance it, some (v, e))
  | none := do
    (g, o, ret) ← g.reveal_more_adjs o,
    match ret with
    | some (v, e) := return (g, advance it, some (v, e))
    | none := return (g, it, none)
    end
  end

meta def exhaust : rewriterator → search_state α β γ δ → tactic (search_state α β γ δ × rewriterator × list (vertex × edge))
| it g := do
  (g, it, ret) ← it.next g,
  match ret with
  | none := return (g, it, [])
  | some (v, e) := do
    (g, it, rest) ← exhaust it g,
    return (g, it, ((v, e) :: rest))
  end

end rewriterator

namespace search_state

meta def exhaust_vertex (v : vertex) : tactic (search_state α β γ δ) := do
  (g, it) ← g.visit_vertex v,
  (g, it) ← it.exhaust g,
  return g

meta def exhaust_all_visited_aux : search_state α β γ δ → list vertex → tactic (search_state α β γ δ)
| g []          := return g
| g (v :: rest) := do
  g ← g.exhaust_vertex v,
  exhaust_all_visited_aux g rest

meta def exhaust_all_visited : tactic (search_state α β γ δ) :=
  g.exhaust_all_visited_aux g.vertices.to_list

-- Find a vertex we haven't visited, and visit it. The bool is true if there might
-- be other unvisited vertices.
meta def exhaust_one_unvisited : list vertex → tactic (search_state α β γ δ × bool)
| []          := return (g, ff)
| (v :: rest) :=
  if v.visited then
    exhaust_one_unvisited rest
  else do
    g ← g.exhaust_vertex v,
    return (g, tt)

meta def exhaust_all_unvisited : search_state α β γ δ → tactic (search_state α β γ δ)
| g := do
  (g, more_left) ← g.exhaust_one_unvisited g.vertices.to_list,
  if more_left then g.exhaust_all_unvisited else return g

meta def exhaust_all : tactic (search_state α β γ δ) := do
  g ← g.exhaust_all_visited,
  g ← g.exhaust_all_unvisited,
  return g

end search_state

namespace inst

meta def mutate : inst α β γ δ :=
{ i with g := g }

meta def step_once (itr : ℕ) : tactic (inst α β γ δ × status) :=
match i.g.solving_edge with
| some e := return (i, status.done e)
| none := do
  if itr > i.g.conf.max_iterations then
    return (i, status.abort "max iterations reached!")
  else do
    g ← i.metric.update i.g itr,
    (g, s) ← i.strategy.step g i.metric itr,
    return (i.mutate g, s)
end

meta def finish_search (e : edge) : tactic (inst α β γ δ × search_result) := do
  -- This must be called before i.g.exhaust_all
  (proof, units) ← backtrack.build_proof i e,

  i ← if i.g.conf.exhaustive then do
      g ← i.g.exhaust_all,
      pure $ i.mutate g
    else
      pure i,
  return (i, search_result.success proof units)

meta def search_until_solved_aux : inst α β γ δ → ℕ → tactic (inst α β γ δ × search_result)
| i itr := do
  (i, s) ← i.step_once itr,
  match s with
  | status.continue := search_until_solved_aux i (itr + 1)
  | status.repeat   := search_until_solved_aux i itr
  | status.abort r  := return (i, search_result.failure ("aborted: " ++ r))
  | status.done e   := i.finish_search e
  end

meta def search_until_solved : tactic (inst α β γ δ × search_result) := do
  if i.g.conf.trace_rules then (do
    rs ← i.g.rs.mmap pp_rule,
    tactic.trace $ "rewrite_search using:\n---\n" ++ (string.intercalate "\n" rs) ++ "\n---"
  ) else tactic.skip,
  i.search_until_solved_aux 0

meta def explain (proof : expr) (steps : list proof_unit) : tactic string :=
  explain_search_result i.g.conf i.g.rs proof steps

end inst

end tactic.rewrite_search
