/-
Copyright (c) 2020 Kevin Lacker, Keeley Hoek, Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Keeley Hoek, Scott Morrison
-/

import tactic.rewrite_search.types
import tactic.rewrite_search.debug
import tactic.rewrite_search.backtrack
import tactic.rewrite_search.explain

/-!
# The core algorithm underlying rewrite search.
-/

universe u

namespace tactic.rewrite_search

variables (g : search_state)

private meta def chop : list char → list string → list string
| [] L := L
| (c :: rest) L := chop rest $ list.join $ L.map (λ l, l.split_on c)

meta def tokenize_expr (e : expr) : tactic (string × list string) := do
  pp ← to_string <$> tactic.pp e,
  pure (pp, chop [' '/-, '(', ')'-/] [pp])

namespace search_state

private meta def register_tokens_aux (s : side) :
table token → list string → table token × list table_ref
| tokens [] := (tokens, [])
| tokens (tstr :: rest) := do
  let (tokens, t) := find_or_create_token tokens s tstr,
  let (tokens, l) := register_tokens_aux tokens rest,
  (tokens, t.id :: l)

meta def register_tokens (s : side) (strs : list string) : search_state × list table_ref :=
  let (new_tokens, refs) := register_tokens_aux s g.tokens strs in
  ({g with tokens := new_tokens}, refs)

-- Find the vertex with the given (e : expr), or return the null vertex if not found.
meta def find_vertex (e : expr) : tactic (option vertex) := do
  pp ← to_string <$> tactic.pp e,
  return (g.vertices.find_key pp)

-- Forcibly add a new vertex to the vertex table. You probably actually want to call
-- add_vertex, which will check that we haven't seen the vertex before first.
meta def alloc_vertex (e : expr) (root : bool) (s : side) : tactic (search_state × vertex) :=
do (pp, tokens) ← tokenize_expr e,
   let (g, token_refs) := g.register_tokens s tokens,
   let v : vertex := vertex.create g.vertices.next_id e pp token_refs root s,
   return ({ g with vertices := g.vertices.alloc v }, v)

-- Look up the given vertex associated to (e : expr), or create it if it is
-- not already present.
meta def add_vertex_aux (e : expr) (root : bool) (s : side) : tactic (search_state × vertex) :=
do maybe_v ← g.find_vertex e,
   match maybe_v with
   | none := do
     (g, v) ← g.alloc_vertex e root s,
     g.trace_vertex_added v,
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
g.set_vertex { v with adj := v.adj.alloc e }

meta def publish_parent (f t : vertex) (e : edge) : search_state × vertex :=
if t.root then
  (g, t)
else
  match t.parent with
  | some parent := (g, t)
  | none := g.set_vertex { t with parent := some e }
  end

meta def mark_vertex_visited (v : vertex) : tactic (search_state × vertex) := do
  return $ g.set_vertex { v with visited := tt }

meta def add_edge (f t : vertex) (proof : tactic expr) (how : how) :
tactic (search_state × vertex × vertex × edge) :=
do let new_edge : edge := ⟨ f.id, t.id, proof, how ⟩,
   g.trace_edge_added new_edge,
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

meta def reveal_more_rewrites (v : vertex) :
tactic (search_state × vertex × option rewrite) :=
do (rw_prog, new_rws) ← discover_more_rewrites g.rs v.exp g.conf v.s v.rw_prog,
  (g, v) ← pure $ g.set_vertex {v with rw_prog := rw_prog, rws := v.rws.alloc_list new_rws},
  return (g, v, new_rws.nth 0)

meta def reveal_more_adjs (o : vertex) :
tactic (search_state × vertex × option (vertex × edge)) :=
do (g, o, rw) ← match o.rws.at_ref o.rw_front with
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

meta def visit_vertex (v : vertex) : tactic (search_state × rewrite_iter) :=
do
  (g, v) ← if ¬v.visited then do
        g.mark_vertex_visited v
      else
        pure (g, v),
  return ⟨g, ⟨v.id, table_ref.first⟩⟩

end search_state

namespace rewrite_iter

private meta def advance (it : rewrite_iter) : rewrite_iter :=
{it with front := it.front.next}

meta def next (it : rewrite_iter) (g : search_state) :
tactic (search_state × rewrite_iter × option (vertex × edge)) := do
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

meta def exhaust :
rewrite_iter → search_state → tactic (search_state × rewrite_iter × list (vertex × edge))
| it g := do
  (g, it, ret) ← it.next g,
  match ret with
  | none := return (g, it, [])
  | some (v, e) := do
    (g, it, rest) ← exhaust it g,
    return (g, it, ((v, e) :: rest))
  end

end rewrite_iter

namespace search_state

meta def exhaust_vertex (v : vertex) : tactic search_state := do
  (g, it) ← g.visit_vertex v,
  (g, it) ← it.exhaust g,
  return g

meta def exhaust_all_visited_aux : search_state → list vertex → tactic search_state
| g []          := return g
| g (v :: rest) := do
  g ← g.exhaust_vertex v,
  exhaust_all_visited_aux g rest

meta def exhaust_all_visited : tactic search_state :=
  g.exhaust_all_visited_aux g.vertices.to_list

-- Find a vertex we haven't visited, and visit it. The bool is true if there might
-- be other unvisited vertices.
meta def exhaust_one_unvisited : list vertex → tactic (search_state × bool)
| []          := return (g, ff)
| (v :: rest) :=
  if v.visited then
    exhaust_one_unvisited rest
  else do
    g ← g.exhaust_vertex v,
    return (g, tt)

meta def exhaust_all_unvisited : search_state → tactic search_state
| g := do
  (g, more_left) ← g.exhaust_one_unvisited g.vertices.to_list,
  if more_left then g.exhaust_all_unvisited else return g

meta def exhaust_all : tactic search_state := do
  g ← g.exhaust_all_visited,
  g ← g.exhaust_all_unvisited,
  return g

end search_state

meta def bfs_init (refs : list (option table_ref)) : bfs_state := ⟨1, refs⟩

meta def bfs_step (g : search_state) : tactic (search_state × status) := do
  let state := g.strat_state,
  if state.curr_depth > 50 then
    return (g, status.abort "max bfs depth reached!")
  else match state.queue with
  | [] := return (g, status.abort "all vertices exhausted!")
  | (none :: rest) := do
    return (g.mutate_strat {state with queue := rest.concat none, curr_depth :=
                            state.curr_depth + 1}, status.repeat)
  | (some v :: rest) := do
    v ← g.vertices.get v,
    (g, it) ← g.visit_vertex v,
    (g, it, adjs) ← it.exhaust g,
    let adjs := adjs.filter $ λ u, ¬u.1.visited,
    return (g.mutate_strat {state with queue := rest.append $ adjs.map $ λ u, some u.1.id},
            status.continue)
  end

namespace search_state

meta def step_once (itr : ℕ) : tactic (search_state × status) :=
match g.solving_edge with
| some e := return (g, status.done e)
| none := do
  if itr > g.conf.max_iterations then
    return (g, status.abort "max iterations reached!")
  else do
    (g, s) ← bfs_step g,
    return (g, s)
end

meta def finish_search (e : edge) : tactic (search_state × search_result) := do
  -- This must be called before exhaust_all
  (proof, units) ← backtrack.build_proof g e,

  i ← if g.conf.exhaustive then do
      g ← g.exhaust_all,
      pure $ g
    else
      pure g,
  return (g, search_result.success proof units)

meta def search_until_solved_aux : search_state → ℕ → tactic (search_state × search_result)
| g itr := do
  (g, s) ← g.step_once itr,
  match s with
  | status.continue := search_until_solved_aux g (itr + 1)
  | status.repeat   := search_until_solved_aux g itr
  | status.abort r  := return (g, search_result.failure ("aborted: " ++ r))
  | status.done e   := g.finish_search e
  end

meta def search_until_solved : tactic (search_state × search_result) := do
  if g.conf.trace_rules then (do
    rs ← g.rs.mmap pp_rule,
    tactic.trace $ "rewrite_search using:\n---\n" ++ (string.intercalate "\n" rs) ++ "\n---"
  ) else tactic.skip,
  g.search_until_solved_aux 0

meta def explain (proof : expr) (steps : list proof_unit) : tactic string :=
  explain_search_result g.conf g.rs proof steps

end search_state

end tactic.rewrite_search
