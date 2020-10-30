/-
Copyright (c) 2020 Kevin Lacker, Keeley Hoek, Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Keeley Hoek, Scott Morrison
-/

import meta.rb_map
import tactic.rewrite_search.discovery
import tactic.rewrite_search.types

/-!
# The graph algorithm part of rewrite search

`search.lean` contains the logic to do a graph search. The search algorithm
starts with an equation to prove, treats the left hand side and right hand side as
two vertices in a graph, and uses rewrite rules to find a path that connects the two sides.
-/

open tactic

namespace tactic.rewrite_search

/-
An edge represents a proof that can get from one expression to another.
It represents the fact that, starting from the vertex `fr`, the expression in `proof`
can prove the vertex `to`.
`how` contains information that the explainer will use to generate Lean code for the
proof.
-/
meta structure edge :=
(fr to : ℕ)
(proof : tactic expr)
(how   : how)

meta def edge.to_string : edge → format
| e := format!"{e.fr} → {e.to}"

meta instance edge.has_to_format : has_to_format edge := ⟨edge.to_string⟩

/-
A vertex represents an expression that is equivalent to either the left or right side
of our initial equation.
`id` is a numerical id used to refer to this vertex in the context of a single graph.
`exp` is the expression this vertex represents.
`pp` is the string format of the expression; we store this in the vertex to avoid
recalculating it.
`side` is whether this vertex descends from the left or right side of the equation.
`parent` is the edge that originally added this vertex to the graph.
-/
meta structure vertex :=
(id     : ℕ)
(exp    : expr)
(pp     : string)
(side   : side)
(parent : option edge)

/-
The graph represents two trees, one descending from each of the left and right sides
of our initial equation.
`conf` and `rules` determine what rewrites are used to generate new graph vertices.
Here, the format of a rewrite rule is an expression for rewriting, plus a flag for the
direction to apply it in.
`vertices` maps vertex.id to vertex.
`vmap` maps vertex.pp to vertex.id, so we can quickly find collisions.
`solving_edge` represents a solution that will prove our target equation.
It is an edge that would connect the two trees, so `solving_edge.fr` and `solving_edge.to`
are vertices in different trees.
-/
meta structure graph :=
(conf         : config)
(rules        : list (expr × bool))
(vertices     : buffer vertex)
(vmap         : native.rb_map string ℕ)
(solving_edge : option edge)

/-
Construct a graph to search for a proof of a given equation.
-/
meta def mk_graph (conf : config) (rules : list (expr × bool)) (eq : expr) : tactic graph :=
do (lhs, rhs) ← split_equation eq,
  lhs_pp ← to_string <$> tactic.pp lhs,
  rhs_pp ← to_string <$> tactic.pp rhs,
  let lhs_vertex : vertex := ⟨0, lhs, lhs_pp, side.L, none⟩,
  let rhs_vertex : vertex := ⟨1, rhs, rhs_pp, side.R, none⟩,
  return ⟨conf, rules, [lhs_vertex, rhs_vertex].to_buffer,
          native.rb_map.of_list [(lhs_pp, 0), (rhs_pp, 1)], none⟩

variables (g : graph)

namespace graph

/-
A convenience wrapper around `g.vertices` that fails if the index is out of bounds.
-/
meta def get_vertex (i : ℕ) : tactic vertex :=
if h : i < g.vertices.size then return $ g.vertices.read (fin.mk i h)
else fail "invalid vertex access"

/-
Find a list of edges that connect the given edge to the root of its tree.
The edges are returned in leaf-to-root order, while they are in root-to-leaf direction,
so if you want them in the logical order you must reverse the returned list.
-/
private meta def walk_up_parents : option edge → tactic (list edge)
| none     := return []
| (some e) := do
  v ← g.get_vertex e.fr,
  edges ← walk_up_parents v.parent,
  return (e :: edges)

/-
Returns two lists that represent a solution. The first list is a path from LHS to some
interior vertex, the second is a path from the RHS to that interior vertex.
-/
private meta def solution_paths : tactic (list edge × list edge) :=
do e ← g.solving_edge,
  v ← g.get_vertex e.to,
  path1 ← walk_up_parents g e,
  path2 ← walk_up_parents g v.parent,
  match v.side with
    | side.L := return (path2.reverse, path1.reverse)
    | side.R := return (path1.reverse, path2.reverse)
  end

/-
Add the new vertex and edge to the graph, that can be proved in one step starting
at a given vertex, with a given rewrite expression.
For efficiency, it's important that this is the only way the graph is mutated,
and it only appends to the end of the `vertices` buffer.
-/
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

/-
Add all single-step rewrites starting at a particular vertex to the graph.
-/
private meta def expand_vertex (v : vertex) : tactic graph :=
do rws ← get_rewrites g.rules v.exp g.conf,
list.mfoldl (λ g rw, add_rewrite g v rw) g rws.to_list

/-
Repeatedly expand edges, starting at a given vertex id, until a solution is found.
-/
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

/-
Use `mk_eq_trans` to combine a list of proof expressions into a single proof expression.
-/
private meta def combine_proofs (proofs : list expr) : tactic expr :=
match proofs with
  | []              := fail "cannot combine empty proof list"
  | (proof :: rest) := list.mfoldl mk_eq_trans proof rest
end

/-
Construct a proof unit, given a path through the graph.
This reverses the direction of the proof on the right hand side, with `mk_eq_symm`.
-/
private meta def proof_for_edges : (side × list edge) → tactic (option proof_unit)
| (s, []) := return none
| (s, edges) := do
  proofs ← match s with
    | side.L := edges.mmap (λ e, e.proof)
    | side.R := edges.reverse.mmap (λ e, e.proof >>= mk_eq_symm)
  end,
  proof ← combine_proofs proofs,
  let hows := edges.map (λ e, e.how),
  return $ some ⟨proof, s, hows⟩

/-
Run the search to find a proof for the provided graph.
Normally, this is the only external method needed to run the graph search.
-/
meta def find_proof : tactic (graph × expr × list proof_unit) :=
do g ← find_solving_edge g 0,
  (left_edges, right_edges) ← solution_paths g,
  units ← [(side.L, left_edges), (side.R, right_edges)].mmap_filter proof_for_edges,
  proof ← combine_proofs $ units.map $ λ u, u.proof,
  return (g, proof, units)

end graph

end tactic.rewrite_search
