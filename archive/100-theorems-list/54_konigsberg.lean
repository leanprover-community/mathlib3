/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import combinatorics.simple_graph.trails
import tactic.derive_fintype

/-!
# The Königsberg bridges problem

We show that a graph that represents the islands and mainlands of Königsberg and seven bridges
between them has no Eulerian trail.
-/

namespace konigsberg

/-- The vertices for the Königsberg graph; four vertices for the bodies of land and seven
vertices for the bridges. -/
@[derive [decidable_eq, fintype], nolint has_inhabited_instance]
inductive verts : Type
| V1 | V2 | V3 | V4 -- The islands and mainlands
| B1 | B2 | B3 | B4 | B5 | B6 | B7 -- The bridges

open verts

/-- Each of the connections between the islands/mainlands and the bridges.
These are ordered pairs, but the data becomes symmetric in `konigsberg.adj`. -/
def edges : list (verts × verts) :=
[ (V1, B1), (V1, B2), (V1, B3), (V1, B4), (V1, B5),
  (B1, V2), (B2, V2), (B3, V4), (B4, V3), (B5, V3),
  (V2, B6), (B6, V4),
  (V3, B7), (B7, V4) ]

/-- The adjacency relation for the Königsberg graph. -/
def adj (v w : verts) : bool := ((v, w) ∈ edges) || ((w, v) ∈ edges)

/-- The Königsberg graph structure. While the Königsberg bridge problem
is usually described using a multigraph, the we use a "mediant" construction
to transform it into a simple graph -- every edge in the multigraph is subdivided
into a path of two edges. This construction preserves whether a graph is Eulerian.

(TODO: once mathlib has multigraphs, either prove the mediant construction preserves the
Eulerian property or switch this file to use multigraphs. -/
@[simps]
def graph : simple_graph verts :=
{ adj := λ v w, adj v w,
  symm := begin
    dsimp [symmetric, adj],
    dec_trivial,
  end,
  loopless := begin
    dsimp [irreflexive, adj],
    dec_trivial
  end }

instance : decidable_rel graph.adj := λ a b, decidable_of_bool (adj a b) iff.rfl

/-- To speed up the proof, this is a cache of all the degrees of each vertex,
proved in `konigsberg.degree_eq_degree`. -/
@[simp]
def degree : verts → ℕ
| V1 := 5 | V2 := 3 | V3 := 3 | V4 := 3
| B1 := 2 | B2 := 2 | B3 := 2 | B4 := 2 | B5 := 2 | B6 := 2 | B7 := 2

@[simp] lemma degree_eq_degree (v : verts) : graph.degree v = degree v := by cases v; refl

/-- The Königsberg graph is not Eulerian. -/
theorem not_is_eulerian {u v : verts} (p : graph.walk u v) (h : p.is_eulerian) : false :=
begin
  have : {v | odd (graph.degree v)} = {verts.V1, verts.V2, verts.V3, verts.V4},
  { ext w,
    simp only [degree_eq_degree, nat.odd_iff_not_even, set.mem_set_of_eq, set.mem_insert_iff,
      set.mem_singleton_iff],
    cases w; simp, },
  have h := h.card_odd_degree,
  simp_rw [this] at h,
  norm_num at h,
end

end konigsberg
