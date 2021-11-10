/-
Copyright (c) 2021 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Kyle Miller
-/

import combinatorics.simple_graph.subgraph
import data.nat.lattice

/-!
# Graph Coloring

The following approach to graph coloring refers to the attribution of "colors" to all of its
vertices such that no edge connects vertices with the same color. A coloring can be represented by a
homomorphism into a complete graph whose vertices are the colors themselves.

## Main definitions

* An *α-coloring* of a simple graph *G* is an homomorphism into the complete graph of *α*, *α* being
the set of available colors.

* We say that *G* is *n-colorable* if it's possible to produce a coloring with at most *n* colors.

* The *chromatic number* of *G* is the minimum number of colors required to color *G*.

## Todo:

  * Gather material from:
    * https://github.com/leanprover-community/mathlib/blob/simple_graph_matching/src/combinatorics/simple_graph/coloring.lean
    * https://github.com/kmill/lean-graphcoloring/blob/master/src/graph.lean

  * Lowerbound for cliques

  * Trees

  * Bipartite graphs

  * Planar graphs
-/

universes u v

namespace simple_graph
variables {V : Type u} (G : simple_graph V)

/--
An `α-coloring` of the `simple_graph G` is a homomorphism of `G` into the complete graph of `α`.
-/
abbreviation coloring (α : Type v) := G →g complete_graph α

variables {G} {α : Type v} (C : G.coloring α)

lemma coloring.valid (v w : V) (h : G.adj v w) : C v ≠ C w :=
  C.map_rel h

/--
Produces a coloring given a color function (which takes a vertex to a color) and a term of the type
which guarantees that adjacent vertices have different colors.
-/
@[pattern] def coloring.mk (color : V → α) (h : ∀ {v w : V}, G.adj v w → color v ≠ color w) :
  G.coloring α := ⟨color, @h⟩

/-- Whether a graph can be colored by at most `n` colors. -/
def colorable (G : simple_graph V) (n : ℕ) : Prop :=
∃ (α : Type v) [fintype α] (C : G.coloring α), by exactI fintype.card α ≤ n

/-- If `G` isn't colorable with finitely many colors, this will be 0. -/
noncomputable def chromatic_number (G : simple_graph V) : ℕ :=
  Inf { n : ℕ | G.colorable n }

def complete_graph.of_embedding {α β : Type*} (f : α ↪ β) : complete_graph α ↪g complete_graph β :=
{ to_fun := f,
  inj' := f.inj',
  map_rel_iff' := by simp }

lemma colorable_iff_nonempty_fin_coloring (G : simple_graph V) (n : ℕ) :
  G.colorable n ↔ nonempty (G.coloring (fin n)) :=
begin
  split,
  { rintro ⟨α, αf, C, h⟩,
    tactic.unfreeze_local_instances,
    let f := (fintype.equiv_fin α).to_embedding.trans (fin.cast_le h).to_embedding,
    exact ⟨(complete_graph.of_embedding f).to_hom.comp C⟩, },
  { rintro ⟨C⟩,
    exact ⟨ulift (fin n), by apply_instance,
      (complete_graph.of_embedding equiv.ulift.symm.to_embedding).to_hom.comp C, by simp⟩, },
end

lemma colorable_iff_nonempty_fin_coloring' (G : simple_graph V) (n : ℕ) :
  G.colorable n ↔ ∃ (C : G.coloring ℕ), ∀ v, C v < n :=
begin
  rw colorable_iff_nonempty_fin_coloring,
  split,
  { rintro ⟨C⟩,
    let f := complete_graph.of_embedding (fin.coe_embedding n).to_embedding,
    use f.to_hom.comp C,
    cases C with color valid,
    intro v,
    exact fin.is_lt (color v), },
  { rintro ⟨C, Cf⟩,
    refine ⟨⟨λ v, ⟨C v, Cf v⟩, _⟩⟩,
    rintro v w hvw,
    simp only [complete_graph_eq_top, top_adj, subtype.mk_eq_mk, ne.def],
    exact C.valid v w hvw, },
end

lemma empty_graph_trivially_colorable (he: is_empty V) : ∀ (n : ℕ), G.colorable n :=
begin
  intro n,
  rw colorable_iff_nonempty_fin_coloring,
  let color : V → fin n := he.elim,
  have h : ∀ (v w : V), G.adj v w → color v ≠ color w,
  { intro v,
    exfalso,
    exact is_empty_iff.mp he v, },
  { use coloring.mk color h, },
end

lemma exists_fin_coloring_then_colorable [fintype α] (C : G.coloring α) :
  G.colorable (fintype.card α) :=
begin
  rw colorable_iff_nonempty_fin_coloring,
  let f : α → (fin (fintype.card α)) := λ a, sorry, -- create a function that takes different
                                                    -- colors to different natural numbers
  let color : V → fin (fintype.card α) := λ v, f (C v),
  have h : ∀ (v w : V), G.adj v w → color v ≠ color w,
  { -- prove that `color` takes adjacent vertices to different colors
    sorry, },
  { use coloring.mk color h, },
end

lemma chromatic_number_bdd_below (C: G.coloring α) : bdd_below {n : ℕ | G.colorable n} :=
begin
  use 0,
  intros _ _,
  simp only [zero_le],
end

lemma chromatic_number_le [fintype α] (C : G.coloring α) :
  G.chromatic_number ≤ fintype.card α :=
begin
  rw chromatic_number,
  apply cInf_le,
  { apply chromatic_number_bdd_below C },
  { simp [exists_fin_coloring_then_colorable C], },
end

lemma chromatic_number_leq_one [subsingleton V] [fintype α] (C : G.coloring α) :
  G.chromatic_number ≤ 1 :=
begin
  rw chromatic_number,
  apply cInf_le,
  { apply chromatic_number_bdd_below C },
  { simp,
    rw colorable_iff_nonempty_fin_coloring,
    let color : V → fin 1 := λ _, 0,
    have h : ∀ (v w : V), G.adj v w → color v ≠ color w,
    { intros v w hh,
      by_cases v = w,
      { exfalso,
        rw h at hh,
        exact G.irrefl hh, },
      { exfalso,
        simp at h,
        exact h, }, },
    use coloring.mk color h, },
end

lemma zero_le_chromatic_number [nonempty V] [fintype α] (C : G.coloring α) :
  0 < G.chromatic_number :=
begin
  rw [nat.lt_iff_add_one_le, chromatic_number, zero_add],
  apply le_cInf,
  { use fintype.card α,
    exact exists_fin_coloring_then_colorable C, },
  { intros n hn,
    by_contra h,
    simp at h,
    simp [h] at hn,
    rw colorable at hn,
    rcases hn with ⟨α', hα', C', hf⟩,
    let v := classical.arbitrary V,
    have c := C' v,
    have hn : nonempty α', use c,
    tactic.unfreeze_local_instances,
    rw ← fintype.card_pos_iff at hn,
    exact nat.lt_le_antisymm hn hf, },
end

lemma chromatic_number_minimal [fintype α] (C : G.coloring α)
  (h : ∀ (C' : G.coloring α), set.range C' = set.univ) :
  G.chromatic_number = fintype.card α :=
begin
  sorry
end

lemma colorable_lower_bound (G' : simple_graph V) (h : G ≤ G') (n : ℕ) (hc : G'.colorable n) :
  G.colorable n :=
begin
  sorry
end

lemma chromatic_number_lower_bound (G' : simple_graph V) (h : G ≤ G') :
  G.chromatic_number ≤ G'.chromatic_number :=
begin
  sorry
end

end simple_graph
