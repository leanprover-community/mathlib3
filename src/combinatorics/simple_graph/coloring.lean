/-
Copyright (c) 2020 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Kyle Miller
-/

import combinatorics.simple_graph.subgraph
import data.nat.lattice

/-!
# Graph Coloring

This approach to graph colorings uses homomorphisms to complete graphs.

#TODO: gather material from:
* https://github.com/leanprover-community/mathlib/blob/simple_graph_matching/src/combinatorics/simple_graph/coloring.lean
* https://github.com/kmill/lean-graphcoloring/blob/master/src/graph.lean

#TODO: vertex / edge coloring duality
-/

universes u v

namespace simple_graph
variables {V : Type u} (G : simple_graph V)

abbreviation proper_coloring (α : Type v) := G →g complete_graph α

variables {G} {α : Type v} (C : G.proper_coloring α)

def proper_coloring.color (v : V) : α := C v

def proper_coloring.used_colors : set α := set.range C.color

-- maybe there's a smoother definition of the chromatic number using the minimal size among
-- proper colorings
def proper_coloring.size [fintype C.used_colors] : ℕ := fintype.card C.used_colors

lemma proper_coloring.valid (v w : V) (h : G.adj v w) : C.color v ≠ C.color w :=
  C.map_rel h

@[pattern]
def proper_coloring.mk (color : V → α) (h : ∀ {v w : V}, G.adj v w → color v ≠ color w) :
  G.proper_coloring α := ⟨color, @h⟩

/-- Whether a graph can be colored by at most `n` colors. -/
def colorable (G : simple_graph V) (n : ℕ) : Prop :=
∃ (α : Type v) [fintype α] (C : G.proper_coloring α), by exactI fintype.card α ≤ n

/-- If `G` isn't colorable with finitely many colors, this will be 0. -/
noncomputable def chromatic_number (G : simple_graph V) : ℕ :=
  Inf { n : ℕ | G.colorable n }

def complete_graph.of_embedding {α β : Type*} (f : α ↪ β) : complete_graph α ↪g complete_graph β :=
{ to_fun := f,
  inj' := f.inj',
  map_rel_iff' := by simp }

lemma colorable_iff_nonempty_fin_coloring (G : simple_graph V) (n : ℕ) :
  G.colorable n ↔ nonempty (G.proper_coloring (fin n)) :=
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
  G.colorable n ↔ ∃ (C : G.proper_coloring ℕ), ∀ v, C.color v < n :=
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
    refine ⟨⟨λ v, ⟨C.color v, Cf v⟩, _⟩⟩,
    rintro v w hvw,
    simp only [complete_graph_eq_top, top_adj, subtype.mk_eq_mk, ne.def],
    exact C.valid v w hvw, },
end

example [fintype α] (r : set α) : fintype (set α) := by library_search

-- may eliminate `proper_coloring.size`'s requirement if we have a finite number of colors
lemma fin_colors_then_fin_size [fintype α] (C : G.proper_coloring α) : fintype C.used_colors :=
begin
  rw proper_coloring.used_colors,
  sorry
end

lemma exists_fin_coloring_then_colorable [fintype α] (C : G.proper_coloring α) :
  G.colorable (fintype.card α) :=
begin
  rw colorable,
  by_contra h,
  simp at h,
  sorry
end

lemma chromatic_number_le [fintype α] (C : G.proper_coloring α) :
  G.chromatic_number ≤ fintype.card α :=
begin
  rw chromatic_number,
  apply cInf_le,
  { use 0,
    rintros _ _,
    simp only [zero_le], },
  { simp [exists_fin_coloring_then_colorable C], },
end

lemma colorable_lower_bound (G' : simple_graph V) (h : G ≤ G') (n : ℕ) (hc : G'.colorable n) :
  G.colorable n :=
begin
  sorry
end

lemma chromatic_number_lower_bound (G' : simple_graph V) (h : G ≤ G') :
  G.chromatic_number ≤ G'.chromatic_number :=
begin
  simp only [chromatic_number],
  sorry
end

lemma zero_le_chromatic_number [nonempty V] [fintype α] (C : G.proper_coloring α) :
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
    let v := classical.arbitrary V, -- coloring this vertex requires at least 1 color
    sorry, },
end

lemma chromatic_number_minimal [fintype α] (C : G.proper_coloring α)
  (h : ∀ (C' : G.proper_coloring α), C'.used_colors = set.univ) :
  G.chromatic_number = fintype.card α :=
begin
  simp [proper_coloring.used_colors] at h,
  rw chromatic_number,
  sorry
end

end simple_graph
