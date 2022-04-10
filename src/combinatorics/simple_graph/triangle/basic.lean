/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simple_graph.clique

/-!
# Triangles in graphs

This file defines triangles in simple graphs.

A triangle is a `3`-clique, that is a set of three vertices which are all connected.

## Main declarations

* `simple_graph.triangle_finset`: Finset of triangles of a graph.
* `simple_graph.triangle_free`: Predicate for a graph to have no triangle.
* `simple_graph.triangle_free_far`: Predicate for a graph to have enough triangles that one must
  remove a lot of edges to remove all of them. This is the crux of the Triangle Removal lemma.
-/

open finset fintype

namespace simple_graph
variables {α 𝕜 : Type*} [linear_ordered_field 𝕜] (G H : simple_graph α) {n : ℕ} {s : finset α}

section triangle_free

/-- `G.triangle_free` means that `G` has no triangles. -/
def triangle_free : Prop := ∀ t, ¬ G.is_n_clique 3 t

variables {G H}

lemma triangle_free_bot : (⊥ : simple_graph α).triangle_free :=
begin
  rintro t ht,
  rw is_n_clique_bot_iff at ht,
  norm_num at ht,
end

lemma triangle_free.mono (h : G ≤ H) : H.triangle_free → G.triangle_free :=
forall_imp $ λ s, mt $ is_n_clique.mono h

end triangle_free

section triangle_finset
variables (G) [fintype α] [decidable_eq α] [decidable_rel G.adj] {a b c : α}

/-- The triangles in a graph as a finset. -/
def triangle_finset : finset (finset α) := (powerset_len 3 univ).filter $ G.is_n_clique 3

lemma mem_triangle_finset_iff (s : finset α) : s ∈ G.triangle_finset ↔ G.is_n_clique 3 s :=
by rw [triangle_finset, mem_filter, mem_powerset_len, and_iff_right (subset_univ _),
  and_iff_right_of_imp is_n_clique.card_eq]

lemma triple_mem_triangle_finset_iff :
  {a, b, c} ∈ G.triangle_finset ↔ G.adj a b ∧ G.adj a c ∧ G.adj b c :=
begin
  rw [mem_triangle_finset_iff, is_n_clique_iff, is_clique_iff],
  simp only [coe_insert, coe_singleton, set.pairwise_insert_of_symmetric G.symm,
    set.pairwise_singleton, true_and, set.mem_insert_iff, set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq, ne.def],
  split,
  { rintro ⟨⟨hbc, hab, hac⟩, h⟩,
    refine ⟨hab _, hac _, hbc _⟩;
    { rintro rfl,
      simp only [insert_idem, insert_singleton_comm, insert_singleton_self_eq] at h,
      exact h.not_lt (nat.lt_succ_iff.2 $ card_insert_le _ _) } },
  { rintro ⟨hab, hac, hbc⟩,
    refine ⟨⟨λ _, hbc, λ _, hab, λ _, hac⟩, _⟩,
    rw card_eq_three,
    exact ⟨_, _, _, G.ne_of_adj hab, G.ne_of_adj hac, G.ne_of_adj hbc, rfl⟩ }
end

lemma mem_triangle_finset_iff' :
  s ∈ G.triangle_finset ↔ ∃ a b c, G.adj a b ∧ G.adj a c ∧ G.adj b c ∧ s = {a, b, c} :=
begin
  refine ⟨λ h, _, _⟩,
  { obtain ⟨a, b, c, -, -, -, rfl⟩ := card_eq_three.1 ((G.mem_triangle_finset_iff s).1 h).2,
    refine ⟨a, b, c, _⟩,
    rw triple_mem_triangle_finset_iff at h,
    tauto },
  { rintro ⟨a, b, c, hab, hbc, hca, rfl⟩,
    exact G.triple_mem_triangle_finset_iff.2 ⟨hab, hbc, hca⟩ }
end

@[simp] lemma triangle_finset_eq_empty_iff : G.triangle_finset = ∅ ↔ G.triangle_free :=
by simp_rw [triangle_free, eq_empty_iff_forall_not_mem, mem_triangle_finset_iff]

alias triangle_finset_eq_empty_iff ↔ _ simple_graph.triangle_free.triangle_finset

attribute [protected] triangle_free.triangle_finset

variables {G} [decidable_rel H.adj]

lemma triangle_finset_mono (h : G ≤ H) : G.triangle_finset ⊆ H.triangle_finset :=
monotone_filter_right _ $ λ _, is_n_clique.mono h

end triangle_finset

section triangle_free_far
variables [fintype α] {G H} {ε δ : 𝕜}

open_locale classical

/-- A simple graph is `ε`-triangle-free far if one must remove a density of `ε` edges to make it
triangle-free. -/
def triangle_free_far (G : simple_graph α) (ε : 𝕜) : Prop :=
∀ ⦃H⦄, H ≤ G → H.triangle_free → ε * (card α^2 : ℕ) ≤ G.edge_finset.card - H.edge_finset.card

lemma triangle_free_far.mono (hε : G.triangle_free_far ε) (h : δ ≤ ε) : G.triangle_free_far δ :=
λ I hIG hI, (mul_le_mul_of_nonneg_right h $ nat.cast_nonneg _).trans $ hε hIG hI

lemma triangle_free_far.triangle_finset_nonempty' (hH : H ≤ G) (hG : G.triangle_free_far ε)
  (hcard : (G.edge_finset.card - H.edge_finset.card : 𝕜) < ε * (card α ^ 2 : ℕ)) :
  H.triangle_finset.nonempty :=
begin
  apply nonempty_of_ne_empty,
  rw [ne.def, triangle_finset_eq_empty_iff],
  exact λ hH', (hG hH hH').not_lt hcard,
end

variables [nonempty α]

lemma triangle_free_far.nonpos (h₀ : G.triangle_free_far ε) (h₁ : G.triangle_free) : ε ≤ 0 :=
begin
  have := h₀ le_rfl h₁,
  rw sub_self at this,
  exact nonpos_of_mul_nonpos_right this (nat.cast_pos.2 $ sq_pos_of_pos fintype.card_pos),
end

lemma triangle_free.not_triangle_free_far (hG : G.triangle_free) (hε : 0 < ε) :
  ¬ G.triangle_free_far ε :=
λ h, (h.nonpos hG).not_lt hε

lemma triangle_free_far.not_triangle_free (hG : G.triangle_free_far ε) (hε : 0 < ε) :
  ¬ G.triangle_free :=
λ h, (hG.nonpos h).not_lt hε

lemma triangle_free_far.triangle_finset_nonempty (hG : G.triangle_free_far ε) (hε : 0 < ε) :
  G.triangle_finset.nonempty :=
nonempty_of_ne_empty $ G.triangle_finset_eq_empty_iff.not.2 $ hG.not_triangle_free hε

end triangle_free_far
end simple_graph
