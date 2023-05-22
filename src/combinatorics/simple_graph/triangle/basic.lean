/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simple_graph.clique
import data.nat.parity
import data.sym.card

/-!
# Triangles in graphs

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A *triangle* in a simple graph is a `3`-clique, namely a set of three vertices that are
pairwise adjacent.

This module defines and proves properties about triangles in simple graphs.

## Main declarations

* `simple_graph.far_from_triangle_free`: Predicate for a graph to have enough triangles that, to
  remove all of them, one must one must remove a lot of edges. This is the crux of the Triangle
  Removal lemma.

## TODO

* Generalise `far_from_triangle_free` to other graphs, to state and prove the Graph Removal Lemma.
* Find a better name for `far_from_triangle_free`. Added 4/26/2022. Remove this TODO if it gets old.
-/

namespace simple_graph
variables {V : Type*}

@[simp] lemma edge_set_top : (⊤ : simple_graph V).edge_set = {e : sym2 V | ¬ e.is_diag} :=
by ext x; induction x using sym2.ind; simp

@[simp] lemma edge_finset_top [fintype V] [decidable_eq V] [fintype (⊤ : simple_graph V).edge_set] :
  (⊤ : simple_graph V).edge_finset = finset.univ.filter (λ e, ¬ e.is_diag) :=
by ext x; induction x using sym2.ind; simp

end simple_graph

open finset fintype nat
open_locale classical

namespace simple_graph
variables {α 𝕜 : Type*} [fintype α] [linear_ordered_field 𝕜] {G H : simple_graph α} {ε δ : 𝕜}
  {n : ℕ} {s : finset α}

/-- A simple graph is *`ε`-triangle-free far* if one must remove at least `ε * (card α)^2` edges to
make it triangle-free. -/
def far_from_triangle_free (G : simple_graph α) (ε : 𝕜) : Prop :=
G.delete_far (λ H, H.clique_free 3) $ ε * (card α^2 : ℕ)

lemma far_from_triangle_free_iff :
  G.far_from_triangle_free ε ↔
    ∀ ⦃H⦄, H ≤ G → H.clique_free 3 → ε * (card α^2 : ℕ) ≤ G.edge_finset.card - H.edge_finset.card :=
delete_far_iff

alias far_from_triangle_free_iff ↔ far_from_triangle_free.le_card_sub_card _

lemma far_from_triangle_free.mono (hε : G.far_from_triangle_free ε) (h : δ ≤ ε) :
  G.far_from_triangle_free δ :=
hε.mono $ mul_le_mul_of_nonneg_right h $ cast_nonneg _

lemma far_from_triangle_free.clique_finset_nonempty' (hH : H ≤ G) (hG : G.far_from_triangle_free ε)
  (hcard : (G.edge_finset.card - H.edge_finset.card : 𝕜) < ε * (card α ^ 2 : ℕ)) :
  (H.clique_finset 3).nonempty :=
nonempty_of_ne_empty $ H.clique_finset_eq_empty_iff.not.2 $ λ hH',
  (hG.le_card_sub_card hH hH').not_lt hcard

variables [nonempty α]

lemma far_from_triangle_free.lt_half (hG : G.far_from_triangle_free ε) : ε < 2⁻¹ :=
begin
  by_contra' hε,
  have := hG.le_card_sub_card bot_le (clique_free_bot $ by norm_num),
  simp only [set.to_finset_card (edge_set ⊥), card_of_finset, edge_set_bot, cast_zero,
    finset.card_empty, tsub_zero] at this,
  have hε₀ : 0 < ε := hε.trans_lt' (by norm_num),
  rw inv_pos_le_iff_one_le_mul (zero_lt_two' 𝕜) at hε,
  refine (this.trans $ le_mul_of_one_le_left (by positivity) hε).not_lt _,
  rw [mul_assoc, mul_lt_mul_left hε₀],
  norm_cast,
  refine (mul_le_mul_left' (card_mono $ edge_finset_mono le_top) _).trans_lt _,
  rw [edge_finset_top, filter_not, card_sdiff (subset_univ _), card_univ, sym2.card],
  simp_rw [sym2.is_diag_iff_mem_range_diag, univ_filter_mem_range, mul_tsub,
    nat.mul_div_cancel' (card α).even_mul_succ_self.two_dvd],
  rw [card_image_of_injective _ sym2.diag_injective, card_univ, mul_add_one, two_mul, sq,
    add_tsub_add_eq_tsub_right],
  exact tsub_lt_self (mul_pos fintype.card_pos fintype.card_pos) fintype.card_pos,
end

lemma far_from_triangle_free.lt_one (hG : G.far_from_triangle_free ε) : ε < 1 :=
hG.lt_half.trans $ by norm_num

lemma far_from_triangle_free.nonpos (h₀ : G.far_from_triangle_free ε) (h₁ : G.clique_free 3) :
  ε ≤ 0 :=
begin
  have := h₀ (empty_subset _),
  rw [coe_empty, finset.card_empty, cast_zero, delete_edges_empty_eq] at this,
  exact nonpos_of_mul_nonpos_left (this h₁) (cast_pos.2 $ sq_pos_of_pos fintype.card_pos),
end

lemma clique_free.not_far_from_triangle_free (hG : G.clique_free 3) (hε : 0 < ε) :
  ¬ G.far_from_triangle_free ε :=
λ h, (h.nonpos hG).not_lt hε

lemma far_from_triangle_free.not_clique_free (hG : G.far_from_triangle_free ε) (hε : 0 < ε) :
  ¬ G.clique_free 3 :=
λ h, (hG.nonpos h).not_lt hε

lemma far_from_triangle_free.clique_finset_nonempty (hG : G.far_from_triangle_free ε) (hε : 0 < ε) :
  (G.clique_finset 3).nonempty :=
nonempty_of_ne_empty $ G.clique_finset_eq_empty_iff.not.2 $ hG.not_clique_free hε

variables {G H} {tris : finset (finset α)}

private lemma far_from_triangle_free_of_disjoint_triangles_aux (htris : tris ⊆ G.clique_finset 3)
  (pd : (tris : set (finset α)).pairwise (λ x y, (x ∩ y).card ≤ 1)) (hHG : H ≤ G)
  (hH : H.clique_free 3) : tris.card ≤ G.edge_finset.card - H.edge_finset.card :=
begin
  rw [←card_sdiff (edge_finset_mono hHG), ←card_attach],
  by_contra' hG,
  have : ∀ t, t ∈ tris → ∃ x y, x ∈ t ∧ y ∈ t ∧ x ≠ y ∧ ⟦(x, y)⟧ ∈ G.edge_finset \ H.edge_finset,
  { intros t ht,
    by_contra' h,
    refine hH t _,
    simp only [not_and, mem_sdiff, not_not, mem_edge_finset, mem_edge_set] at h,
    obtain ⟨x, y, z, xy, xz, yz, rfl⟩ := is_3_clique_iff.1 (G.mem_clique_finset_iff.1 $ htris ht),
    rw is_3_clique_triple_iff,
    refine ⟨h _ _ _ _ xy.ne xy, h _ _ _ _ xz.ne xz, h _ _ _ _ yz.ne yz⟩; simp },
  choose fx fy hfx hfy hfne fmem using this,
  let f : {x // x ∈ tris} → sym2 α := λ t, ⟦(fx _ t.2, fy _ t.2)⟧,
  have hf : ∀ x, x ∈ tris.attach → f x ∈ G.edge_finset \ H.edge_finset := λ x hx, fmem _ _,
  obtain ⟨⟨t₁, ht₁⟩, -, ⟨t₂, ht₂⟩, -, tne, t : ⟦_⟧ = ⟦_⟧⟩ :=
    exists_ne_map_eq_of_card_lt_of_maps_to hG hf,
  dsimp at t,
  have i := pd ht₁ ht₂ (subtype.val_injective.ne tne),
  simp only [finset.card_le_one_iff, mem_inter, and_imp] at i,
  rw sym2.eq_iff at t,
  cases t,
  { exact hfne _ _ (i (hfx t₁ ht₁) (t.1.symm ▸ hfx t₂ ht₂) (hfy t₁ ht₁) $ t.2.symm ▸ hfy t₂ ht₂) },
  { exact hfne _ _ (i (hfx t₁ ht₁) (t.1.symm ▸ hfy t₂ ht₂) (hfy t₁ ht₁) $ t.2.symm ▸ hfx t₂ ht₂) }
end

/-- If there are `ε * (card α)^2` disjoint triangles, then the graph is `ε`-far from being
triangle-free. -/
lemma far_from_triangle_free_of_disjoint_triangles (tris : finset (finset α))
  (htris : tris ⊆ G.clique_finset 3)
  (pd : (tris : set (finset α)).pairwise (λ x y, (x ∩ y).card ≤ 1))
  (tris_big : ε * (card α ^ 2 : ℕ) ≤ tris.card) :
  G.far_from_triangle_free ε :=
begin
  refine far_from_triangle_free_iff.2 (λ H hG hH, _),
  rw ←nat.cast_sub (card_le_of_subset $ edge_finset_mono hG),
  exact tris_big.trans
    (nat.cast_le.2 $ far_from_triangle_free_of_disjoint_triangles_aux htris pd hG hH),
end

end simple_graph
