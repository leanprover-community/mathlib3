/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .regularity_lemma
import .triangle

/-!
# Triangle counting lemma
-/

open finset fintype
open_locale big_operators

variables {α : Type*} {G : simple_graph α}

namespace simple_graph

variables [fintype α]
lemma double_edge_finset_card_eq [decidable_eq α] [decidable_rel G.adj] :
  2 * G.edge_finset.card = (univ.filter (λ (xy : α × α), G.adj xy.1 xy.2)).card :=
begin
  rw [finset.card_eq_sum_ones (finset.filter _ _), sum_partition (sym2.rel.setoid α),
    @sum_const_nat _ _ 2, mul_comm],
  { congr' 2,
    ext x,
    apply sym2.induction_on x,
    simp only [mem_image, true_and, exists_prop, mem_filter, mem_univ, mem_edge_finset,
      mem_edge_set, prod.exists, sym2.eq_iff],
    intros x y,
    refine ⟨λ h, ⟨x, y, h, or.inl ⟨rfl, rfl⟩⟩, _⟩,
    rintro ⟨_, _, h, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩,
    { apply h },
    { apply G.symm h } },
  refine sym2.ind _,
  simp only [mem_image, true_and, and_imp, filter_congr_decidable, exists_prop, mem_filter, mul_one,
    algebra.id.smul_eq_mul, forall_exists_index, mem_univ, sum_const, prod.exists,
    filter_filter],
  rintro x y x' y' h q,
  suffices : filter (λ (a : α × α), G.adj a.fst a.snd ∧ ⟦a⟧ = ⟦(x, y)⟧) univ = {(x',y'), (y',x')},
  { rw [this, card_insert_of_not_mem, card_singleton],
    simp only [mem_singleton, prod.mk.inj_iff, not_and_distrib],
    left,
    apply G.ne_of_adj h },
  ext ⟨i, j⟩,
  simp only [true_and, mem_filter, mem_insert, mem_univ, mem_singleton],
  rw ←q,
  split,
  { rw sym2.eq_iff,
    rintro ⟨_, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩;
    simp },
  rw prod.mk.inj_iff,
  rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩),
  { exact ⟨h, rfl⟩ },
  { exact ⟨G.symm h, sym2.eq_swap⟩, }
end

open_locale classical

lemma reduced_edges_card_aux [nonempty α] {ε : ℝ} {P : finpartition (univ : finset α)}
  (hε : 0 < ε)
  (hP : P.is_equipartition) (hPε : P.is_uniform G (ε/8)) (hP' : 4 / ε ≤ P.parts.card) :
  2 * (G.edge_finset.card - (reduced_graph G ε P).edge_finset.card : ℝ) < 2 * ε * (card α)^2 :=
begin
  have i : univ.filter (λ (xy : α × α), (G.reduced_graph ε P).adj xy.1 xy.2) ⊆
    univ.filter (λ (xy : α × α), G.adj xy.1 xy.2),
  { apply monotone_filter_right,
    rintro ⟨x,y⟩,
    apply reduced_graph_le },
  rw mul_sub,
  norm_cast,
  rw [nat.cast_pow, double_edge_finset_card_eq, double_edge_finset_card_eq,
    ←nat.cast_sub (card_le_of_subset i), ←card_sdiff i],
  refine (nat.cast_le.2 (card_le_of_subset reduced_double_edges)).trans_lt _,
  refine (nat.cast_le.2 (card_union_le _ _)).trans_lt _,
  rw nat.cast_add,
  refine (add_le_add_right (nat.cast_le.2 (card_union_le _ _)) _).trans_lt _,
  rw nat.cast_add,
  have h₁ : 0 ≤ ε/4, linarith,
  refine (add_le_add_left (sum_sparse h₁ P hP) _).trans_lt _,
  rw add_right_comm,
  refine (add_le_add_left (internal_killed_card' hε hP hP') _).trans_lt _,
  rw add_assoc,
  have h₂ : 0 < ε/8, linarith,
  refine (add_lt_add_right (sum_irreg_pairs_le_of_uniform' h₂ P hP hPε) _).trans_le _,
  apply le_of_eq,
  ring,
end

lemma triangle_removal_2 {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1)
  (hG : G.triangle_free_far ε) :
  triangle_removal_bound ε * (card α)^3 ≤ G.triangle_finset.card :=
begin
  let l : ℕ := nat.ceil (4/ε),
  have hl : 4/ε ≤ l := nat.le_ceil (4/ε),
  let ε' : ℝ := ε/8,
  have hε' : 0 < ε/8 := by linarith,
  casesI is_empty_or_nonempty α with i i,
  { simp [fintype.card_eq_zero] },
  cases lt_or_le (card α) l with hl' hl',
  { have : (card α : ℝ)^3 < l^3 :=
      pow_lt_pow_of_lt_left (nat.cast_lt.2 hl') (nat.cast_nonneg _) (by norm_num),
    refine (mul_le_mul_of_nonneg_left this.le (triangle_removal_bound_pos hε hε₁).le).trans _,
    apply (triangle_removal_bound_mul_cube_lt hε).le.trans,
    simp only [nat.one_le_cast],
    apply hG.triangle_finset_card_pos hε },
  obtain ⟨P, hP₁, hP₂, hP₃, hP₄⟩ := szemeredi_regularity G l hε' hl',
  have : 4/ε ≤ P.parts.card := hl.trans (nat.cast_le.2 hP₂),
  have k := reduced_edges_card_aux hε hP₁ hP₄ this,
  rw mul_assoc at k,
  replace k := lt_of_mul_lt_mul_left k zero_le_two,
  obtain ⟨t, ht⟩ := has_triangle_of_few_edges_removed G reduced_graph_le hG k,
  apply triangle_removal_aux hε hε₁ hP₁ hP₃ hP₄ ht,
end

/-- If there are not too many triangles, then you can remove some edges to remove all triangles. -/
lemma triangle_removal {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1)
  (hG : (G.triangle_finset.card : ℝ) < triangle_removal_bound ε * (card α)^3) :
  ∃ (G' ≤ G),
    (G.edge_finset.card - G'.edge_finset.card : ℝ) < ε * (card α)^2
      ∧ G'.no_triangles :=
begin
  by_contra,
  push_neg at h,
  have : G.triangle_free_far ε,
  { intros G' hG hG',
    apply le_of_not_lt,
    intro i,
    apply h G' hG i hG' },
  apply not_le_of_lt hG (triangle_removal_2 hε hε₁ this),
end

end simple_graph
