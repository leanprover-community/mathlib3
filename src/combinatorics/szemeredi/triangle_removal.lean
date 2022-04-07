/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .regularity_lemma
import .triangle_counting

/-!
# Triangle removal lemma

In this file, we prove the triangle removal lemma.
-/

open finset fintype szemeredi_regularity
open_locale classical

variables {α : Type*} [fintype α] {G : simple_graph α}

namespace simple_graph

/-- An explicit form for the constant in the triangle removal lemma. -/
noncomputable def triangle_removal_bound (ε : ℝ) : ℝ :=
min (1 / (2 * ⌈4/ε⌉₊^3)) ((1 - ε/4) * (ε/(16 * bound (ε/8) ⌈4/ε⌉₊))^3)

lemma triangle_removal_bound_pos {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
  0 < triangle_removal_bound ε :=
begin
  apply lt_min,
  { rw one_div_pos,
    refine mul_pos zero_lt_two (pow_pos _ _),
    rw [nat.cast_pos, nat.lt_ceil, nat.cast_zero],
    exact div_pos zero_lt_four hε },
  { exact mul_pos (by linarith) (pow_pos (div_pos hε $ mul_pos (by norm_num) $ nat.cast_pos.2 $
      bound_pos _ _) _) }
end

lemma triangle_removal_bound_mul_cube_lt {ε : ℝ} (hε : 0 < ε) :
  (triangle_removal_bound ε) * ⌈4/ε⌉₊^3 < 1 :=
begin
  have : triangle_removal_bound ε ≤ _ := min_le_left _ _,
  apply (mul_le_mul_of_nonneg_right this (pow_nonneg (nat.cast_nonneg _) _)).trans_lt,
  rw [←div_div_eq_div_mul, div_mul_cancel],
  { norm_num },
  apply ne_of_gt (pow_pos _ _),
  rw [nat.cast_pos, nat.lt_ceil, nat.cast_zero],
  exact div_pos zero_lt_four hε
end

lemma card_bound [nonempty α] {ε : ℝ} {X : finset α} {P : finpartition (univ : finset α)}
  (hP₁ : P.is_equipartition) (hP₃ : P.parts.card ≤ bound (ε / 8) ⌈4/ε⌉₊)
  (hX : X ∈ P.parts) :
  (card α : ℝ) / (2 * bound (ε / 8) ⌈4/ε⌉₊) ≤ X.card :=
begin
  refine le_trans _ (nat.cast_le.2 (hP₁.average_le_card_part hX)),
  rw div_le_iff',
  { norm_cast,
    apply (annoying_thing (P.parts_nonempty $ univ_nonempty.ne_empty).card_pos
      P.card_parts_le_card).le.trans,
    apply nat.mul_le_mul_right,
    exact nat.mul_le_mul_left _ hP₃ },
  refine mul_pos zero_lt_two (nat.cast_pos.2 $ bound_pos _ _),
end

lemma triangle_removal_aux [nonempty α] {ε : ℝ}
  (hε : 0 < ε) (hε₁ : ε ≤ 1)
  {P : finpartition univ}
  (hP₁ : P.is_equipartition)
  (hP₃ : P.parts.card ≤ bound (ε / 8) ⌈4/ε⌉₊)
  {t : finset α} (ht : t ∈ (G.reduced_graph ε P).triangle_finset) :
  triangle_removal_bound ε * ↑(card α) ^ 3 ≤ ↑(G.triangle_finset.card) :=
begin
  rw [mem_triangle_finset, card_eq_three] at ht,
  obtain ⟨⟨x, y, z, xy, xz, yz, rfl⟩, ht⟩ := ht,
  simp only [coe_insert, coe_singleton] at ht,
  have hx : x ∈ ({x,y,z} : set α) := or.inl rfl,
  have hy : y ∈ ({x,y,z} : set α) := or.inr (or.inl rfl),
  have hz : z ∈ ({x,y,z} : set α) := or.inr (or.inr rfl),
  have hxy : (G.reduced_graph ε P).adj x y := ht hx hy xy,
  have hxz : (G.reduced_graph ε P).adj x z := ht hx hz xz,
  have hyz : (G.reduced_graph ε P).adj y z := ht hy hz yz,
  obtain ⟨xy, X, hX, Y, hY, xX, yY, nXY, uXY, dXY⟩ := hxy,
  obtain ⟨xz, X', hX', Z, hZ, xX', zZ, nXZ, uXZ, dXZ⟩ := hxz,
  cases P.disjoint.elim hX hX' (not_disjoint_iff.2 ⟨x, xX, xX'⟩),
  obtain ⟨yz, Y', hY', Z', hZ', yY', zZ', nYZ, uYZ, dYZ⟩ := hyz,
  cases P.disjoint.elim hY hY' (not_disjoint_iff.2 ⟨y, yY, yY'⟩),
  cases P.disjoint.elim hZ hZ' (not_disjoint_iff.2 ⟨z, zZ, zZ'⟩),
  have dXY := P.disjoint hX hY nXY,
  have dXZ := P.disjoint hX hZ nXZ,
  have dYZ := P.disjoint hY hZ nYZ,
  have : 2 * (ε/8) = ε/4, by ring,
  have i := triangle_counting2 G (by rwa this) uXY dXY (by rwa this) uXZ dXZ (by rwa this) uYZ dYZ,
  apply le_trans _ i,
  rw [this, triangle_removal_bound],
  refine (mul_le_mul_of_nonneg_right (min_le_right (_:ℝ) _) (pow_nonneg _ _)).trans _,
  apply nat.cast_nonneg,
  rw [mul_assoc, ←mul_pow, div_mul_eq_mul_div, (show (16:ℝ) = 8 * 2, by norm_num), mul_assoc (8:ℝ),
    ←div_mul_div_comm₀, mul_pow, ←mul_assoc],
  suffices : ((card α : ℝ) / (2 * bound (ε / 8) ⌈4 / ε⌉₊)) ^ 3 ≤ X.card * Y.card * Z.card,
  { refine (mul_le_mul_of_nonneg_left this (mul_nonneg _ _)).trans _,
    { linarith },
    { apply pow_nonneg,
      apply div_nonneg hε.le,
      norm_num },
    apply le_of_eq,
    ring },
  rw [pow_succ, sq, mul_assoc],
  refine mul_le_mul (card_bound hP₁ hP₃ hX) _ (mul_nonneg _ _) (nat.cast_nonneg _),
  refine mul_le_mul (card_bound hP₁ hP₃ hY) (card_bound hP₁ hP₃ hZ) _ (nat.cast_nonneg _),
  all_goals
  { exact div_nonneg (nat.cast_nonneg _) (mul_nonneg (by norm_num) $ nat.cast_nonneg _) }
end

lemma reduced_edges_card_aux [nonempty α] {ε : ℝ} {P : finpartition (univ : finset α)} (hε : 0 < ε)
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

lemma triangle_removal_2 {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (hG : G.triangle_free_far ε) :
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
  apply triangle_removal_aux hε hε₁ hP₁ hP₃ ht,
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
