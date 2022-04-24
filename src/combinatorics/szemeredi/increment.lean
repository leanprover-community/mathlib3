/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .chunk
import combinatorics.simple_graph.regularity.energy

/-!
# Increment
-/

universes u v

open finset fintype simple_graph szemeredi_regularity
open_locale big_operators classical

variables {α : Type*} [fintype α] {P : finpartition (univ : finset α)} (hP : P.is_equipartition)
  (G : simple_graph α) (ε : ℝ)

local notation `m` := (card α/step_bound P.parts.card : ℕ)

namespace finpartition

/-- The work-horse of SRL. This says that if we have an equipartition which is *not* uniform, then
we can make a (much bigger) equipartition with a slightly higher energy. This is helpful since the
energy is bounded by a constant (see `energy_le_one`), so this process eventually terminates and
yields a not-too-big uniform equipartition. -/
noncomputable def is_equipartition.increment : finpartition (univ : finset α) :=
P.bind (λ U, hP.chunk_increment G ε)

open finpartition finpartition.is_equipartition

variables {hP G ε}

lemma card_increment (hPα : P.parts.card * 16^P.parts.card ≤ card α) (hPG : ¬P.is_uniform G ε) :
  (hP.increment G ε).parts.card = step_bound P.parts.card :=
begin
  have hPα' : step_bound P.parts.card ≤ card α :=
    (nat.mul_le_mul_of_nonneg_left $ nat.pow_le_pow_of_le_left (by norm_num) _).trans hPα,
  have hPpos : 0 < step_bound P.parts.card := step_bound_pos (nonempty_of_not_uniform hPG).card_pos,
  rw [is_equipartition, finset.equitable_on_iff] at hP,
  rw [increment, card_bind],
  simp_rw [finpartition.is_equipartition.chunk_increment, apply_dite finpartition.parts,
    apply_dite card],
  rw [sum_dite, sum_const_nat, sum_const_nat, card_attach, card_attach], rotate,
  { exact λ x hx, card_parts_equitabilise (nat.div_pos hPα' hPpos).ne' _ },
  { exact λ x hx, card_parts_equitabilise (nat.div_pos hPα' hPpos).ne' _ },
  rw [nat.sub_add_cancel a_add_one_le_four_pow_parts_card, nat.sub_add_cancel ((nat.le_succ _).trans
    a_add_one_le_four_pow_parts_card), ←add_mul],
  congr,
  rw [filter_card_add_filter_neg_card_eq_card, card_attach],
end

lemma increment_is_equipartition (hP : P.is_equipartition) (G : simple_graph α) (ε : ℝ) :
  (hP.increment G ε).is_equipartition :=
begin
  rw [is_equipartition, set.equitable_on_iff_exists_eq_eq_add_one],
  refine ⟨m, λ A hA, _⟩,
  rw [mem_coe, increment, mem_bind] at hA,
  obtain ⟨U, hU, hA⟩ := hA,
  exact card_eq_of_mem_parts_chunk_increment hA,
end

lemma distinct_pairs_increment :
  P.parts.off_diag.attach.bUnion
    (λ UV, (hP.chunk_increment G ε ((mem_off_diag _ _).1 UV.2).1).parts.product
      (hP.chunk_increment G ε ((mem_off_diag _ _).1 UV.2).2.1).parts)
  ⊆ (hP.increment G ε).parts.off_diag :=
begin
  rintro ⟨Ui, Vj⟩,
  simp only [finpartition.is_equipartition.increment, mem_off_diag, bind_parts, mem_bUnion,
    prod.exists, exists_and_distrib_left, exists_prop, mem_product, mem_attach, true_and,
    subtype.exists, and_imp, mem_off_diag, forall_exists_index, bex_imp_distrib, ne.def],
  rintro U V hUV hUi hVj,
  refine ⟨⟨_, hUV.1, hUi⟩, ⟨_, hUV.2.1, hVj⟩, _⟩,
  rintro rfl,
  obtain ⟨i, hi⟩ := nonempty_of_mem_parts _ hUi,
  apply hUV.2.2 (P.disjoint.elim_finset hUV.1 hUV.2.1 i (finpartition.le _ hUi hi)
    (finpartition.le _ hVj hi)),
end

/-- The contribution to `energy` of a pair of distinct parts of a finpartition. -/
noncomputable def pair_contrib (G : simple_graph α) (ε : ℝ) (hP : P.is_equipartition)
  (x : {x // x ∈ P.parts.off_diag}) : ℚ :=
(∑ i in
  (hP.chunk_increment G ε ((mem_off_diag _ _).1 x.2).1).parts.product
    (hP.chunk_increment G ε ((mem_off_diag _ _).1 x.2).2.1).parts,
  G.edge_density i.fst i.snd ^ 2)

lemma off_diag_pairs_le_increment_energy :
  ∑ x in P.parts.off_diag.attach, pair_contrib G ε hP x / (hP.increment G ε).parts.card ^ 2 ≤
    (hP.increment G ε).energy G :=
begin
  simp_rw [pair_contrib, ←sum_div],
  refine div_le_div_of_le_of_nonneg _ (sq_nonneg _),
  rw ←sum_bUnion,
  { exact sum_le_sum_of_subset_of_nonneg distinct_pairs_increment (λ i _ _, sq_nonneg _) },
  rintro ⟨⟨s₁, s₂⟩, hs⟩ _ ⟨⟨t₁, t₂⟩, ht⟩ _ hst ⟨u, v⟩ huv,
  simp only [inf_eq_inter, mem_inter, mem_product] at huv,
  rw mem_off_diag at hs ht,
  obtain ⟨a, ha⟩ := finpartition.nonempty_of_mem_parts _ huv.1.1,
  obtain ⟨b, hb⟩ := finpartition.nonempty_of_mem_parts _ huv.1.2,
  exact hst (subtype.ext_val $ prod.ext
    (P.disjoint.elim_finset hs.1 ht.1 a
      (finpartition.le _ huv.1.1 ha) (finpartition.le _ huv.2.1 ha))
    (P.disjoint.elim_finset hs.2.1 ht.2.1 b
      (finpartition.le _ huv.1.2 hb) (finpartition.le _ huv.2.2 hb))),
end

lemma pair_contrib_lower_bound [nonempty α] (x : {i // i ∈ P.parts.off_diag}) (hε₁ : ε ≤ 1)
  (hPα : P.parts.card * 16^P.parts.card ≤ card α) (hPε : 100 ≤ 4^P.parts.card * ε^5) :
  ↑(G.edge_density x.1.1 x.1.2)^2 - ε^5/25 + (if G.is_uniform ε x.1.1 x.1.2 then 0 else ε^4/3) ≤
    pair_contrib G ε hP x / (16^P.parts.card) :=
begin
  rw pair_contrib,
  push_cast,
  split_ifs,
  { rw add_zero,
    exact sq_density_sub_eps_le_sum_sq_density_div_card hPα hPε _ _ },
  { apply sq_density_sub_eps_le_sum_sq_density_div_card_of_nonuniform hPα hPε hε₁ _ h,
    exact ((mem_off_diag _ _).1 x.2).2.2 }
end

lemma uniform_add_nonuniform_eq_off_diag_pairs [nonempty α] (hε₁ : ε ≤ 1) (hP₇ : 7 ≤ P.parts.card)
  (hPα : P.parts.card * 16^P.parts.card ≤ card α) (hPε : 100 ≤ 4^P.parts.card * ε^5)
  (hPG : ¬P.is_uniform G ε) :
  (∑ x in P.parts.off_diag, G.edge_density x.1 x.2 ^ 2 + P.parts.card^2 * (ε ^ 5 / 4) : ℝ)
    / P.parts.card ^ 2
      ≤ ∑ x in P.parts.off_diag.attach, pair_contrib G ε hP x / (hP.increment G ε).parts.card ^ 2 :=
begin
  conv_rhs
  { rw [←sum_div, card_increment hPα hPG, step_bound, ←nat.cast_pow, mul_pow, pow_right_comm,
      nat.cast_mul, mul_comm, ←div_div_eq_div_mul, (show 4^2 = 16, by norm_num), sum_div] },
  rw [←nat.cast_pow, nat.cast_pow 16],
  refine div_le_div_of_le_of_nonneg _ (nat.cast_nonneg _),
  norm_num,
  suffices : _ ≤ ∑ x in P.parts.off_diag.attach,
      (G.edge_density x.1.1 x.1.2^2 - ε^5/25 + if G.is_uniform ε x.1.1 x.1.2 then 0 else ε^4/3 : ℝ),
  { apply le_trans this (sum_le_sum (λ i hi, pair_contrib_lower_bound i hε₁ hPα hPε)) },
  have : ∑ x in P.parts.off_diag.attach,
    (G.edge_density x.1.1 x.1.2^2 - ε^5/25 + if G.is_uniform ε x.1.1 x.1.2 then 0 else ε^4/3 : ℝ) =
    ∑ x in P.parts.off_diag,
      (G.edge_density x.1 x.2^2 - ε^5/25 + if G.is_uniform ε x.1 x.2 then 0 else ε^4/3),
  { convert sum_attach, refl },
  rw [this, sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, sum_ite, sum_const_zero,
    zero_add, sum_const, nsmul_eq_mul, ←finpartition.non_uniforms],
  rw finpartition.is_uniform at hPG,
  simp only [not_le] at hPG,
  apply le_trans _ (add_le_add_left (mul_le_mul_of_nonneg_right hPG.le _) _),
  { conv_rhs { congr, congr, skip, rw [off_diag_card], congr, congr,
      conv { congr, skip, rw ←mul_one P.parts.card }, rw ←nat.mul_sub_left_distrib },
    simp_rw [mul_assoc, sub_add_eq_add_sub, add_sub_assoc, ←mul_sub_left_distrib, mul_div_assoc' ε,
      ←pow_succ, div_eq_mul_one_div (ε^5), ←mul_sub_left_distrib],
    rw [mul_left_comm, mul_left_comm _ (ε^5), sq, mul_assoc, nat.cast_mul, mul_assoc],
    apply add_le_add_left,
    apply mul_le_mul_of_nonneg_left _ (eps_pow_five_pos hPε).le,
    apply mul_le_mul_of_nonneg_left _ (nat.cast_nonneg _),
    rw [nat.cast_sub (P.parts_nonempty $ univ_nonempty.ne_empty).card_pos, mul_sub_right_distrib,
      nat.cast_one, one_mul, le_sub, ←mul_sub_left_distrib,
      ←div_le_iff (show (0:ℝ) < 1/3 - 1/25 - 1/4, by norm_num)],
    refine le_trans (show _ ≤ (7:ℝ), by norm_num) (by exact_mod_cast hP₇) },
  exact div_nonneg (pow_bit0_nonneg _ _) (by norm_num),
end

lemma energy_increment [nonempty α] (hP : P.is_equipartition) (hP₇ : 7 ≤ P.parts.card)
  (hε : 100 < 4^P.parts.card * ε^5) (hPα : P.parts.card * 16^P.parts.card ≤ card α)
  (hPG : ¬P.is_uniform G ε) (hε₁ : ε ≤ 1) :
  ↑(P.energy G) + ε^5 / 4 ≤ (hP.increment G ε).energy G :=
begin
  have h := uniform_add_nonuniform_eq_off_diag_pairs hε₁ hP₇ hPα hε.le hPG,
  rw [add_div, mul_div_cancel_left] at h,
  rw energy,
  push_cast,
  exact h.trans (by exact_mod_cast off_diag_pairs_le_increment_energy),
  refine (sq_pos_of_ne_zero _ $ _).ne',
  norm_cast,
  linarith,
end

end finpartition
