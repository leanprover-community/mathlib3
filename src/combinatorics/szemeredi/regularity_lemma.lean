/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .increment
import analysis.special_functions.pow
import order.iterate

/-!
# Szemerédi's Regularity Lemma

In this file, we prove Szemerédi's Regularity Lemma.
-/

open_locale big_operators classical
open finpartition finset fintype function

variables {α : Type*} [fintype α] {P : finpartition (univ : finset α)} (hP : P.is_equipartition)
  (G : simple_graph α) (ε : ℝ)

local notation `m` := (card α/exp_bound P.size : ℕ)

/-- The maximal number of times we need to blow up an equipartition to make it uniform -/
noncomputable def iteration_bound (ε : ℝ) (l : ℕ) : ℕ :=
max (max 7 l) (⌊real.log (100/ε^5) / real.log 4⌋₊ + 1)

lemma le_iteration_bound (ε : ℝ) (l : ℕ) : l ≤ iteration_bound ε l :=
(le_max_right _ _).trans (le_max_left _ _)

lemma one_hundred_le_iteration_bound (ε : ℝ) (l : ℕ) : 7 ≤ iteration_bound ε l :=
(le_max_left _ _).trans (le_max_left _ _)

lemma iteration_bound_pos (ε : ℝ) (l : ℕ) : 0 < iteration_bound ε l :=
nat.succ_pos'.trans_le (le_max_right _ _)

lemma const_lt_pow_iteration_bound_mul {ε : ℝ} (hε : 0 < ε) (l : ℕ) :
  100 < 4^iteration_bound ε l * ε^5 :=
begin
  rw [←real.rpow_nat_cast 4, ←div_lt_iff (pow_pos hε 5), real.lt_rpow_iff_log_lt _ zero_lt_four,
    ←div_lt_iff, iteration_bound, nat.cast_max],
  { exact lt_max_of_lt_right (nat.lt_floor_add_one _) },
  { apply real.log_pos,
    norm_num },
  { exact div_pos (by norm_num) (pow_pos hε 5) }
end

/-- An explicit bound on the size of the equipartition in the proof of Szemerédi's Regularity Lemma
-/
noncomputable def szemeredi_bound (ε : ℝ) (l : ℕ) : ℕ :=
(exp_bound^[⌊4 / ε^5⌋₊] (iteration_bound ε l)) *
  16^(exp_bound^[⌊4 / ε^5⌋₊] (iteration_bound ε l))

lemma iteration_bound_le_szemeredi_bound (ε l) :
  iteration_bound ε l ≤ szemeredi_bound ε l :=
(id_le_iterate_of_id_le le_exp_bound _ _).trans
  (nat.le_mul_of_pos_right (pow_pos (by norm_num) _))

/-- Effective Szemerédi's Regularity Lemma: For any sufficiently big graph, there is an ε-uniform
equipartition of bounded size (where the bound does not depend on the graph). -/
theorem szemeredi_regularity {ε : ℝ} (l : ℕ) (hε : 0 < ε) (hε' : ε ≤ 1)
  (hG : l ≤ card α) :
  ∃ (P : finpartition (univ : finset α)),
    P.is_equipartition ∧ l ≤ P.parts.card ∧ P.parts.card ≤ szemeredi_bound ε l ∧ P.is_uniform G ε :=
begin
  obtain hα | hα := le_total (card α) (szemeredi_bound ε l),
  { refine ⟨finpartition.discrete _, discrete_is_equipartition _, _⟩,
    rw [card_discrete, card_univ],
    exact ⟨hG, hα, discrete_is_uniform _ hε⟩ },
  let t := iteration_bound ε l,
  have ht : 0 < t := iteration_bound_pos _ _,
  haveI : nonempty α,
  { rw ←fintype.card_pos_iff,
    apply ht.trans_le ((iteration_bound_le_szemeredi_bound _ _).trans hα) },
  suffices h : ∀ i, ∃ (P : finpartition (univ : finset α)), P.is_equipartition ∧
    t ≤ P.parts.card ∧ P.parts.card ≤ (exp_bound^[i]) t ∧
      (P.is_uniform G ε ∨ ε^5 / 4 * i ≤ P.index G),
  { obtain ⟨P, hP₁, hP₂, hP₃, hP₄⟩ := h (⌊4 / ε^5⌋₊ + 1),
    refine ⟨P, hP₁, (le_iteration_bound _ _).trans hP₂, hP₃.trans _, _⟩,
    { rw function.iterate_succ_apply',
      exact mul_le_mul_left' (pow_le_pow_of_le_left (by norm_num) (by norm_num) _) _ },
    apply hP₄.resolve_right,
    rintro hPindex,
    apply lt_irrefl (1 : ℝ),
    calc
      1 = ε ^ 5 / 4 * (4 / ε ^ 5)
          : by { rw [mul_comm, div_mul_div_cancel 4 (pow_pos hε 5).ne'], norm_num }
      ... < ε ^ 5 / 4 * (⌊4 / ε ^ 5⌋₊ + 1)
          : (mul_lt_mul_left (div_pos (pow_pos hε 5) (by norm_num))).2 (nat.lt_floor_add_one _)
      ... ≤ P.index G : hPindex
      ... ≤ 1 : P.index_le_one G },
  intro i,
  induction i with i ih,
  { have : t ≤ (univ : finset α).card :=
      (iteration_bound_le_szemeredi_bound _ _).trans (by rwa finset.card_univ),
    obtain ⟨P, hP₁, hP₂⟩ := dummy_equipartition (univ : finset α) ht this,
    refine ⟨P, hP₁, hP₂.ge, hP₂.le, or.inr _⟩,
    rw [nat.cast_zero, mul_zero],
    exact P.index_nonneg G },
  obtain ⟨P, hP₁, hP₂, hP₃, hP₄⟩ := ih,
  by_cases huniform : P.is_uniform G ε,
  { refine ⟨P, hP₁, hP₂, _, or.inl huniform⟩,
    rw function.iterate_succ_apply',
    exact hP₃.trans (le_exp_bound _) },
  replace hP₄ := hP₄.resolve_left huniform,
  have hεl' : 100 < 4 ^ P.parts.card * ε ^ 5,
  { apply (const_lt_pow_iteration_bound_mul hε l).trans_le,
    rw mul_le_mul_right (pow_pos hε 5),
    refine pow_le_pow (by norm_num) hP₂ },
  have hi : (i : ℝ) ≤ 4 / ε^5,
  { have hi := hP₄.trans (P.index_le_one G),
    rw [div_mul_eq_mul_div, div_le_iff (show (0:ℝ) < 4, by norm_num)] at hi,
    norm_num at hi,
    rwa le_div_iff' (pow_pos hε _) },
  have hsize : P.parts.card ≤ (exp_bound^[⌊4 / ε^5⌋₊] t) :=
    hP₃.trans (iterate_le_iterate_of_id_le le_exp_bound (nat.le_floor_of_le hi) _),
  have hPα : P.parts.card * 16^P.parts.card ≤ card α :=
    (nat.mul_le_mul hsize (nat.pow_le_pow_of_le_right (by norm_num) hsize)).trans hα,
  refine ⟨hP₁.increment G ε, increment_is_equipartition hP₁ G ε, _, _,
    or.inr (le_trans _ (index_increment hP₁ ((one_hundred_le_iteration_bound ε l).trans hP₂)
      hεl' hPα huniform hε'))⟩,
  { rw card_increment hPα huniform,
    exact hP₂.trans (le_exp_bound _) },
  { rw [card_increment hPα huniform, function.iterate_succ_apply'],
    exact exp_bound_mono hP₃ },
  { rw [nat.cast_succ, mul_add, mul_one],
    exact add_le_add_right hP₄ _ }
end
