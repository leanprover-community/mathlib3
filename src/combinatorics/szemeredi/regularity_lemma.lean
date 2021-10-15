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
open finset fintype function

variables {α : Type*} [fintype α] {P : finpartition (univ : finset α)} (hP : P.is_equipartition)
  (G : simple_graph α) (ε : ℝ)

local notation `m` := (card α/exp_bound P.size : ℕ)
local notation `a` := (card α/P.size - m * 4^P.size : ℕ)

/-- The maximal number of times we need to blow up an equipartition to make it uniform -/
noncomputable def iteration_bound (ε : ℝ) (l : ℕ) : ℕ :=
max (max 100 l) (nat_floor (real.log (100/ε^5) / real.log 4) + 1)

lemma le_iteration_bound (ε : ℝ) (l : ℕ) : l ≤ iteration_bound ε l :=
(le_max_right _ _).trans (le_max_left _ _)

lemma one_hundred_le_iteration_bound (ε : ℝ) (l : ℕ) : 100 ≤ iteration_bound ε l :=
(le_max_left _ _).trans (le_max_left _ _)

lemma iteration_bound_pos (ε : ℝ) (l : ℕ) : 0 < iteration_bound ε l :=
nat.succ_pos'.trans_le (le_max_right _ _)

lemma const_lt_mul_pow_iteration_bound {ε : ℝ} (hε : 0 < ε) (l : ℕ) :
  100 < ε^5 * 4^iteration_bound ε l :=
begin
  rw [←real.rpow_nat_cast 4, ←div_lt_iff' (pow_pos hε 5), real.lt_rpow_iff_log_lt, ←div_lt_iff,
    iteration_bound, nat.cast_max],
  { exact lt_max_of_lt_right (lt_nat_floor_add_one _) },
  { apply real.log_pos,
    norm_num },
  { exact div_pos (by norm_num) (pow_pos hε 5) },
  norm_num,
end

/-- An explicit bound on the size of the equipartition in the proof of Szemerédi's Regularity Lemma
-/
noncomputable def szemeredi_bound (ε : ℝ) (l : ℕ) : ℕ :=
(exp_bound^[nat_floor (4/ε^5)] (iteration_bound ε l)) *
  16^(exp_bound^[nat_floor (4/ε^5)] (iteration_bound ε l))

lemma iteration_bound_le_szemeredi_bound (ε l) :
  iteration_bound ε l ≤ szemeredi_bound ε l :=
(id_le_iterate_of_id_le le_exp_bound _ _).trans
  (nat.le_mul_of_pos_right (pow_pos (by norm_num) _))

/-- Effective Szemerédi's Regularity Lemma: For any sufficiently big graph, there is an ε-uniform
equipartition of bounded size (where the bound does not depend on the graph). -/
theorem szemeredi_regularity {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1) (l : ℕ)
  (hG : l ≤ card α) :
  ∃ (P : finpartition (univ : finset α)),
    P.is_equipartition ∧ l ≤ P.size ∧ P.size ≤ szemeredi_bound ε l ∧ P.is_uniform G ε :=
begin
  obtain hα | hα := le_total (card α) (szemeredi_bound ε l),
  { refine ⟨discrete_finpartition _, discrete_finpartition.is_equipartition _, _⟩,
    rw [discrete_finpartition.size, card_univ],
    exact ⟨hG, hα, discrete_finpartition.is_uniform _ hε⟩ },
  let t := iteration_bound ε l,
  have ht : 0 < t := iteration_bound_pos _ _,
  haveI : nonempty α,
  { rw ←fintype.card_pos_iff,
    apply ht.trans_le ((iteration_bound_le_szemeredi_bound _ _).trans hα) },
  suffices h : ∀ i, ∃ (P : finpartition (univ : finset α)), P.is_equipartition ∧
    t ≤ P.size ∧ P.size ≤ (exp_bound^[i]) t ∧ (P.is_uniform G ε ∨ ε^5 / 8 * i ≤ P.index G),
  { obtain ⟨P, hP₁, hP₂, hP₃, hP₄⟩ := h (nat_floor (4/ε^5) + 1),
    refine ⟨P, hP₁, (le_iteration_bound _ _).trans hP₂, hP₃.trans _, _⟩,
    { rw function.iterate_succ_apply',
      exact mul_le_mul_left' (pow_le_pow_of_le_left (by norm_num) (by norm_num) _) _ },
    apply hP₄.resolve_right,
    rintro hPindex,
    apply lt_irrefl (1/2 : ℝ),
    calc
      1/2 = ε ^ 5 / 8 * (4 / ε ^ 5)
          : by { rw [mul_comm, div_mul_div_cancel 4 (pow_pos hε 5).ne'], norm_num }
      ... < ε ^ 5 / 8 * (nat_floor (4 / ε ^ 5) + 1)
          : (mul_lt_mul_left (div_pos (pow_pos hε 5) (by norm_num))).2 (lt_nat_floor_add_one _)
      ... ≤ P.index G : hPindex
      ... ≤ 1/2 : P.index_le_half G },
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
  have hεl' : 100 < ε ^ 5 * 4 ^ P.size,
  { apply lt_of_lt_of_le (const_lt_mul_pow_iteration_bound hε l),
    rw mul_le_mul_left (pow_pos hε 5),
    refine pow_le_pow (by norm_num) hP₂ },
  have hi : (i : ℝ) ≤ 4 / ε^5,
  { have hi := hP₄.trans (P.index_le_half G),
    rw [div_mul_eq_mul_div, div_le_iff (show (0:ℝ) < 8, by norm_num)] at hi,
    norm_num at hi,
    rwa le_div_iff' (pow_pos hε _) },
  have hsize : P.size ≤ (exp_bound^[nat_floor (4/ε^5)] t) :=
    hP₃.trans (iterate_le_iterate_of_id_le le_exp_bound (le_nat_floor_of_le hi) _),
  have hPα : P.size * 16^P.size ≤ card α :=
    (nat.mul_le_mul hsize (nat.pow_le_pow_of_le_right (by norm_num) hsize)).trans hα,
  refine ⟨hP₁.increment G ε, increment.is_equipartition hP₁ G ε, _, _,
    or.inr (le_trans _ (increment.index hP₁ ((one_hundred_le_iteration_bound ε l).trans hP₂)
      hεl' hPα huniform))⟩,
  { rw increment.size hP₁ hPα huniform,
    exact hP₂.trans (le_exp_bound _) },
  { rw [increment.size hP₁ hPα huniform, function.iterate_succ_apply'],
    exact exp_bound_mono hP₃ },
  { rw [nat.cast_succ, mul_add, mul_one],
    exact add_le_add_right hP₄ _ }
end
