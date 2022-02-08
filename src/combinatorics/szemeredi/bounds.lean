/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .mathlib

/-!
# Numerical bounds for Szemerédi Regularity Lemma
-/

open finset fintype

variables {α : Type*}

/-- Auxiliary function to explicit the bound on the parts.card of the equipartition in the proof of
Szemerédi's Regularity Lemma -/
def exp_bound (n : ℕ) : ℕ := n * 4^n

lemma le_exp_bound : id ≤ exp_bound :=
λ n, nat.le_mul_of_pos_right (pow_pos (by norm_num) n)

lemma exp_bound_mono : monotone exp_bound :=
λ a b h, nat.mul_le_mul h (nat.pow_le_pow_of_le_right (by norm_num) h)

lemma exp_bound_pos {n : ℕ} : 0 < exp_bound n ↔ 0 < n :=
zero_lt_mul_right (pow_pos (by norm_num) _)

variables [decidable_eq α] [fintype α] {G : simple_graph α} {P : finpartition (univ : finset α)}
  {ε : ℝ}

local notation `m` := (card α/exp_bound P.parts.card : ℕ)
local notation `a` := (card α/P.parts.card - m * 4^P.parts.card : ℕ)

lemma m_pos [nonempty α] (hPα : P.parts.card * 16^P.parts.card ≤ card α) : 0 < m :=
nat.div_pos ((nat.mul_le_mul_left _ (nat.pow_le_pow_of_le_left (by norm_num) _)).trans hPα)
  (exp_bound_pos.2 (P.parts_nonempty $ univ_nonempty.ne_empty).card_pos)

lemma m_coe_pos [nonempty α] (hPα : P.parts.card * 16^P.parts.card ≤ card α) : (0 : ℝ) < m :=
nat.cast_pos.2 $ m_pos hPα

lemma coe_m_add_one_pos : 0 < (m:ℝ) + 1 :=
nat.cast_add_one_pos _

lemma one_le_m_coe [nonempty α] (hPα : P.parts.card * 16^P.parts.card ≤ card α) : (1 : ℝ) ≤ m :=
nat.one_le_cast.2 $ m_pos hPα

lemma eps_pow_five_pos (hPε : 100 ≤ 4^P.parts.card * ε^5) : 0 < ε^5 :=
pos_of_mul_pos_left ((by norm_num : (0 : ℝ) < 100).trans_le hPε) (pow_nonneg (by norm_num) _)

lemma eps_pos (hPε : 100 ≤ 4^P.parts.card * ε^5) : 0 < ε :=
pow_bit1_pos_iff.1 $ eps_pow_five_pos hPε

lemma four_pow_pos {n : ℕ} : 0 < (4 : ℝ)^n := pow_pos (by norm_num) n

lemma hundred_div_ε_pow_five_le_m [nonempty α] (hPα : P.parts.card * 16^P.parts.card ≤ card α)
  (hPε : 100 ≤ 4^P.parts.card * ε^5) :
  100/ε^5 ≤ m :=
(div_le_of_nonneg_of_le_mul (eps_pow_five_pos hPε).le four_pow_pos.le hPε).trans
begin
  norm_cast,
  rwa [nat.le_div_iff_mul_le'(exp_bound_pos.2
    (P.parts_nonempty $ univ_nonempty.ne_empty).card_pos), exp_bound, mul_left_comm, ←mul_pow],
end

lemma hundred_le_m [nonempty α] (hPα : P.parts.card * 16^P.parts.card ≤ card α)
  (hPε : 100 ≤ 4^P.parts.card * ε^5) (hε : ε ≤ 1) : 100 ≤ m :=
by exact_mod_cast
  (le_div_self (by norm_num) (eps_pow_five_pos hPε) (pow_le_one _ (eps_pos hPε).le hε)).trans
    (hundred_div_ε_pow_five_le_m hPα hPε)

lemma a_add_one_le_four_pow_parts_card : a + 1 ≤ 4^P.parts.card :=
begin
  have h : 1 ≤ 4^P.parts.card := one_le_pow_of_one_le (by norm_num) _,
  rw [exp_bound, ←nat.div_div_eq_div_mul, nat.add_le_to_le_sub _ h, tsub_le_iff_left,
    ←nat.add_sub_assoc h],
  exact nat.le_pred_of_lt (nat.lt_div_mul_add h),
end

lemma card_aux₁ : m * 4^P.parts.card + a = (4^P.parts.card - a) * m + a * (m + 1) :=
by rw [mul_add, mul_one, ←add_assoc, ←add_mul, nat.sub_add_cancel
  ((nat.le_succ _).trans a_add_one_le_four_pow_parts_card), mul_comm]

lemma card_aux₂ {U : finset α} (hUcard : U.card = m * 4^P.parts.card + a) :
  (4^P.parts.card - a) * m + a * (m + 1) = U.card :=
by rw [hUcard, mul_add, mul_one, ←add_assoc, ←add_mul, nat.sub_add_cancel
  ((nat.le_succ _).trans a_add_one_le_four_pow_parts_card), mul_comm]

lemma card_aux₃ (hP : P.is_equipartition) {U : finset α} (hU : U ∈ P.parts)
  (hUcard : ¬U.card = m * 4^P.parts.card + a) :
  (4^P.parts.card - (a + 1)) * m + (a + 1) * (m + 1) = U.card :=
begin
  have : m * 4 ^ P.parts.card ≤ card α / P.parts.card,
  { rw [exp_bound, ←nat.div_div_eq_div_mul],
    apply nat.div_mul_le_self },
  rw (nat.add_sub_of_le this) at hUcard,
  rw finpartition.is_equipartition_iff_card_parts_eq_average' at hP,
  rw [(hP U hU).resolve_left hUcard, mul_add, mul_one, ←add_assoc, ←add_mul, nat.sub_add_cancel
    a_add_one_le_four_pow_parts_card, ←add_assoc, mul_comm, nat.add_sub_of_le this],
end

lemma pow_mul_m_le_card_part (hP : P.is_equipartition) {U : finset α} (hU : U ∈ P.parts) :
  (4 : ℝ) ^ P.parts.card * m ≤ U.card :=
begin
  norm_cast,
  rw [exp_bound, ←nat.div_div_eq_div_mul],
  exact (nat.mul_div_le _ _).trans (hP.average_le_card_part hU),
end
