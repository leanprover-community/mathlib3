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

/-- Auxiliary function to explicit the bound on the size of the equipartition in the proof of
Szemerédi's Regularity Lemma -/
def exp_bound (n : ℕ) : ℕ := n * 4^n

lemma le_exp_bound :
 id ≤ exp_bound :=
λ n, nat.le_mul_of_pos_right (pow_pos (by norm_num) n)

lemma exp_bound_mono :
  monotone exp_bound :=
λ a b h, nat.mul_le_mul h (nat.pow_le_pow_of_le_right (by norm_num) h)

lemma exp_bound_pos {n : ℕ} : 0 < exp_bound n ↔ 0 < n :=
begin
  rw exp_bound,
  exact zero_lt_mul_right (pow_pos (by norm_num) _),
end

variables [decidable_eq α] [fintype α] {G : simple_graph α} {P : finpartition α} {ε : ℝ}

local notation `m` := (card α/exp_bound P.size : ℕ)
local notation `a` := (card α/P.size - m * 4^P.size : ℕ)

lemma m_pos [nonempty α] (hPα : P.size * 16^P.size ≤ card α) : 0 < m :=
begin
  refine nat.div_pos ((nat.mul_le_mul_left _ (nat.pow_le_pow_of_le_left (by norm_num) _)).trans hPα)
    _,
  rw [exp_bound_pos, P.size_eq_card_parts, card_pos],
  exact P.parts_nonempty,
end

lemma hundred_div_ε_pow_five_le_m [nonempty α] (hPα : P.size * 16^P.size ≤ card α)
  (hPε : 100 ≤ 4^P.size * ε^5) :
  100/ε^5 ≤ m :=
begin
  calc
    100/ε^5
        ≤ 4^P.size : div_le_of_nonneg_of_le_mul (nonneg_of_mul_nonneg_left
          (le_trans (by norm_num) hPε) (pow_pos (by norm_num) _)) (pow_nonneg (by norm_num) _) hPε
    ... = ((P.size * 16^P.size)/exp_bound P.size : ℕ) : begin
      norm_cast,
      refine (nat.div_eq_of_eq_mul_left _ _).symm,
      { rw [exp_bound_pos, P.size_eq_card_parts, card_pos],
        exact P.parts_nonempty },
      rw [exp_bound, mul_comm (4^P.size), mul_assoc, ←mul_pow],
      norm_num,
    end
    ... ≤ m : nat.cast_le.2 (nat.div_le_div_right hPα)
end

lemma a_add_one_le_four_pow_size :
  a + 1 ≤ 4^P.size :=
begin
  have h : 1 ≤ 4^P.size := one_le_pow_of_one_le (by norm_num) _,
  rw [exp_bound, ←nat.div_div_eq_div_mul, nat.add_le_to_le_sub _ h, sub_le_iff_left,
    ←nat.add_sub_assoc h],
  exact nat.le_pred_of_lt (nat.lt_div_mul_add h),
end

lemma card_aux₁ :
  m * 4^P.size + a = (4^P.size - a) * m + a * (m + 1) :=
by rw [mul_add, mul_one, ←add_assoc, ←add_mul, nat.sub_add_cancel
  ((nat.le_succ _).trans a_add_one_le_four_pow_size), mul_comm]

lemma card_aux₂ {U : finset α} (hUcard : U.card = m * 4^P.size + a) :
  (4^P.size - a) * m + a * (m + 1) = U.card :=
by rw [hUcard, mul_add, mul_one, ←add_assoc, ←add_mul, nat.sub_add_cancel
  ((nat.le_succ _).trans a_add_one_le_four_pow_size), mul_comm]

lemma card_aux₃ (hP : P.is_equipartition) {U : finset α} (hU : U ∈ P.parts)
  (hUcard : ¬U.card = m * 4^P.size + a) :
  (4^P.size - (a + 1)) * m + (a + 1) * (m + 1) = U.card :=
begin
  have aux :
    m * 4^finpartition_on.size P + a = card α/P.size,
  { apply add_sub_cancel_of_le,
    rw [exp_bound, ←nat.div_div_eq_div_mul],
    exact nat.div_mul_le_self _ _ },
  rw aux at hUcard,
  rw finpartition.is_equipartition_iff_card_parts_eq_average at hP,
  rw [(hP U hU).resolve_left hUcard, mul_add, mul_one, ←add_assoc, ←add_mul, nat.sub_add_cancel
    a_add_one_le_four_pow_size, ←add_assoc, mul_comm, add_sub_cancel_of_le, ←aux],
  rw ←aux,
  exact nat.le_add_right _ _,
end
