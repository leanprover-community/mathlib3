/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.special_functions.pow
import order.partition.equipartition

/-!
# Numerical bounds for Szemerédi Regularity Lemma

This file gathers the numerical facts required by the proof of Szemerédi's regularity lemma.

## Main declarations

* `szemeredi_regularity.step_bound`: During the inductive step, a partition of size `n` is blown to
  size at most `step_bound n`.
* `szemeredi_regularity.initial_bound`: The size of the partition we start the induction with.
* `szemeredi_regularity.bound`: The upper bound on the size of the partition produced by our version
  of Szemerédi's regularity lemma.
-/

open finset fintype function real

namespace szemeredi_regularity

/-- Auxiliary function for Szemerédi's regularity lemma. Blowing up a partition of size `n` during
the induction results in a partition of size at most `step_bound n`. -/
def step_bound (n : ℕ) : ℕ := n * 4 ^ n

lemma le_step_bound : id ≤ step_bound := λ n, nat.le_mul_of_pos_right $ pow_pos (by norm_num) n

lemma step_bound_mono : monotone step_bound :=
λ a b h, nat.mul_le_mul h $ nat.pow_le_pow_of_le_right (by norm_num) h

lemma step_bound_pos_iff {n : ℕ} : 0 < step_bound n ↔ 0 < n :=
zero_lt_mul_right $ pow_pos (by norm_num) _

alias step_bound_pos_iff ↔ _ step_bound_pos

variables {α : Type*} [decidable_eq α] [fintype α] {P : finpartition (univ : finset α)}
  {u : finset α} {ε : ℝ}

local notation `m` := (card α/step_bound P.parts.card : ℕ)
local notation `a` := (card α/P.parts.card - m * 4^P.parts.card : ℕ)

lemma m_pos [nonempty α] (hPα : P.parts.card * 16^P.parts.card ≤ card α) : 0 < m :=
nat.div_pos ((nat.mul_le_mul_left _ $ nat.pow_le_pow_of_le_left (by norm_num) _).trans hPα) $
  step_bound_pos (P.parts_nonempty $ univ_nonempty.ne_empty).card_pos

lemma m_coe_pos [nonempty α] (hPα : P.parts.card * 16^P.parts.card ≤ card α) : (0 : ℝ) < m :=
nat.cast_pos.2 $ m_pos hPα

lemma coe_m_add_one_pos : 0 < (m : ℝ) + 1 := nat.cast_add_one_pos _

lemma one_le_m_coe [nonempty α] (hPα : P.parts.card * 16^P.parts.card ≤ card α) : (1 : ℝ) ≤ m :=
nat.one_le_cast.2 $ m_pos hPα

lemma eps_pow_five_pos (hPε : 100 ≤ 4^P.parts.card * ε^5) : 0 < ε^5 :=
pos_of_mul_pos_right ((by norm_num : (0 : ℝ) < 100).trans_le hPε) $ pow_nonneg (by norm_num) _

lemma eps_pos (hPε : 100 ≤ 4^P.parts.card * ε^5) : 0 < ε :=
pow_bit1_pos_iff.1 $ eps_pow_five_pos hPε

lemma four_pow_pos {n : ℕ} : 0 < (4 : ℝ)^n := pow_pos (by norm_num) n

lemma hundred_div_ε_pow_five_le_m [nonempty α] (hPα : P.parts.card * 16^P.parts.card ≤ card α)
  (hPε : 100 ≤ 4^P.parts.card * ε^5) :
  100 / ε^5 ≤ m :=
(div_le_of_nonneg_of_le_mul (eps_pow_five_pos hPε).le four_pow_pos.le hPε).trans
begin
  norm_cast,
  rwa [nat.le_div_iff_mul_le'(step_bound_pos (P.parts_nonempty $ univ_nonempty.ne_empty).card_pos),
    step_bound, mul_left_comm, ←mul_pow],
end

lemma hundred_le_m [nonempty α] (hPα : P.parts.card * 16^P.parts.card ≤ card α)
  (hPε : 100 ≤ 4^P.parts.card * ε^5) (hε : ε ≤ 1) : 100 ≤ m :=
by exact_mod_cast
  (le_div_self (by norm_num) (eps_pow_five_pos hPε) $ pow_le_one _ (eps_pos hPε).le hε).trans
    (hundred_div_ε_pow_five_le_m hPα hPε)

lemma a_add_one_le_four_pow_parts_card : a + 1 ≤ 4^P.parts.card :=
begin
  have h : 1 ≤ 4^P.parts.card := one_le_pow_of_one_le (by norm_num) _,
  rw [step_bound, ←nat.div_div_eq_div_mul, ←nat.le_sub_iff_right h, tsub_le_iff_left,
    ←nat.add_sub_assoc h],
  exact nat.le_pred_of_lt (nat.lt_div_mul_add h),
end

lemma card_aux₁ (hucard : u.card = m * 4^P.parts.card + a) :
  (4^P.parts.card - a) * m + a * (m + 1) = u.card :=
by rw [hucard, mul_add, mul_one, ←add_assoc, ←add_mul, nat.sub_add_cancel
  ((nat.le_succ _).trans a_add_one_le_four_pow_parts_card), mul_comm]

lemma card_aux₂ (hP : P.is_equipartition) (hu : u ∈ P.parts)
  (hucard : ¬u.card = m * 4^P.parts.card + a) :
  (4^P.parts.card - (a + 1)) * m + (a + 1) * (m + 1) = u.card :=
begin
  have : m * 4 ^ P.parts.card ≤ card α / P.parts.card,
  { rw [step_bound, ←nat.div_div_eq_div_mul],
    exact nat.div_mul_le_self _ _ },
  rw nat.add_sub_of_le this at hucard,
  rw [(hP.card_parts_eq_average hu).resolve_left hucard, mul_add, mul_one, ←add_assoc, ←add_mul,
    nat.sub_add_cancel a_add_one_le_four_pow_parts_card, ←add_assoc, mul_comm,
    nat.add_sub_of_le this, card_univ],
end

lemma pow_mul_m_le_card_part (hP : P.is_equipartition) (hu : u ∈ P.parts) :
  (4 : ℝ) ^ P.parts.card * m ≤ u.card :=
begin
  norm_cast,
  rw [step_bound, ←nat.div_div_eq_div_mul],
  exact (nat.mul_div_le _ _).trans (hP.average_le_card_part hu),
end

variables (P ε) (l : ℕ)

/-- Auxiliary function for Szemerédi's regularity lemma. The size of the partition by which we start
blowing. -/
noncomputable def initial_bound : ℕ := max 7 $ max l $ ⌊log (100 / ε^5) / log 4⌋₊ + 1

lemma le_initial_bound : l ≤ initial_bound ε l := (le_max_left _ _).trans $ le_max_right _ _
lemma seven_le_initial_bound : 7 ≤ initial_bound ε l := le_max_left _ _
lemma initial_bound_pos : 0 < initial_bound ε l :=
nat.succ_pos'.trans_le $ seven_le_initial_bound _ _

lemma hundred_lt_pow_initial_bound_mul {ε : ℝ} (hε : 0 < ε) (l : ℕ) :
  100 < 4^initial_bound ε l * ε^5 :=
begin
  rw [←rpow_nat_cast 4, ←div_lt_iff (pow_pos hε 5), lt_rpow_iff_log_lt _ zero_lt_four,
    ←div_lt_iff, initial_bound, nat.cast_max, nat.cast_max],
  { push_cast, exact lt_max_of_lt_right (lt_max_of_lt_right $ nat.lt_floor_add_one _) },
  { exact log_pos (by norm_num) },
  { exact div_pos (by norm_num) (pow_pos hε 5) }
end

/-- An explicit bound on the size of the equipartition whose existence is given by Szemerédi's
regularity lemma. -/
noncomputable def bound : ℕ :=
(step_bound^[⌊4 / ε^5⌋₊] $ initial_bound ε l) * 16 ^ (step_bound^[⌊4 / ε^5⌋₊] $ initial_bound ε l)

lemma initial_bound_le_bound : initial_bound ε l ≤ bound ε l :=
(id_le_iterate_of_id_le le_step_bound _ _).trans $ nat.le_mul_of_pos_right $ pow_pos (by norm_num) _

lemma le_bound : l ≤ bound ε l := (le_initial_bound ε l).trans $ initial_bound_le_bound ε l
lemma bound_pos : 0 < bound ε l := (initial_bound_pos ε l).trans_le $ initial_bound_le_bound ε l

end szemeredi_regularity
