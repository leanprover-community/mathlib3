/-
Copyright (c) 2022 Tomaz Gomes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes
-/
import data.nat.log
import tactic.linarith
/-!
# lemmas
  This file defines and proves some lemmas about the logarithm function (with base set fixed to 2)
  and other arithmetic relations that will be used to prove merge sort's time complexity.
## Main Results
  - log_pred : ∀ (a : ℕ) , nat.log 2 a - 1 = nat.log 2 (a / 2)
  - log_2_times : ∀ (a : ℕ), 2 * nat.log 2 (a + 2) ≤ a + 2
-/

lemma log_pred : ∀ (a : ℕ) , nat.log 2 a - 1 = nat.log 2 (a / 2)
| 0 := by simp only [nat.log_zero_right, nat.zero_div]
| 1 := by norm_num
| (a + 2) :=
begin
  rw nat.log,
  split_ifs,
  { simp only [nat.add_succ_sub_one, add_zero], },
  simp only [le_refl, not_true, zero_le, nat.one_lt_bit0_iff, and_self, le_add_iff_nonneg_left]
       at h,
  cases h,
end

lemma log_2_val : nat.log 2 2 = 1 :=
begin
  rw nat.log,
  split_ifs,
  { simp only [nat.succ_pos', nat.log_one_right, nat.div_self], },
  simp only [le_refl, not_true, nat.one_lt_bit0_iff, and_self]
       at h,
  cases h,
end

lemma sum_2b (a b : ℕ) : a ≤ 2 * b → a + 2 * b ≤ 4 * b :=
begin
  intro h,
  calc a + 2 * b ≤ 2 * b + 2 * b : by { refine add_le_add h _, exact rfl.ge }
       ...       = 4 * b : by linarith
end

lemma log_2_times : ∀ (a : ℕ), 2 * nat.log 2 (a + 2) ≤ a + 2
| 0       := by { rw log_2_val, norm_num, }
| (a + 1) := have (a + 1) / 2 < a + 1, from nat.div_lt_self' a 0,
begin
  rw nat.log,
  split_ifs,
  { have IH := log_2_times ((a + 1) / 2),
    rw mul_add,
    cases a,
    { norm_num, },
    cases a,
    { norm_num, rw log_2_val, simp, },
    norm_num,
    have add_one :
      2 * nat.log 2 ((a.succ.succ + 1) / 2).succ ≤
      2 * nat.log 2 ((a.succ.succ + 1) / 2 + 2), from
      begin
        refine mul_le_mul le_rfl _ bot_le bot_le,
        refine @nat.log_monotone 2 ((a.succ.succ + 1) / 2).succ (((a.succ.succ + 1) / 2) + 2) _,
        exact nat.le_succ ((a.succ.succ + 1) / 2 + 1),
      end,
    refine le_trans add_one _,
    refine le_trans IH _,
    have succ_succ_two : a.succ.succ + 1 = a + 3 := rfl,
    have two_div_two: ∀ {y}, (y + 2) / 2 = y / 2 + 1 :=
      by { intro, exact (y + 2).div_def 2, },
    have three_eq_one_plus_two : ∀ {y}, y + 3 = y + 1 + 2 :=
      by { intro, exact rfl, },
    rw [ succ_succ_two
       , two_div_two
       , three_eq_one_plus_two
       , ← three_eq_one_plus_two
       ],
    refine add_le_add _ (le_refl 3),
    exact nat.lt_succ_iff.mp (nat.div_lt_self' a 0), },
  exact bot_le,
end

lemma div_two (b a : ℕ) : 2 * a ≤ b → a ≤ b / 2 :=
  by simp_rw [nat.le_div_iff_mul_le _ _ zero_lt_two, mul_comm, imp_self]

