/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Joseph Myers
-/

import data.complex.exponential
import analysis.special_functions.log.deriv

/-!
# Bounds on specific values of the exponential

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/
namespace real

open is_absolute_value finset cau_seq complex

lemma exp_one_near_10 : |exp 1 - 2244083/825552| ≤ 1/10^10 :=
begin
  apply exp_approx_start,
  iterate 13 { refine exp_1_approx_succ_eq (by norm_num1; refl) (by norm_cast; refl) _ },
  norm_num1,
  refine exp_approx_end' _ (by norm_num1; refl) _ (by norm_cast; refl) (by simp) _,
  rw [_root_.abs_one, abs_of_pos]; norm_num1,
end

lemma exp_one_near_20 : |exp 1 - 363916618873/133877442384| ≤ 1/10^20 :=
begin
  apply exp_approx_start,
  iterate 21 { refine exp_1_approx_succ_eq (by norm_num1; refl) (by norm_cast; refl) _ },
  norm_num1,
  refine exp_approx_end' _ (by norm_num1; refl) _ (by norm_cast; refl) (by simp) _,
  rw [_root_.abs_one, abs_of_pos]; norm_num1,
end

lemma exp_one_gt_d9 : 2.7182818283 < exp 1 :=
lt_of_lt_of_le (by norm_num) (sub_le_comm.1 (abs_sub_le_iff.1 exp_one_near_10).2)

lemma exp_one_lt_d9 : exp 1 < 2.7182818286 :=
lt_of_le_of_lt (sub_le_iff_le_add.1 (abs_sub_le_iff.1 exp_one_near_10).1) (by norm_num)

lemma exp_neg_one_gt_d9 : 0.36787944116 < exp (-1) :=
begin
  rw [exp_neg, lt_inv _ (exp_pos _)],
  refine lt_of_le_of_lt (sub_le_iff_le_add.1 (abs_sub_le_iff.1 exp_one_near_10).1) _,
  all_goals {norm_num},
end

lemma exp_neg_one_lt_d9 : exp (-1) < 0.36787944120 :=
begin
  rw [exp_neg, inv_lt (exp_pos _)],
  refine lt_of_lt_of_le _ (sub_le_comm.1 (abs_sub_le_iff.1 exp_one_near_10).2),
  all_goals {norm_num},
end

lemma log_two_near_10 : |log 2 - 287209 / 414355| ≤ 1/10^10 :=
begin
  suffices : |log 2 - 287209 / 414355| ≤ 1/17179869184 + (1/10^10 - 1/2^34),
  { norm_num1 at *,
    assumption },
  have t : |(2⁻¹ : ℝ)| = 2⁻¹,
  { rw abs_of_pos, norm_num },
  have z := real.abs_log_sub_add_sum_range_le (show |(2⁻¹ : ℝ)| < 1, by { rw t, norm_num }) 34,
  rw t at z,
  norm_num1 at z,
  rw [one_div (2:ℝ), log_inv, ←sub_eq_add_neg, _root_.abs_sub_comm] at z,
  apply le_trans (_root_.abs_sub_le _ _ _) (add_le_add z _),
  simp_rw [sum_range_succ],
  norm_num,
  rw abs_of_pos;
  norm_num
end

lemma log_two_gt_d9 : 0.6931471803 < log 2 :=
lt_of_lt_of_le (by norm_num1) (sub_le_comm.1 (abs_sub_le_iff.1 log_two_near_10).2)

lemma log_two_lt_d9 : log 2 < 0.6931471808 :=
lt_of_le_of_lt (sub_le_iff_le_add.1 (abs_sub_le_iff.1 log_two_near_10).1) (by norm_num)

end real
