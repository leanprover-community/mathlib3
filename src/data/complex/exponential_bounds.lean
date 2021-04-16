/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Joseph Myers
-/

import data.complex.exponential
/-!
# Bounds on specific values of the exponential
-/
namespace real

local notation `abs'` := _root_.abs
open is_absolute_value finset cau_seq complex

lemma exp_one_near_10 : abs' (exp 1 - 2244083/825552) ≤ 1/10^10 :=
begin
  apply exp_approx_start,
  iterate 13 { refine exp_1_approx_succ_eq (by norm_num1; refl) (by norm_cast; refl) _ },
  norm_num1,
  refine exp_approx_end' _ (by norm_num1; refl) _ (by norm_cast; refl) (by simp) _,
  rw [_root_.abs_one, abs_of_pos]; norm_num1,
end

lemma exp_one_near_20 : abs' (exp 1 - 363916618873/133877442384) ≤ 1/10^20 :=
begin
  apply exp_approx_start,
  iterate 21 { refine exp_1_approx_succ_eq (by norm_num1; refl) (by norm_cast; refl) _ },
  norm_num1,
  refine exp_approx_end' _ (by norm_num1; refl) _ (by norm_cast; refl) (by simp) _,
  rw [_root_.abs_one, abs_of_pos]; norm_num1,
end

lemma exp_one_gt_271828182 : 2.71828182 < exp 1 :=
lt_of_lt_of_le (by norm_num) (sub_le.1 (abs_sub_le_iff.1 exp_one_near_10).2)

lemma exp_one_lt_271828183 : exp 1 < 2.71828183 :=
lt_of_le_of_lt (sub_le_iff_le_add.1 (abs_sub_le_iff.1 exp_one_near_10).1) (by norm_num)

lemma exp_neg_one_gt_0367879441 : 0.367879441 < exp (-1) :=
begin
  rw [exp_neg, lt_inv _ (exp_pos _)],
  refine lt_of_le_of_lt (sub_le_iff_le_add.1 (abs_sub_le_iff.1 exp_one_near_10).1) _,
  all_goals {norm_num},
end

lemma exp_neg_one_lt_0367879442 : exp (-1) < 0.367879442 :=
begin
  rw [exp_neg, inv_lt (exp_pos _)],
  refine lt_of_lt_of_le _ (sub_le.1 (abs_sub_le_iff.1 exp_one_near_10).2),
  all_goals {norm_num},
end

end real
