/-
Copyright (c) 2018 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import analysis.special_functions.log
import analysis.special_functions.pow

/-!
# Logarithm Tonality

In this file we describe the tonality of the logarithm function when multiplied by functions of the
form `x ^ a`.

## Tags

logarithm, tonality
-/

open set filter function
open_locale topological_space
noncomputable theory

namespace real
variables {x y : ℝ}


lemma log_mul_self_monotone_on : monotone_on (λ x : ℝ, log x * x) {x | 1 ≤ x} :=
begin
  -- TODO: can be strengthened to exp (-1) ≤ x
  simp only [monotone_on, mem_set_of_eq],
  intros x hex y hey hxy,
  have x_pos : 0 < x := lt_of_lt_of_le zero_lt_one hex,
  have y_pos : 0 < y := lt_of_lt_of_le zero_lt_one hey,
  refine mul_le_mul ((log_le_log x_pos y_pos).mpr hxy) hxy (le_of_lt x_pos) _,
  rwa [le_log_iff_exp_le y_pos, real.exp_zero],
end

lemma log_div_self_antitone_on : antitone_on (λ x : ℝ, log x / x) {x | exp 1 ≤ x} :=
begin
  simp only [antitone_on, mem_set_of_eq],
  intros x hex y hey hxy,
  have x_pos : 0 < x := (exp_pos 1).trans_le hex,
  have y_pos : 0 < y := (exp_pos 1).trans_le hey,
  have hlogx : 1 ≤ log x := by rwa le_log_iff_exp_le x_pos,
  have hyx : 0 ≤ y / x - 1 := by rwa [le_sub_iff_add_le, le_div_iff x_pos, zero_add, one_mul],
  rw [div_le_iff y_pos, ←sub_le_sub_iff_right (log x)],
  calc
    log y - log x = log (y / x)           : by rw [log_div (y_pos.ne') (x_pos.ne')]
    ...           ≤ (y / x) - 1           : log_le_sub_one_of_pos (div_pos y_pos x_pos)
    ...           ≤ log x * (y / x - 1)   : le_mul_of_one_le_left hyx hlogx
    ...           = log x / x * y - log x : by ring,
end

-- This could also be made into an antitone_on statemnt
lemma log_div_self_rpow_antitone_on {x y a : ℝ} (ha : 0 < a) (hex : exp (1 / a) ≤ x) (hxy : x ≤ y) :
  log y / y ^ a ≤ log x / x ^ a :=
begin
  have x_pos : 0 < x := lt_of_lt_of_le (exp_pos (1 / a)) hex,
  have y_pos : 0 < y := by linarith,
  have x_nonneg : 0 ≤ x := le_trans (le_of_lt (exp_pos (1 / a))) hex,
  have y_nonneg : 0 ≤ y := by linarith,
  nth_rewrite 0 ←rpow_one y,
  nth_rewrite 0 ←rpow_one x,
  rw ←div_self (ne_of_lt ha).symm,
  rw div_eq_mul_one_div a a,
  rw rpow_mul y_nonneg,
  rw rpow_mul x_nonneg,
  rw log_rpow (rpow_pos_of_pos y_pos a),
  rw log_rpow (rpow_pos_of_pos x_pos a),
  rw mul_div_assoc,
  rw mul_div_assoc,
  rw mul_le_mul_left (one_div_pos.mpr ha),
  { refine log_div_self_antitone_on _ _ _,
    { simp only [set.mem_set_of_eq],
      convert rpow_le_rpow _ hex (le_of_lt ha),
      rw ←exp_mul,
      simp only [real.exp_eq_exp],
      field_simp [(ne_of_lt ha).symm],
      exact le_of_lt (exp_pos (1 / a)), },
    { simp only [set.mem_set_of_eq],
      convert rpow_le_rpow _ (trans hex hxy) (le_of_lt ha),
      rw ←exp_mul,
      simp only [real.exp_eq_exp],
      field_simp [(ne_of_lt ha).symm],
      exact le_of_lt (exp_pos (1 / a)), },
    apply rpow_le_rpow,
    exact x_nonneg,
    exact hxy,
    exact le_of_lt ha, },
end

-- This could also be made into an antitone_on statemnt
lemma log_div_sqrt_decreasing {x y : ℝ} (hex : exp 2 ≤ x) (hxy : x ≤ y) :
  log y / sqrt y ≤ log x / sqrt x :=
begin
  rw sqrt_eq_rpow,
  rw sqrt_eq_rpow,
  apply log_div_self_rpow_antitone_on,
  norm_num,
  simp only [one_div, inv_inv],
  assumption,
  assumption,
end

end real
