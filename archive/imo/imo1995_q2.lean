/-
Copyright (c) 2022 Mantas Bakšys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys
-/

import algebra.order.rearrangement
import data.real.basic
import data.fin.vec_notation
import logic.equiv.fin
import data.fintype.card
import tactic.fin_cases
import tactic.norm_fin
import tactic.ring_exp
import analysis.mean_inequalities
import tactic.linarith

open real

variables {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1)
include ha hb hc habc

lemma preparation : a ≤ b → b ≤ c → 3 / 2 ≤ a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (b + a) :=
begin
  intros hab hbc,
  set f : fin 3 → ℝ := ![a ^ 2, b ^ 2, c ^ 2] with hf,
  set g : fin 3 → ℝ := ![(b + c)⁻¹, (c + a)⁻¹, (b + a)⁻¹] with hg,
  have hfm : monotone f := by sorry,
  have hfg : monotone g := by sorry,
  have h1 := @monovary.sum_smul_comp_perm_le_sum_smul _ _ _ _ _ _ _
    (fin_rotate 3) _ _ _ (hfm.monovary hfg),
  have h2 := @monovary.sum_smul_comp_perm_le_sum_smul _ _ _ _ _ _ _
    ((fin_rotate 3) ^ 2) _ _ _ (hfm.monovary hfg),
  rw [← mul_le_mul_left (show (0 : ℝ) < 2, by norm_num), two_mul, two_mul],
  have h3 := (add_le_add h1 h2),
  simp only [pow_two, fin_rotate_succ_apply, smul_eq_mul, equiv.perm.coe_mul,
    function.comp_app] at h3,
  have huniv : (@finset.univ (fin 3) _) = {0, 1, 2},
  { ext x, fin_cases x; simp },
  rw huniv at *,
  have h4 : ({0, 1, 2} : finset (fin 3)).sum (λ (x : fin 3), f x * g x) =
    a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (b + a),
  { rw [finset.sum_insert _, finset.sum_insert, finset.sum_singleton, hf, hg],
    { field_simp [add_assoc] },
    all_goals { simp, norm_num }},
  rw h4 at h3,
  apply le_trans _ h3,
  iterate 2 { rw [finset.sum_insert _, finset.sum_insert, finset.sum_singleton] },
  { norm_fin,
    field_simp [hf, hg],
    suffices : 3 ≤ (c ^ 2 + a ^ 2) / (c + a) +
      (b ^ 2 + a ^ 2) / (b + a) + (b ^ 2 + c ^ 2) / (b + c),
    { convert this using 1,
      ring_exp_eq },
    calc 3 = 3 * (a ^ (1 / 3 : ℝ) * b ^ (1 / 3 : ℝ) * c ^ (1 / 3 : ℝ)) :
      by { rw [← real.mul_rpow, ← real.mul_rpow, habc, one_rpow]; linarith [mul_pos ha hb] }
    ...  ≤ 3 * (1/ 3 * a + 1 / 3 * b + 1 / 3 * c) :
      by { rw [(mul_le_mul_left (show (0 : ℝ) < 3, by norm_num)), div_eq_mul_inv],
           convert (geom_mean_le_arith_mean3_weighted _ _ _ _ _ _ _) using 1,
           swap 7, iterate 4 { norm_num },
           all_goals { linarith }}
    ... = a + b + c : by field_simp [mul_comm]
    ... = 1 / 2 * ((a + b) ^ 2 / (a + b) + (b + c) ^ 2 / (b + c) + (c + a) ^ 2 / (c + a)) :
      by { field_simp [pow_two, mul_two], abel }
    ... ≤ (a ^ 2 + b ^ 2) / (a + b) + (b ^ 2 + c ^ 2) / (b + c) + (c ^ 2 + a ^ 2) / (c + a) :
      by { simp only [mul_add, ← mul_div_assoc],
           apply add_le_add (add_le_add _ _),
           { rw [div_le_div_right, one_div, inv_mul_le_iff, add_sq, mul_add];
             linarith [two_mul_le_add_sq c a] },
           swap 5,
           { rw [div_le_div_right, one_div, inv_mul_le_iff, add_sq, mul_add];
             linarith [two_mul_le_add_sq a b] },
           swap 5,
           { rw [div_le_div_right, one_div, inv_mul_le_iff, add_sq, mul_add];
             linarith [two_mul_le_add_sq b c] },
           all_goals { apply_instance } }
    ... = (c ^ 2 + a ^ 2) / (c + a) + (b ^ 2 + a ^ 2) / (b + a) + (b ^ 2 + c ^ 2) / (b + c) :
      by { rw [add_comm a b], ring_exp_eq } },
  all_goals { simp, norm_num }
end
