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

lemma preparation : a ≤ b → b ≤ c → 3 / 2 ≤ a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (a + b) :=
begin
  intros hab hbc,
  set f : fin 3 → ℝ := ![a ^ 2, b ^ 2, c ^ 2] with hf,
  set g : fin 3 → ℝ := ![(b + c)⁻¹, (c + a)⁻¹, (b + a)⁻¹] with hg,
  have hfm : monotone f,
  { rw hf,
    intros i j hij,
    fin_cases i;
    fin_cases j,
    swap 4,
    iterate 3 { simp [pow_two], nlinarith },
    iterate 3 { exfalso, apply not_lt.mpr hij, norm_fin }},
  have hfg : monotone g,
  { rw hg,
    intros i j hij,
    fin_cases i;
    fin_cases j,
    swap 4,
    iterate 3 { simp, rw inv_le_inv; nlinarith },
    iterate 3 { exfalso, apply not_lt.mpr hij, norm_fin }},
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
    a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (a + b),
  { rw [finset.sum_insert _, finset.sum_insert, finset.sum_singleton, hf, hg],
    { field_simp [add_assoc, add_comm a b] },
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

lemma IMO_1995_Q2 : 3 / 2 ≤ 1 / (a ^ 3 * (b + c)) + 1 / (b ^ 3 * (c + a)) + 1 / (c ^ 3 * (a + b)) :=
begin
  set x : ℝ := 1 / a with hx,
  have hx0 : 0 < x, simpa [hx, one_div, inv_pos],
  set y : ℝ := 1 / b with hy,
  have hy0 : 0 < y, simpa [hy, one_div, inv_pos],
  set z : ℝ := 1 / c with hz,
  have hz0 : 0 < z, simpa [hz, one_div, inv_pos],
  have hxyz : x * y * z = 1 := by field_simp [habc],
  -- I hoped this change of variables would be easier to prove
  suffices : 3 / 2 ≤ x ^ 2 / (y + z) + y ^ 2 / (z + x) + z ^ 2 / (x + y),
  { convert this using 1,
    rw [← habc, hx, hy, hz],
    field_simp [pow_succ, pow_two, ← mul_assoc],
    have h1 : a * b * c / (a * a * a * (b + c)) = 1 / (a * a * (1 / b + 1 / c)),
    { rw [div_eq_div_iff, one_mul],
      calc a * b * c * (a * a * (1 / b + 1 / c)) = a ^ 3 * (b * c / c + b * c / b) : by ring_exp_eq
      ... = a * a * a * (b + c) :
        by simp only [pow_succ, pow_two, mul_div_cancel b (ne_of_gt hc),
          mul_div_cancel_left c (ne_of_gt hb), ← mul_assoc],
        { norm_num, rintro ⟨_, _⟩; linarith },
        { norm_num [← hy, ← hz], rintro ⟨_, _⟩; linarith }},
    have h2 : a * b * c / (b * b * b * (c + a)) = 1 / (b * b * (1 / c + 1 / a)),
    { rw [div_eq_div_iff, one_mul],
      calc a * b * c * (b * b * (1 / c + 1 / a)) = b ^ 3 * (a * c / a + a * c / c) : by ring_exp_eq
      ... = b * b * b * (c + a) :
        by simp only [pow_succ, pow_two, mul_div_cancel a (ne_of_gt hc),
          mul_div_cancel_left c (ne_of_gt ha), ← mul_assoc],
        { norm_num, rintro ⟨_, _⟩; linarith },
        { norm_num [← hx, ← hz], rintro ⟨_, _⟩; linarith }},
    have h3 : a * b * c / (c * c * c * (a + b)) = 1 / (c * c * (1 / a + 1 / b)),
    { rw [div_eq_div_iff, one_mul],
      calc a * b * c * (c * c * (1 / a + 1 / b)) = c ^ 3 * (a * b / b + a * b / a) : by ring_exp_eq
      ... = c * c * c * (a + b) :
        by simp only [pow_succ, pow_two, mul_div_cancel a (ne_of_gt hb),
          mul_div_cancel_left b (ne_of_gt ha), ← mul_assoc],
        { norm_num, rintro ⟨_, _⟩; linarith },
        { norm_num [← hx, ← hy], rintro ⟨_, _⟩; linarith }},
  rw [h1, h2, h3] },
  -- just a case bash from now on because `wlog` doesn't work well enough
  by_cases hxy : x ≤ y,
  { by_cases hyz : y ≤ z,
    { exact preparation hx0 hy0 hz0 hxyz hxy hyz },
    { by_cases hzx : z ≤ x,
      { convert preparation hz0 hx0 hy0 (show z * x * y = 1, by {rw ← hxyz, ring}) hzx hxy using 1,
        ring },
      { convert preparation hx0 hz0 hy0 (show x * z * y = 1, by {rw ← hxyz, ring})
          (le_of_not_le hzx) (le_of_not_le hyz) using 1,
        ring_exp_eq }}},
  { by_cases hxz : x ≤ z,
    { convert preparation hy0 hx0 hz0 (show y * x * z = 1, by {rw ← hxyz, ring})
        (le_of_not_le hxy) hxz using 1,
      ring_exp_eq },
    { by_cases hyz : y ≤ z,
      { convert preparation hy0 hz0 hx0 (show y * z * x = 1, by {rw ← hxyz, ring}) hyz
          (le_of_not_le hxz) using 1,
        ring_exp_eq },
      { convert preparation hz0 hy0 hx0 (show z * y * x = 1, by {rw ← hxyz, ring})
          (le_of_not_le hyz) (le_of_not_le hxy) using 1,
        ring_exp_eq }}}
end
