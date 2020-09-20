/-
Copyright (c) 2019 Chris Hughes All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import topology.algebra.polynomial
import analysis.special_functions.pow

/-!
# The fundamental theorem of algebra

This file proves that every nonconstant complex polynomial has a root.
-/

open complex polynomial metric filter is_absolute_value set

namespace complex

lemma exists_forall_abs_polynomial_eval_le (p : polynomial ℂ) :
  ∃ x, ∀ y, (p.eval x).abs ≤ (p.eval y).abs :=
if hp0 : 0 < degree p
then let ⟨r, hr0, hr⟩ := polynomial.tendsto_infinity complex.abs hp0 ((p.eval 0).abs) in
  let ⟨x, hx₁, hx₂⟩ := (proper_space.compact_ball (0:ℂ) r).exists_forall_le
    ⟨0, by simp [le_of_lt hr0]⟩
    (continuous_abs.comp p.continuous_eval).continuous_on in
  ⟨x, λ y, if hy : y.abs ≤ r then hx₂ y $ by simpa [complex.dist_eq] using hy
    else le_trans (hx₂ _ (by simp [le_of_lt hr0])) (le_of_lt (hr y (lt_of_not_ge hy)))⟩
else ⟨p.coeff 0, by rw [eq_C_of_degree_le_zero (le_of_not_gt hp0)]; simp⟩

/- The following proof uses the method given at
  <https://ncatlab.org/nlab/show/fundamental+theorem+of+algebra#classical_fta_via_advanced_calculus> -/
/-- The fundamental theorem of algebra. Every non constant complex polynomial
  has a root -/
lemma exists_root {f : polynomial ℂ} (hf : 0 < degree f) : ∃ z : ℂ, is_root f z :=
let ⟨z₀, hz₀⟩ := exists_forall_abs_polynomial_eval_le f in
exists.intro z₀ $ classical.by_contradiction $ λ hf0,
have hfX : f - C (f.eval z₀) ≠ 0,
  from mt sub_eq_zero.1 (λ h, not_le_of_gt hf (h.symm ▸ degree_C_le)),
let n := root_multiplicity z₀ (f - C (f.eval z₀)) in
let g := (f - C (f.eval z₀)) /ₘ ((X - C z₀) ^ n) in
have hg0 : g.eval z₀ ≠ 0, from eval_div_by_monic_pow_root_multiplicity_ne_zero _ hfX,
have hg : g * (X - C z₀) ^ n = f - C (f.eval z₀),
  from div_by_monic_mul_pow_root_multiplicity_eq _ _,
have hn0 : 0 < n, from nat.pos_of_ne_zero $ λ hn0, by simpa [g, hn0] using hg0,
let ⟨δ', hδ'₁, hδ'₂⟩ := continuous_iff.1 (polynomial.continuous_eval g) z₀
  ((g.eval z₀).abs) (complex.abs_pos.2 hg0) in
let δ := min (min (δ' / 2) 1) (((f.eval z₀).abs / (g.eval z₀).abs) / 2) in
have hf0' : 0 < (f.eval z₀).abs, from complex.abs_pos.2 hf0,
have hfg0 : 0 < abs (eval z₀ f) * (abs (eval z₀ g))⁻¹, from div_pos hf0' (complex.abs_pos.2 hg0),
have hδ0 : 0 < δ, from lt_min (lt_min (half_pos hδ'₁) (by norm_num)) (half_pos hfg0),
have hδ : ∀ z : ℂ, abs (z - z₀) = δ → abs (g.eval z - g.eval z₀) < (g.eval z₀).abs,
  from λ z hz, hδ'₂ z (by rw [complex.dist_eq, hz];
    exact lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _))
      (half_lt_self hδ'₁)),
have hδ1 : δ ≤ 1, from le_trans (min_le_left _ _) (min_le_right _ _),
let F : polynomial ℂ := C (f.eval z₀) + C (g.eval z₀) * (X - C z₀) ^ n in
let z' := (-f.eval z₀ * (g.eval z₀).abs * δ ^ n /
  ((f.eval z₀).abs * g.eval z₀)) ^ (n⁻¹ : ℂ) + z₀ in
have hF₁ : F.eval z' = f.eval z₀ - f.eval z₀ * (g.eval z₀).abs * δ ^ n / (f.eval z₀).abs,
  by simp only [F, cpow_nat_inv_pow _ hn0, div_eq_mul_inv, eval_pow, mul_assoc, mul_comm (g.eval z₀),
      mul_left_comm (g.eval z₀), mul_left_comm (g.eval z₀)⁻¹, mul_inv', inv_mul_cancel hg0,
      eval_C, eval_add, eval_neg, sub_eq_add_neg, eval_mul, eval_X, add_neg_cancel_right,
      neg_mul_eq_neg_mul_symm, mul_one, div_eq_mul_inv];
    simp only [mul_comm, mul_left_comm, mul_assoc],
have hδs : (g.eval z₀).abs * δ ^ n / (f.eval z₀).abs < 1,
  by rw [div_eq_mul_inv, mul_right_comm, mul_comm, ← @inv_inv' _ _ (complex.abs _ * _),
      mul_inv_rev', inv_inv', ← div_eq_mul_inv, div_lt_iff hfg0, one_mul];
    calc δ ^ n ≤ δ ^ 1 : pow_le_pow_of_le_one (le_of_lt hδ0) hδ1 hn0
      ... = δ : pow_one _
      ... ≤ ((f.eval z₀).abs / (g.eval z₀).abs) / 2 : min_le_right _ _
      ... < _ : half_lt_self hfg0,
have hF₂ : (F.eval z').abs = (f.eval z₀).abs - (g.eval z₀).abs * δ ^ n,
  from calc (F.eval z').abs = (f.eval z₀ - f.eval z₀ * (g.eval z₀).abs
    * δ ^ n / (f.eval z₀).abs).abs : congr_arg abs hF₁
  ... = abs (f.eval z₀) * complex.abs (1 - (g.eval z₀).abs * δ ^ n /
      (f.eval z₀).abs : ℝ) : by rw [← complex.abs_mul];
        exact congr_arg complex.abs
          (by simp [mul_add, add_mul, mul_assoc, div_eq_mul_inv, sub_eq_add_neg])
  ... = _ : by rw [complex.abs_of_nonneg (sub_nonneg.2 (le_of_lt hδs)),
      mul_sub, mul_div_cancel' _ (ne.symm (ne_of_lt hf0')), mul_one],
have hef0 : abs (eval z₀ g) * (eval z₀ f).abs ≠ 0,
  from mul_ne_zero (mt complex.abs_eq_zero.1 hg0) (mt complex.abs_eq_zero.1 hf0),
have hz'z₀ : abs (z' - z₀) = δ,
  by simp [z', mul_assoc, mul_left_comm _ (_ ^ n), mul_comm _ (_ ^ n),
    mul_comm (eval z₀ f).abs, _root_.mul_div_cancel _ hef0, of_real_mul,
    neg_mul_eq_neg_mul_symm, neg_div, is_absolute_value.abv_pow complex.abs,
    complex.abs_of_nonneg (le_of_lt hδ0), real.pow_nat_rpow_nat_inv (le_of_lt hδ0) hn0],
have hF₃ : (f.eval z' - F.eval z').abs < (g.eval z₀).abs * δ ^ n,
  from calc (f.eval z' - F.eval z').abs
      = (g.eval z' - g.eval z₀).abs * (z' - z₀).abs ^ n :
        by rw [← eq_sub_iff_add_eq.1 hg, ← is_absolute_value.abv_pow complex.abs,
            ← complex.abs_mul, sub_mul];
          simp [F, eval_pow, eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_neg, add_sub_cancel,
                sub_eq_add_neg, add_assoc]
  ... = (g.eval z' - g.eval z₀).abs * δ ^ n : by rw hz'z₀
  ... < _ : (mul_lt_mul_right (pow_pos hδ0 _)).2 (hδ _ hz'z₀),
lt_irrefl (f.eval z₀).abs $
  calc (f.eval z₀).abs ≤ (f.eval z').abs : hz₀ _
    ... = (F.eval z' + (f.eval z' - F.eval z')).abs : by simp
    ... ≤ (F.eval z').abs + (f.eval z' - F.eval z').abs : complex.abs_add _ _
    ... < (f.eval z₀).abs - (g.eval z₀).abs * δ ^ n + (g.eval z₀).abs * δ ^ n :
      add_lt_add_of_le_of_lt (by rw hF₂) hF₃
    ... = (f.eval z₀).abs : sub_add_cancel _ _

end complex
