/-
Copyright (c) 2019 Chris Hughes All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import analysis.special_functions.pow
import field_theory.is_alg_closed.basic
import topology.algebra.polynomial

/-!
# The fundamental theorem of algebra

This file proves that every nonconstant complex polynomial has a root.

As a consequence, the complex numbers are algebraically closed.
-/

open complex polynomial metric filter set
open_locale polynomial topological_space

namespace complex

/- The following proof uses the method given at
<https://ncatlab.org/nlab/show/fundamental+theorem+of+algebra#classical_fta_via_advanced_calculus>
-/
/-- **Fundamental theorem of algebra**: every non constant complex polynomial
  has a root -/
lemma exists_root {f : ℂ[X]} (hf : 0 < degree f) : ∃ z : ℂ, is_root f z :=
begin
  /- Choose a global minimum `z₀` of `∥f z∥`. -/
  refine f.exists_forall_norm_le.imp (λ z₀ hz₀, by_contra $ λ (hf0 : eval z₀ f ≠ 0), _),
  /- Represent `f` as `g * (X - C z₀) ^ k + C a`. -/
  obtain ⟨a, k, g, ha0, hk0, hg0, rfl⟩ :
    ∃ (a : ℂ) (k : ℕ) (g : ℂ[X]), a ≠ 0 ∧ 0 < k ∧ eval z₀ g ≠ 0 ∧ g * (X - C z₀) ^ k + C a = f,
  { set a := f.eval z₀,
    set n := root_multiplicity z₀ (f - C a),
    have hfa : f - C a ≠ 0, from mt sub_eq_zero.1 (λ h, hf.not_le (h.symm ▸ degree_C_le)),
    refine ⟨a, n, (f - C a) /ₘ ((X - C z₀) ^ n), hf0, (root_multiplicity_pos hfa).2 _, _, _⟩,
    { rw [is_root, eval_sub, eval_C, sub_self] },
    { exact eval_div_by_monic_pow_root_multiplicity_ne_zero _ hfa },
    { exact eq_sub_iff_add_eq.1 (div_by_monic_mul_pow_root_multiplicity_eq _ _) } },
  clear hf0 hf,
  /- Choose `k`-th root of $-\frac{a}{g(z_0)}$. -/
  obtain ⟨w, hw⟩ : ∃ w, w ^ k = -a / eval z₀ g, from ⟨_, cpow_nat_inv_pow _ hk0.ne'⟩,
  /- It suffices to show that $∥f(z₀+εw)∥ < ∥f(z₀)∥$ for sufficiently small positive `ε`. We
  substitute `f = g * (X - C z₀) ^ k + C a` and reorder terms in this inequality. -/
  suffices : ∀ᶠ ε : ℝ in 𝓝[>] 0,
    abs (1 - ε ^ k + ε ^ k * ((eval z₀ g - eval (z₀ + ε * w) g) / eval z₀ g)) < 1,
  { rcases this.exists with ⟨ε, hε⟩,
    rw [← mul_lt_mul_left (abs.pos ha0), ← map_mul, mul_one] at hε,
    refine hε.not_le _,
    convert hz₀ (z₀ + ε * w),
    { rw [eval_add, eval_mul, eval_pow, eval_sub, eval_X, eval_C, eval_C, sub_self, zero_pow hk0,
        mul_zero, zero_add] },
    { rw [eval_add, eval_C, eval_mul, eval_pow, eval_sub, eval_X, eval_C, add_sub_cancel', mul_pow,
        hw, sub_div, div_self hg0, div_eq_mul_inv, div_eq_mul_inv],
      ring } },
  /- Since `g` is continuous, the fraction `(eval z₀ g - eval (z₀ + ↑ε * w) g) / eval z₀ g` tends
  to zero as `ε → 0`. -/
  have hg : tendsto (λ ε : ℝ, ∥(eval z₀ g - eval (z₀ + ↑ε * w) g) / eval z₀ g∥) (𝓝 0) (𝓝 0),
  { refine (continuous_const.sub _).div_const.norm.tendsto' _ _ _,
    { exact g.continuous.comp (continuous_const.add $ continuous_of_real.mul continuous_const) },
    { simp } },
  /- Choose `ε ∈ (0, 1)` such that `(eval z₀ g - eval (z₀ + ↑ε * w) g) / eval z₀ g` has norm less
  than one. It is easy to see that $∥f (z₀ + εw)∥ < ∥f(z₀)∥$. -/
  filter_upwards [(hg.eventually $ gt_mem_nhds one_pos).filter_mono nhds_within_le_nhds,
    Ioo_mem_nhds_within_Ioi (left_mem_Ico.2 (zero_lt_one' ℝ))] with ε hgε hε,
  refine (abs.add_le _ _).trans_lt _,
  have hε0 : 0 < ε ^ k, from pow_pos hε.1 k,
  have hε1 : ε ^ k < 1, from pow_lt_one hε.1.le hε.2 hk0.ne',
  rw [← of_real_pow, ← of_real_one, ← of_real_sub, abs_of_real, abs_of_pos (sub_pos.2 hε1),
    sub_add_eq_add_sub, add_sub_assoc, add_lt_iff_neg_left, sub_lt_zero, map_mul, abs_of_real,
    abs_of_pos hε0],
  exact mul_lt_of_lt_one_right hε0 hgε
end

instance is_alg_closed : is_alg_closed ℂ :=
is_alg_closed.of_exists_root _ $ λ p _ hp, complex.exists_root $ degree_pos_of_irreducible hp

end complex
