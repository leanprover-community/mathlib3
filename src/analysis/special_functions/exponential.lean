/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.normed_space.exponential
import analysis.calculus.fderiv_analytic
import data.complex.exponential
import topology.metric_space.cau_seq_filter

/-!
# Calculus results on exponential in a Banach algebra

In this file, we prove basic properties about the derivative of the exponential map `exp 𝕂`
in a Banach algebra `𝔸` over a field `𝕂`. We keep them separate from the main file
`analysis/normed_space/exponential` in order to minimize dependencies.

## Main results

We prove most result for an arbitrary field `𝕂`, and then specialize to `𝕂 = ℝ` or `𝕂 = ℂ`.

### General case

- `has_strict_fderiv_at_exp_zero_of_radius_pos` : `exp 𝕂` has strict Fréchet-derivative
  `1 : 𝔸 →L[𝕂] 𝔸` at zero, as long as it converges on a neighborhood of zero
  (see also `has_strict_deriv_at_exp_zero_of_radius_pos` for the case `𝔸 = 𝕂`)
- `has_strict_fderiv_at_exp_of_lt_radius` : if `𝕂` has characteristic zero and `𝔸` is commutative,
  then given a point `x` in the disk of convergence, `exp 𝕂` as strict Fréchet-derivative
  `exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸` at x (see also `has_strict_deriv_at_exp_of_lt_radius` for the case
  `𝔸 = 𝕂`)

### `𝕂 = ℝ` or `𝕂 = ℂ`

- `has_strict_fderiv_at_exp_zero` : `exp 𝕂` has strict Fréchet-derivative `1 : 𝔸 →L[𝕂] 𝔸` at zero
  (see also `has_strict_deriv_at_exp_zero` for the case `𝔸 = 𝕂`)
- `has_strict_fderiv_at_exp` : if `𝔸` is commutative, then given any point `x`, `exp 𝕂` as strict
  Fréchet-derivative `exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸` at x (see also `has_strict_deriv_at_exp` for the
  case `𝔸 = 𝕂`)

### Compatibilty with `real.exp` and `complex.exp`

- `complex.exp_eq_exp_ℂ` : `complex.exp = exp ℂ ℂ`
- `real.exp_eq_exp_ℝ` : `real.exp = exp ℝ ℝ`

-/

open filter is_R_or_C continuous_multilinear_map normed_field asymptotics
open_locale nat topology big_operators ennreal

section any_field_any_algebra

variables {𝕂 𝔸 : Type*} [nontrivially_normed_field 𝕂] [normed_ring 𝔸] [normed_algebra 𝕂 𝔸]
  [complete_space 𝔸]

/-- The exponential in a Banach-algebra `𝔸` over a normed field `𝕂` has strict Fréchet-derivative
`1 : 𝔸 →L[𝕂] 𝔸` at zero, as long as it converges on a neighborhood of zero. -/
lemma has_strict_fderiv_at_exp_zero_of_radius_pos (h : 0 < (exp_series 𝕂 𝔸).radius) :
  has_strict_fderiv_at (exp 𝕂) (1 : 𝔸 →L[𝕂] 𝔸) 0 :=
begin
  convert (has_fpower_series_at_exp_zero_of_radius_pos h).has_strict_fderiv_at,
  ext x,
  change x = exp_series 𝕂 𝔸 1 (λ _, x),
  simp [exp_series_apply_eq]
end

/-- The exponential in a Banach-algebra `𝔸` over a normed field `𝕂` has Fréchet-derivative
`1 : 𝔸 →L[𝕂] 𝔸` at zero, as long as it converges on a neighborhood of zero. -/
lemma has_fderiv_at_exp_zero_of_radius_pos (h : 0 < (exp_series 𝕂 𝔸).radius) :
  has_fderiv_at (exp 𝕂) (1 : 𝔸 →L[𝕂] 𝔸) 0 :=
(has_strict_fderiv_at_exp_zero_of_radius_pos h).has_fderiv_at

end any_field_any_algebra

section any_field_comm_algebra

variables {𝕂 𝔸 : Type*} [nontrivially_normed_field 𝕂] [normed_comm_ring 𝔸] [normed_algebra 𝕂 𝔸]
  [complete_space 𝔸]

/-- The exponential map in a commutative Banach-algebra `𝔸` over a normed field `𝕂` of
characteristic zero has Fréchet-derivative `exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸` at any point `x` in the
disk of convergence. -/
lemma has_fderiv_at_exp_of_mem_ball [char_zero 𝕂] {x : 𝔸}
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  has_fderiv_at (exp 𝕂) (exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸) x :=
begin
  have hpos : 0 < (exp_series 𝕂 𝔸).radius := (zero_le _).trans_lt hx,
  rw has_fderiv_at_iff_is_o_nhds_zero,
  suffices : (λ h, exp 𝕂 x * (exp 𝕂 (0 + h) - exp 𝕂 0 - continuous_linear_map.id 𝕂 𝔸 h))
    =ᶠ[𝓝 0] (λ h, exp 𝕂 (x + h) - exp 𝕂 x - exp 𝕂 x • continuous_linear_map.id 𝕂 𝔸 h),
  { refine (is_o.const_mul_left _ _).congr' this (eventually_eq.refl _ _),
    rw ← has_fderiv_at_iff_is_o_nhds_zero,
    exact has_fderiv_at_exp_zero_of_radius_pos hpos },
  have : ∀ᶠ h in 𝓝 (0 : 𝔸), h ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius :=
    emetric.ball_mem_nhds _ hpos,
  filter_upwards [this] with _ hh,
  rw [exp_add_of_mem_ball hx hh, exp_zero, zero_add, continuous_linear_map.id_apply, smul_eq_mul],
  ring
end

/-- The exponential map in a commutative Banach-algebra `𝔸` over a normed field `𝕂` of
characteristic zero has strict Fréchet-derivative `exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸` at any point `x` in
the disk of convergence. -/
lemma has_strict_fderiv_at_exp_of_mem_ball [char_zero 𝕂] {x : 𝔸}
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  has_strict_fderiv_at (exp 𝕂) (exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸) x :=
let ⟨p, hp⟩ := analytic_at_exp_of_mem_ball x hx in
hp.has_fderiv_at.unique (has_fderiv_at_exp_of_mem_ball hx) ▸ hp.has_strict_fderiv_at

end any_field_comm_algebra

section deriv

variables {𝕂 : Type*} [nontrivially_normed_field 𝕂] [complete_space 𝕂]

/-- The exponential map in a complete normed field `𝕂` of characteristic zero has strict derivative
`exp 𝕂 x` at any point `x` in the disk of convergence. -/
lemma has_strict_deriv_at_exp_of_mem_ball [char_zero 𝕂] {x : 𝕂}
  (hx : x ∈ emetric.ball (0 : 𝕂) (exp_series 𝕂 𝕂).radius) :
  has_strict_deriv_at (exp 𝕂) (exp 𝕂 x) x :=
by simpa using (has_strict_fderiv_at_exp_of_mem_ball hx).has_strict_deriv_at

/-- The exponential map in a complete normed field `𝕂` of characteristic zero has derivative
`exp 𝕂 x` at any point `x` in the disk of convergence. -/
lemma has_deriv_at_exp_of_mem_ball [char_zero 𝕂] {x : 𝕂}
  (hx : x ∈ emetric.ball (0 : 𝕂) (exp_series 𝕂 𝕂).radius) :
  has_deriv_at (exp 𝕂) (exp 𝕂 x) x :=
(has_strict_deriv_at_exp_of_mem_ball hx).has_deriv_at

/-- The exponential map in a complete normed field `𝕂` of characteristic zero has strict derivative
`1` at zero, as long as it converges on a neighborhood of zero. -/
lemma has_strict_deriv_at_exp_zero_of_radius_pos (h : 0 < (exp_series 𝕂 𝕂).radius) :
  has_strict_deriv_at (exp 𝕂) (1 : 𝕂) 0 :=
(has_strict_fderiv_at_exp_zero_of_radius_pos h).has_strict_deriv_at

/-- The exponential map in a complete normed field `𝕂` of characteristic zero has derivative
`1` at zero, as long as it converges on a neighborhood of zero. -/
lemma has_deriv_at_exp_zero_of_radius_pos (h : 0 < (exp_series 𝕂 𝕂).radius) :
  has_deriv_at (exp 𝕂) (1 : 𝕂) 0 :=
(has_strict_deriv_at_exp_zero_of_radius_pos h).has_deriv_at

end deriv

section is_R_or_C_any_algebra

variables {𝕂 𝔸 : Type*} [is_R_or_C 𝕂] [normed_ring 𝔸] [normed_algebra 𝕂 𝔸]
  [complete_space 𝔸]

/-- The exponential in a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` has strict Fréchet-derivative
`1 : 𝔸 →L[𝕂] 𝔸` at zero. -/
lemma has_strict_fderiv_at_exp_zero :
  has_strict_fderiv_at (exp 𝕂) (1 : 𝔸 →L[𝕂] 𝔸) 0 :=
has_strict_fderiv_at_exp_zero_of_radius_pos (exp_series_radius_pos 𝕂 𝔸)

/-- The exponential in a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` has Fréchet-derivative
`1 : 𝔸 →L[𝕂] 𝔸` at zero. -/
lemma has_fderiv_at_exp_zero :
  has_fderiv_at (exp 𝕂) (1 : 𝔸 →L[𝕂] 𝔸) 0 :=
has_strict_fderiv_at_exp_zero.has_fderiv_at

end is_R_or_C_any_algebra

section is_R_or_C_comm_algebra

variables {𝕂 𝔸 : Type*} [is_R_or_C 𝕂] [normed_comm_ring 𝔸] [normed_algebra 𝕂 𝔸]
  [complete_space 𝔸]

/-- The exponential map in a commutative Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` has strict
Fréchet-derivative `exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸` at any point `x`. -/
lemma has_strict_fderiv_at_exp {x : 𝔸} :
  has_strict_fderiv_at (exp 𝕂) (exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸) x :=
has_strict_fderiv_at_exp_of_mem_ball ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

/-- The exponential map in a commutative Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ` has
Fréchet-derivative `exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸` at any point `x`. -/
lemma has_fderiv_at_exp {x : 𝔸} :
  has_fderiv_at (exp 𝕂) (exp 𝕂 x • 1 : 𝔸 →L[𝕂] 𝔸) x :=
has_strict_fderiv_at_exp.has_fderiv_at

end is_R_or_C_comm_algebra

section deriv_R_or_C

variables {𝕂 : Type*} [is_R_or_C 𝕂]

/-- The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has strict derivative `exp 𝕂 x` at any point
`x`. -/
lemma has_strict_deriv_at_exp {x : 𝕂} : has_strict_deriv_at (exp 𝕂) (exp 𝕂 x) x :=
has_strict_deriv_at_exp_of_mem_ball ((exp_series_radius_eq_top 𝕂 𝕂).symm ▸ edist_lt_top _ _)

/-- The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has derivative `exp 𝕂 x` at any point `x`. -/
lemma has_deriv_at_exp {x : 𝕂} : has_deriv_at (exp 𝕂) (exp 𝕂 x) x :=
has_strict_deriv_at_exp.has_deriv_at

/-- The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has strict derivative `1` at zero. -/
lemma has_strict_deriv_at_exp_zero : has_strict_deriv_at (exp 𝕂) (1 : 𝕂) 0 :=
has_strict_deriv_at_exp_zero_of_radius_pos (exp_series_radius_pos 𝕂 𝕂)

/-- The exponential map in `𝕂 = ℝ` or `𝕂 = ℂ` has derivative `1` at zero. -/
lemma has_deriv_at_exp_zero :
  has_deriv_at (exp 𝕂) (1 : 𝕂) 0 :=
has_strict_deriv_at_exp_zero.has_deriv_at

end deriv_R_or_C

lemma complex.exp_eq_exp_ℂ : complex.exp = exp ℂ :=
begin
  refine funext (λ x, _),
  rw [complex.exp, exp_eq_tsum_div],
  exact tendsto_nhds_unique x.exp'.tendsto_limit
    (exp_series_div_summable ℝ x).has_sum.tendsto_sum_nat
end

lemma real.exp_eq_exp_ℝ : real.exp = exp ℝ :=
by { ext x, exact_mod_cast congr_fun complex.exp_eq_exp_ℂ x }

/-! ### Series expansions of `cos` and `sin` for `ℝ` and `ℂ` -/

/-- The equivalence between `a` and `(a / n, a % n)` for nonzero `n`. -/
@[simps]
def nat.div_mod_equiv (n : ℕ) [ne_zero n] : ℕ ≃ ℕ × fin n :=
{ to_fun := λ a, (a / n, ↑a),
  inv_fun := λ p, p.1 * n + p.2,
  left_inv := λ a, nat.div_add_mod' _ _,
  right_inv := λ p, begin
    refine prod.ext _ (fin.ext $ nat.mul_add_mod_of_lt p.2.is_lt),
    dsimp only,
    rw [add_comm, nat.add_mul_div_right _ _ (ne_zero.pos n), nat.div_eq_zero p.2.is_lt, zero_add],
  end }

section sin_cos

lemma complex.has_sum_cos' (z : ℂ) :
  has_sum (λ n : ℕ, (z * complex.I) ^ (2 * n) / ↑(2 * n)!) (complex.cos z) :=
begin
  rw [complex.cos, complex.exp_eq_exp_ℂ],
  have := ((exp_series_div_has_sum_exp ℂ (z * complex.I)).add
          (exp_series_div_has_sum_exp ℂ (-z * complex.I))).div_const 2,
  replace := ((nat.div_mod_equiv 2)).symm.has_sum_iff.mpr this,
  dsimp [function.comp] at this,
  simp_rw [←mul_comm 2 _] at this,
  refine this.prod_fiberwise (λ k, _),
  dsimp only,
  convert has_sum_fintype (_ : fin 2 → ℂ) using 1,
  rw fin.sum_univ_two,
  simp_rw [fin.coe_zero, fin.coe_one, add_zero, pow_succ', pow_mul,
    mul_pow, neg_sq, ←two_mul, neg_mul, mul_neg, neg_div, add_right_neg, zero_div, add_zero,
    mul_div_cancel_left _ (two_ne_zero : (2 : ℂ) ≠ 0)],
end

lemma complex.has_sum_sin' (z : ℂ) :
  has_sum (λ n : ℕ, (z * complex.I) ^ (2 * n + 1) / ↑(2 * n + 1)! / complex.I) (complex.sin z) :=
begin
  rw [complex.sin, complex.exp_eq_exp_ℂ],
  have := (((exp_series_div_has_sum_exp ℂ (-z * complex.I)).sub
          (exp_series_div_has_sum_exp ℂ (z * complex.I))).mul_right complex.I).div_const 2,
  replace := ((nat.div_mod_equiv 2)).symm.has_sum_iff.mpr this,
  dsimp [function.comp] at this,
  simp_rw [←mul_comm 2 _] at this,
  refine this.prod_fiberwise (λ k, _),
  dsimp only,
  convert has_sum_fintype (_ : fin 2 → ℂ) using 1,
  rw fin.sum_univ_two,
  simp_rw [fin.coe_zero, fin.coe_one, add_zero, pow_succ', pow_mul,
    mul_pow, neg_sq, sub_self, zero_mul, zero_div, zero_add,
    neg_mul, mul_neg, neg_div, ← neg_add', ←two_mul, neg_mul, neg_div, mul_assoc,
    mul_div_cancel_left _ (two_ne_zero : (2 : ℂ) ≠ 0), complex.div_I],
end

lemma complex.has_sum_cos (z : ℂ) :
  has_sum (λ n : ℕ, ((-1) ^ n) * z ^ (2 * n) / ↑(2 * n)!) (complex.cos z) :=
begin
  convert complex.has_sum_cos' z using 1,
  simp_rw [mul_pow, pow_mul, complex.I_sq, mul_comm]
end

lemma complex.has_sum_sin (z : ℂ) :
  has_sum (λ n : ℕ, ((-1) ^ n) * z ^ (2 * n + 1) / ↑(2 * n + 1)!) (complex.sin z) :=
begin
  convert complex.has_sum_sin' z using 1,
  simp_rw [mul_pow, pow_succ', pow_mul, complex.I_sq, ←mul_assoc,
    mul_div_assoc, div_right_comm, div_self complex.I_ne_zero, mul_comm _ ((-1 : ℂ)^_), mul_one_div,
    mul_div_assoc, mul_assoc]
end

lemma complex.cos_eq_tsum' (z : ℂ) :
  complex.cos z = ∑' n : ℕ, (z * complex.I) ^ (2 * n) / ↑(2 * n)! :=
(complex.has_sum_cos' z).tsum_eq.symm

lemma complex.sin_eq_tsum' (z : ℂ) :
  complex.sin z = ∑' n : ℕ, (z * complex.I) ^ (2 * n + 1) / ↑(2 * n + 1)! / complex.I :=
(complex.has_sum_sin' z).tsum_eq.symm

lemma complex.cos_eq_tsum (z : ℂ) :
  complex.cos z = ∑' n : ℕ, ((-1) ^ n) * z ^ (2 * n) / ↑(2 * n)! :=
(complex.has_sum_cos z).tsum_eq.symm

lemma complex.sin_eq_tsum (z : ℂ) :
  complex.sin z = ∑' n : ℕ, ((-1) ^ n) * z ^ (2 * n + 1) / ↑(2 * n + 1)! :=
(complex.has_sum_sin z).tsum_eq.symm

lemma real.has_sum_cos (r : ℝ) :
  has_sum (λ n : ℕ, ((-1) ^ n) * r ^ (2 * n) / ↑(2 * n)!) (real.cos r) :=
by exact_mod_cast complex.has_sum_cos r

lemma real.has_sum_sin (r : ℝ) :
  has_sum (λ n : ℕ, ((-1) ^ n) * r ^ (2 * n + 1) / ↑(2 * n + 1)!) (real.sin r) :=
by exact_mod_cast complex.has_sum_sin r

lemma real.cos_eq_tsum (r : ℝ) :
  real.cos r = ∑' n : ℕ, ((-1) ^ n) * r ^ (2 * n) / ↑(2 * n)! :=
(real.has_sum_cos r).tsum_eq.symm

lemma real.sin_eq_tsum (r : ℝ) :
  real.sin r = ∑' n : ℕ, ((-1) ^ n) * r ^ (2 * n + 1) / ↑(2 * n + 1)! :=
(real.has_sum_sin r).tsum_eq.symm

end sin_cos
