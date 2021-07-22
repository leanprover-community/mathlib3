/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.analytic.basic
import analysis.specific_limits
import data.complex.exponential
import analysis.complex.basic
import topology.metric_space.cau_seq_filter

open filter is_R_or_C continuous_multilinear_map normed_field
open_locale nat topological_space

section exp

lemma real.summable_pow_div_factorial (x : ℝ) : summable (λ n : ℕ, x^n / n!) :=
begin
  by_cases h : x = 0,
  { refine summable_of_norm_bounded_eventually 0 summable_zero _,
    filter_upwards [eventually_cofinite_ne 0],
    intros n hn,
    rw [h, zero_pow' n hn, zero_div, norm_zero],
    exact le_refl _ },
  { refine summable_of_ratio_test_tendsto_lt_one zero_lt_one (eventually_of_forall $
      λ n, div_ne_zero (pow_ne_zero n h) (nat.cast_ne_zero.mpr n.factorial_ne_zero)) _,
    suffices : ∀ n : ℕ, ∥x^(n+1) / (n+1)!∥ / ∥x^n / n!∥ = ∥x∥ / ∥((n+1 : ℕ) : ℝ)∥,
    { conv {congr, funext, rw [this, real.norm_coe_nat] },
      exact (tendsto_const_div_at_top_nhds_0_nat _).comp (tendsto_add_at_top_nat 1) },
    intro n,
    calc ∥x^(n+1) / (n+1)!∥ / ∥x^n / n!∥
        = (∥x∥^n * ∥x∥) * (∥(n! : ℝ)∥⁻¹ * ∥((n+1 : ℕ) : ℝ)∥⁻¹) * ((∥x∥^n)⁻¹ * ∥(n! : ℝ)∥) :
          by rw [ normed_field.norm_div, normed_field.norm_div,
                  normed_field.norm_pow, normed_field.norm_pow, pow_add, pow_one,
                  div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv', inv_inv',
                  nat.factorial_succ, nat.cast_mul, normed_field.norm_mul, mul_inv_rev' ]
    ... = (∥x∥ * ∥((n+1 : ℕ) : ℝ)∥⁻¹) * (∥x∥^n * (∥x∥^n)⁻¹) * (∥(n! : ℝ)∥ * ∥(n! : ℝ)∥⁻¹) :
          by linarith --faster than ac_refl !
    ... = (∥x∥ * ∥((n+1 : ℕ) : ℝ)∥⁻¹) * 1 * 1 :
          by  rw [mul_inv_cancel (pow_ne_zero _ $ λ h', h $ norm_eq_zero.mp h'), mul_inv_cancel
                    (λ h', n.factorial_ne_zero $ nat.cast_eq_zero.mp $ norm_eq_zero.mp h')];
              apply_instance
    ... = ∥x∥ / ∥((n+1 : ℕ) : ℝ)∥ : by rw [mul_one, mul_one, ← div_eq_mul_inv] }
end

variables (𝕂 𝔸 : Type*) [nondiscrete_normed_field 𝕂] [normed_ring 𝔸] [normed_algebra 𝕂 𝔸]

def exp_series : formal_multilinear_series 𝕂 𝔸 𝔸 :=
  λ n, (1/n! : 𝕂) • continuous_multilinear_map.mk_pi_algebra_fin 𝕂 n 𝔸

noncomputable def exp (x : 𝔸) : 𝔸 := (exp_series 𝕂 𝔸).sum x

variables {𝕂 𝔸}

lemma exp_series_apply_eq (x : 𝔸) (n : ℕ) : exp_series 𝕂 𝔸 n (λ _, x) = (1 / n! : 𝕂) • x^n :=
by simp [exp_series]

lemma exp_series_apply_eq' (x : 𝔸) :
  (λ n, exp_series 𝕂 𝔸 n (λ _, x)) = (λ n, (1 / n! : 𝕂) • x^n) :=
funext (exp_series_apply_eq x)

lemma exp_series_apply_eq_field (x : 𝕂) (n : ℕ) : exp_series 𝕂 𝕂 n (λ _, x) = x^n / n! :=
begin
  rw [div_eq_inv_mul, ←smul_eq_mul, inv_eq_one_div],
  exact exp_series_apply_eq x n,
end

lemma exp_series_apply_eq_field' (x : 𝕂) : (λ n, exp_series 𝕂 𝕂 n (λ _, x)) = (λ n, x^n / n!) :=
funext (exp_series_apply_eq_field x)

lemma exp_series_tsum_eq (x : 𝔸) : (exp_series 𝕂 𝔸).sum x = ∑' (n : ℕ), (1 / n! : 𝕂) • x^n :=
tsum_congr (λ n, exp_series_apply_eq x n)

lemma exp_series_tsum_eq_field (x : 𝕂) : (exp_series 𝕂 𝕂).sum x = ∑' (n : ℕ), x^n / n! :=
tsum_congr (λ n, exp_series_apply_eq_field x n)

lemma exp_def : exp 𝕂 𝔸 = (λ x : 𝔸, ∑' (n : ℕ), (1 / n! : 𝕂) • x^n) :=
funext exp_series_tsum_eq

lemma exp_def_field : exp 𝕂 𝕂 = (λ x : 𝕂, ∑' (n : ℕ), x^n / n!) :=
funext exp_series_tsum_eq_field

section analytic

variables [complete_space 𝔸]

lemma exp_has_fpower_series_on_ball_of_radius_pos (h : 0 < (exp_series 𝕂 𝔸).radius) :
  has_fpower_series_on_ball (exp 𝕂 𝔸) (exp_series 𝕂 𝔸) 0 (exp_series 𝕂 𝔸).radius :=
(exp_series 𝕂 𝔸).has_fpower_series_on_ball h

lemma exp_has_fpower_series_at_zero_of_radius_pos (h : 0 < (exp_series 𝕂 𝔸).radius) :
  has_fpower_series_at (exp 𝕂 𝔸) (exp_series 𝕂 𝔸) 0 :=
(exp_has_fpower_series_on_ball_of_radius_pos h).has_fpower_series_at

lemma exp_continuous_on_ball :
  continuous_on (exp 𝕂 𝔸) (emetric.ball 0 (exp_series 𝕂 𝔸).radius) :=
formal_multilinear_series.continuous_on

lemma exp_analytic_at_of_mem_ball (x : 𝔸) (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝕂 𝔸).radius) :
  analytic_at 𝕂 (exp 𝕂 𝔸) x:=
begin
  by_cases h : (exp_series 𝕂 𝔸).radius = 0,
  { rw h at hx, exact (ennreal.not_lt_zero hx).elim },
  { have h := pos_iff_ne_zero.mpr h,
    exact (exp_has_fpower_series_on_ball_of_radius_pos h).analytic_at_of_mem hx }
end

end analytic

end exp

section is_R_or_C

variables {𝕂 𝔸 : Type*} [is_R_or_C 𝕂] [normed_ring 𝔸] [normed_algebra 𝕂 𝔸] [complete_space 𝔸]

lemma exp_series_radius_eq_top : (exp_series 𝕂 𝔸).radius = ⊤ :=
begin
  refine (exp_series 𝕂 𝔸).radius_eq_top_of_summable_norm (λ r, _),
  refine summable_of_norm_bounded_eventually _ (r : ℝ).summable_pow_div_factorial _,
  filter_upwards [eventually_cofinite_ne 0],
  intros n hn,
  rw [norm_mul, norm_norm (exp_series 𝕂 𝔸 n), exp_series, norm_smul, norm_div, norm_one, norm_pow,
      nnreal.norm_eq, norm_eq_abs, abs_cast_nat, mul_comm, ←mul_assoc, ←mul_div_assoc, mul_one],
  have : ∥continuous_multilinear_map.mk_pi_algebra_fin 𝕂 n 𝔸∥ ≤ 1 :=
    norm_mk_pi_algebra_fin_le_of_pos (nat.pos_of_ne_zero hn),
  exact mul_le_of_le_one_right (div_nonneg (pow_nonneg r.coe_nonneg n) n!.cast_nonneg) this
end

lemma exp_series_summable (x : 𝔸) : summable (λ n, exp_series 𝕂 𝔸 n (λ _, x)) :=
begin
  refine formal_multilinear_series.summable (exp_series 𝕂 𝔸) _,
  rw exp_series_radius_eq_top,
  exact edist_lt_top x 0
end

lemma exp_series_summable' (x : 𝔸) : summable (λ n, (1 / n! : 𝕂) • x^n) :=
begin
  rw ← exp_series_apply_eq',
  exact exp_series_summable x
end

lemma exp_series_summable_field (x : 𝕂) : summable (λ n, x^n / n!) :=
begin
  rw ← exp_series_apply_eq_field',
  exact exp_series_summable x
end

lemma exp_series_has_sum_exp (x : 𝔸) : has_sum (λ n, exp_series 𝕂 𝔸 n (λ _, x)) (exp 𝕂 𝔸 x) :=
begin
  refine formal_multilinear_series.has_sum (exp_series 𝕂 𝔸) _,
  rw exp_series_radius_eq_top,
  exact edist_lt_top x 0
end

lemma exp_series_has_sum_exp' (x : 𝔸) : has_sum (λ n, (1 / n! : 𝕂) • x^n) (exp 𝕂 𝔸 x):=
begin
  rw ← exp_series_apply_eq',
  exact exp_series_has_sum_exp x
end

lemma exp_series_has_sum_exp_field (x : 𝕂) : has_sum (λ n, x^n / n!) (exp 𝕂 𝕂 x):=
begin
  rw ← exp_series_apply_eq_field',
  exact exp_series_has_sum_exp x
end

end is_R_or_C

section scalar_tower

variables (𝕂 𝕂' 𝔸 : Type) [nondiscrete_normed_field 𝕂] [nondiscrete_normed_field 𝕂']
  [normed_ring 𝔸] [normed_algebra 𝕂 𝔸] [normed_algebra 𝕂 𝕂'] [normed_algebra 𝕂' 𝔸]
  [is_scalar_tower 𝕂 𝕂' 𝔸] (p : ℕ) [char_p 𝕂 p] [char_p 𝕂' p]

include p

private lemma exp_series_eq_exp_series (n : ℕ) (x : 𝔸) :
  (exp_series 𝕂 𝔸 n (λ _, x)) = (exp_series 𝕂' 𝔸 n (λ _, x)) :=
begin
  rw [exp_series, exp_series,
      smul_apply, mk_pi_algebra_fin_apply, list.of_fn_const, list.prod_repeat,
      smul_apply, mk_pi_algebra_fin_apply, list.of_fn_const, list.prod_repeat,
      ←inv_eq_one_div, ←inv_eq_one_div, ← smul_one_smul 𝕂' (_ : 𝕂) (_ : 𝔸)],
  congr,
  symmetry,
  have key : (n! : 𝕂) = 0 ↔ (n! : 𝕂') = 0,
  { rw [char_p.cast_eq_zero_iff 𝕂' p, char_p.cast_eq_zero_iff 𝕂 p] },
  by_cases h : (n! : 𝕂) = 0,
  { have h' : (n! : 𝕂') = 0 := key.mp h,
    field_simp [h, h'] },
  { have h' : (n! : 𝕂') ≠ 0 := λ hyp, h (key.mpr hyp),
    suffices : (n! : 𝕂) • (n!⁻¹ : 𝕂') = (n! : 𝕂) • ((n!⁻¹ : 𝕂) • 1),
    { apply_fun (λ (x : 𝕂'), (n!⁻¹ : 𝕂) • x) at this,
      rwa [inv_smul_smul' h, inv_smul_smul' h] at this },
    rw [← smul_assoc, ← nsmul_eq_smul_cast, nsmul_eq_smul_cast 𝕂' _ (_ : 𝕂')],
    field_simp [h, h'] }
end

lemma exp_eq_exp_of_field_extension : exp 𝕂 𝔸 = exp 𝕂' 𝔸 :=
begin
  ext,
  rw [exp, exp],
  refine tsum_congr (λ n, _),
  rw exp_series_eq_exp_series 𝕂 𝕂' 𝔸 p n x
end

end scalar_tower

section complex

lemma complex.exp_eq_exp_ℂ_ℂ : complex.exp = exp ℂ ℂ :=
begin
  refine funext (λ x, _),
  rw [complex.exp, exp_def_field],
  exact tendsto_nhds_unique x.exp'.tendsto_limit
    (exp_series_summable_field x).has_sum.tendsto_sum_nat
end

lemma exp_ℝ_ℂ_eq_exp_ℂ_ℂ : exp ℝ ℂ = exp ℂ ℂ :=
exp_eq_exp_of_field_extension _ _ _ 0

end complex

section real

lemma real.exp_eq_exp_ℝ_ℝ : real.exp = exp ℝ ℝ :=
begin
  refine funext (λ x, _),
  rw [real.exp, complex.exp_eq_exp_ℂ_ℂ, ← exp_ℝ_ℂ_eq_exp_ℂ_ℂ, exp_def, exp_def_field,
      ← re_to_complex, ← re_clm_apply, re_clm.map_tsum (exp_series_summable' (x : ℂ))],
  refine tsum_congr (λ n, _),
  rw [re_clm.map_smul, ← complex.of_real_pow, re_clm_apply, re_to_complex, complex.of_real_re,
      smul_eq_mul, one_div, mul_comm, div_eq_mul_inv]
end

end real
