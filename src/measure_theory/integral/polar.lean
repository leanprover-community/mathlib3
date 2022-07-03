/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import measure_theory.function.jacobian
import measure_theory.integral.exp_decay
import analysis.special_functions.gamma

/-!
# Changing variables in integrals through polar coordinates

-/

noncomputable theory

open real set measure_theory
open_locale real topological_space


/-- The polar coordinates local homeomorphism in `ℝ^2`, mapping `(r cos θ, r sin θ)` to `(r, θ)`.
It is a homeomorphism between `ℝ^2 - (-∞, 0]` and `(0, +∞) × (-π, π)`. -/
@[simps] def polar_coord : local_homeomorph (ℝ × ℝ) (ℝ × ℝ) :=
{ to_fun := λ q, (real.sqrt (q.1^2 + q.2^2), complex.arg (complex.equiv_real_prod.symm q)),
  inv_fun := λ p, (p.1 * cos p.2, p.1 * sin p.2),
  source := {q | 0 < q.1} ∪ {q | q.2 ≠ 0},
  target := Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
  map_target' :=
  begin
    rintros ⟨r, θ⟩ ⟨hr, hθ⟩,
    dsimp at hr hθ,
    rcases eq_or_ne θ 0 with rfl|h'θ,
    { simpa using hr },
    { right,
      simpa only [ne_of_gt hr, ne.def, mem_set_of_eq, mul_eq_zero, false_or,
        sin_eq_zero_iff_of_lt_of_lt hθ.1 hθ.2] using h'θ }
  end,
  map_source' :=
  begin
    rintros ⟨x, y⟩ hxy,
    simp only [prod_mk_mem_set_prod_eq, mem_Ioi, sqrt_pos, mem_Ioo, complex.neg_pi_lt_arg,
      true_and, complex.arg_lt_pi_iff],
    split,
    { cases hxy,
      { dsimp at hxy, linarith [sq_pos_of_ne_zero _ (hxy.ne'), sq_nonneg y] },
      { linarith [sq_nonneg x, sq_pos_of_ne_zero _ hxy] } },
    { cases hxy,
      { exact or.inl (le_of_lt hxy) },
      { exact or.inr hxy } }
  end,
  right_inv' :=
  begin
    rintros ⟨r, θ⟩ ⟨hr, hθ⟩,
    dsimp at hr hθ,
    simp only [prod.mk.inj_iff],
    split,
    { conv_rhs { rw [← sqrt_sq (le_of_lt hr), ← one_mul (r^2), ← sin_sq_add_cos_sq θ], },
      congr' 1,
      ring_exp },
    { convert complex.arg_mul_cos_add_sin_mul_I hr ⟨hθ.1, hθ.2.le⟩,
      simp only [complex.equiv_real_prod_symm_apply, complex.of_real_mul, complex.of_real_cos,
        complex.of_real_sin],
      ring }
  end,
  left_inv' :=
  begin
    rintros ⟨x, y⟩ hxy,
    have A : sqrt (x ^ 2 + y ^ 2) = complex.abs (x + y * complex.I),
      by simp only [complex.abs, complex.norm_sq, pow_two, monoid_with_zero_hom.coe_mk,
        complex.add_re, complex.of_real_re, complex.mul_re, complex.I_re, mul_zero,
        complex.of_real_im, complex.I_im, sub_self, add_zero, complex.add_im,
        complex.mul_im, mul_one, zero_add],
    have Z := complex.abs_mul_cos_add_sin_mul_I (x + y * complex.I),
    simp only [← complex.of_real_cos, ← complex.of_real_sin, mul_add, ← complex.of_real_mul,
      ← mul_assoc] at Z,
    simpa [A, -complex.of_real_cos, -complex.of_real_sin] using complex.ext_iff.1 Z,
  end,
  open_target := is_open_Ioi.prod is_open_Ioo,
  open_source := (is_open_lt continuous_const continuous_fst).union
    (is_open_ne_fun continuous_snd continuous_const),
  continuous_inv_fun := ((continuous_fst.mul (continuous_cos.comp continuous_snd)).prod_mk
    (continuous_fst.mul (continuous_sin.comp continuous_snd))).continuous_on,
  continuous_to_fun :=
  begin
    apply ((continuous_fst.pow 2).add (continuous_snd.pow 2)).sqrt.continuous_on.prod,
    have A : maps_to complex.equiv_real_prod.symm
      ({q : ℝ × ℝ | 0 < q.1} ∪ {q : ℝ × ℝ | q.2 ≠ 0}) {z | 0 < z.re ∨ z.im ≠ 0},
    { rintros ⟨x, y⟩ hxy, simpa only using hxy },
    apply continuous_on.comp (λ z hz, _) _ A,
    { exact (complex.continuous_at_arg hz).continuous_within_at },
    { exact complex.equiv_real_prodₗ.symm.continuous.continuous_on }
  end }

lemma has_fderiv_at_polar_coord_symm (p : ℝ × ℝ) :
  has_fderiv_at polar_coord.symm
    (matrix.to_lin (basis_fin_two_prod ℝ) (basis_fin_two_prod ℝ)
      ![![cos p.2, -p.1 * sin p.2], ![sin p.2, p.1 * cos p.2]]).to_continuous_linear_map p :=
begin
  rw to_lin_prod_continuous_linear_map,
  convert has_fderiv_at.prod
    (has_fderiv_at_fst.mul ((has_deriv_at_cos p.2).comp_has_fderiv_at p has_fderiv_at_snd))
    (has_fderiv_at_fst.mul ((has_deriv_at_sin p.2).comp_has_fderiv_at p has_fderiv_at_snd)) using 2;
  simp only [smul_smul, add_comm, neg_mul, neg_smul, smul_neg],
end

.

lemma polar_coord_source_ae_eq_univ :
  polar_coord.source =ᵐ[volume] univ :=
begin
  have A : polar_coord.sourceᶜ ⊆ (linear_map.snd ℝ ℝ ℝ).ker,
  { assume x hx,
    simp only [polar_coord_source, compl_union, mem_inter_eq, mem_compl_eq, mem_set_of_eq, not_lt,
      not_not] at hx,
    exact hx.2 },
  have B : volume ((linear_map.snd ℝ ℝ ℝ).ker : set (ℝ × ℝ)) = 0,
  { apply measure.add_haar_submodule,
    rw [ne.def, linear_map.ker_eq_top],
    assume h,
    have : (linear_map.snd ℝ ℝ ℝ) (0, 1) = (0 : (ℝ × ℝ →ₗ[ℝ] ℝ)) (0, 1), by rw h,
    simpa using this },
  simp only [ae_eq_univ],
  exact le_antisymm ((measure_mono A).trans (le_of_eq B)) bot_le,
end


theorem integral_comp_polar_coord_symm
  {E : Type*} [normed_group E] [normed_space ℝ E] [complete_space E]
  (f : ℝ × ℝ → E) :
  (∫ p in polar_coord.target, p.1 • f (polar_coord.symm p))
    = ∫ p, f p :=
begin
  set B : (ℝ × ℝ) → ((ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) := λ p,
    (matrix.to_lin (basis_fin_two_prod ℝ) (basis_fin_two_prod ℝ)
      ![![cos p.2, -p.1 * sin p.2], ![sin p.2, p.1 * cos p.2]]).to_continuous_linear_map with hB,
  have A : ∀ p ∈ polar_coord.symm.source, has_fderiv_at polar_coord.symm (B p) p :=
    λ p hp, has_fderiv_at_polar_coord_symm p,
  have B_det : ∀ p, (B p).det = p.1,
  { assume p,
    conv_rhs {rw [← one_mul p.1, ← cos_sq_add_sin_sq p.2] },
    simp only [neg_mul, linear_map.det_to_continuous_linear_map, det_to_lin,
      matrix.det_fin_two_mk, sub_neg_eq_add],
    ring_exp },
  symmetry,
  calc
  ∫ p, f p
      = ∫ p in polar_coord.source, f p :
  begin
    rw ← integral_univ,
    apply set_integral_congr_set_ae,
    exact polar_coord_source_ae_eq_univ.symm
  end
  ... = ∫ p in polar_coord.target, abs ((B p).det) • f (polar_coord.symm p) :
    by apply integral_target_eq_integral_abs_det_fderiv_smul volume A
  ... = ∫ p in polar_coord.target, p.1 • f (polar_coord.symm p) :
  begin
    apply set_integral_congr (polar_coord.open_target.measurable_set) (λ x hx, _),
    rw [B_det, abs_of_pos],
    exact hx.1,
  end
end

open filter asymptotics

lemma exp_neg_mul_sq_is_o_exp_neg {b : ℝ} (hb : 0 < b) :
  (λ x:ℝ, exp (-b * x^2)) =o[at_top] (λ x:ℝ, exp (-x)) :=
begin
  refine is_o_of_tendsto (λ x hx, _) _,
  { exfalso, exact (exp_pos (-x)).ne' hx },
  have : (λ (x:ℝ), exp (-b * x^2) / exp (-x)) = (λ (x:ℝ), exp (x * (1 - b * x))),
  { ext1 x, field_simp [exp_ne_zero, real.exp_neg, ← real.exp_add], ring_exp },
  rw this,
  apply tendsto_exp_at_bot.comp,
  apply tendsto.at_top_mul_at_bot tendsto_id,
  apply tendsto_at_bot_add_const_left at_top (1 : ℝ),
  apply tendsto_neg_at_top_at_bot.comp,
  exact tendsto.const_mul_at_top hb tendsto_id,
end

lemma rpow_mul_exp_neg_mul_sq_is_o_exp_neg {b : ℝ} (hb : 0 < b) (s : ℝ) :
  (λ x:ℝ, x ^ s * exp (-b * x^2)) =o[at_top] (λ x:ℝ, exp (-(1/2) * x)) :=
begin
  apply ((is_O_refl (λ x:ℝ, x ^ s) at_top).mul_is_o (exp_neg_mul_sq_is_o_exp_neg hb)).trans,
  convert Gamma_integrand_is_o s,
  simp_rw [mul_comm],
end

lemma abs_rpow_neg_le_rpow {x : ℝ} (hx : 0 ≤ x) (s : ℝ) : |(-x) ^ s| ≤ x ^ s :=
begin
  rcases eq_or_lt_of_le hx with hx|hx,
  { rcases eq_or_ne s 0 with rfl|hs,
    { simp [← hx] },
    { simp [← hx, zero_rpow hs] } },
  rw [rpow_def_of_pos hx, rpow_def_of_neg (neg_lt_zero.mpr hx), abs_mul,
    abs_of_nonneg (exp_pos _).le, log_neg_eq_log],
  exact mul_le_of_le_one_right (exp_pos _).le (abs_cos_le_one _)
end

lemma integrable_on_rpow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : -1 < s) :
  integrable_on (λ x:ℝ, x ^ s * exp (-b * x^2)) (Ioi 0) :=
begin
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1), integrable_on_union],
  split,
  { rw [←integrable_on_Icc_iff_integrable_on_Ioc],
    refine integrable_on.mul_continuous_on _ _ is_compact_Icc,
    { refine (interval_integrable_iff_integrable_Icc_of_le zero_le_one).mp _,
      exact interval_integral.interval_integrable_rpow' hs },
    { exact (continuous_exp.comp (continuous_const.mul (continuous_pow 2))).continuous_on } },
  { have B : (0 : ℝ) < 1/2, by norm_num,
    apply integrable_of_is_O_exp_neg B _ (is_o.is_O (rpow_mul_exp_neg_mul_sq_is_o_exp_neg hb _)),
    assume x hx,
    have N : x ≠ 0, { refine (zero_lt_one.trans_le _).ne', exact hx },
    apply ((continuous_at_rpow_const _ _ (or.inl N)).mul _).continuous_within_at,
    exact (continuous_exp.comp (continuous_const.mul (continuous_pow 2))).continuous_at },
end

lemma integrable_rpow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : -1 < s) :
  integrable (λ x:ℝ, x ^ s * exp (-b * x^2)) :=
begin
  rw [← integrable_on_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrable_on_union,
      integrable_on_Ici_iff_integrable_on_Ioi],
  refine ⟨_, integrable_on_rpow_mul_exp_neg_mul_sq hb hs⟩,
  rw ← (measure.measure_preserving_neg (volume : measure ℝ)).integrable_on_comp_preimage
    ((homeomorph.neg ℝ).to_measurable_equiv.measurable_embedding),
  simp only [function.comp, neg_sq, neg_preimage, preimage_neg_Iio, neg_neg, neg_zero],
  apply integrable.mono' (integrable_on_rpow_mul_exp_neg_mul_sq hb hs),
  { apply measurable.ae_strongly_measurable,
    exact (measurable_id'.neg.pow measurable_const).mul
      ((measurable_id'.pow measurable_const).const_mul (-b)).exp },
  { have : measurable_set (Ioi (0 : ℝ)) := measurable_set_Ioi,
    filter_upwards [ae_restrict_mem this] with x hx,
    rw [real.norm_eq_abs, abs_mul, abs_of_nonneg (exp_pos _).le],
    apply mul_le_mul_of_nonneg_right _ (exp_pos _).le,
    exact abs_rpow_neg_le_rpow (le_of_lt hx) _ }
end

lemma integrable_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
  integrable (λ x:ℝ, exp (-b * x^2)) :=
begin
  have A : (-1 : ℝ) < 0, by linarith,
  convert integrable_rpow_mul_exp_neg_mul_sq hb A,
  simp,
end

lemma integrable_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
  integrable (λ x:ℝ, x * exp (-b * x^2)) :=
begin
  have A : (-1 : ℝ) < 1, by linarith,
  convert integrable_rpow_mul_exp_neg_mul_sq hb A,
  simp,
end

lemma integral_mul_exp_neg_sq_div_two : ∫ (r : ℝ) in Ioi 0, r * exp (-r ^ 2 / 2) = 1 :=
begin
  have I : integrable (λ x, x * exp (-x^2 / 2)),
  { have A : (0 : ℝ) < 1/2, by norm_num,
    convert (integrable_mul_exp_neg_mul_sq A),
    ext x,
    simp [div_eq_inv_mul] },
  refine tendsto_nhds_unique
    (interval_integral_tendsto_integral_Ioi _ I.integrable_on filter.tendsto_id) _,
  have A : ∀ x, has_deriv_at (λ x, -exp (-x^2 / 2)) (x * exp (- x^2 / 2)) x,
  { assume x,
    convert (((has_deriv_at_pow 2 x)).neg.div_const 2).exp.neg using 1,
    simp,
    ring },
  have : ∀ (y : ℝ), ∫ x in 0..(id y), x * exp (- x^2 / 2) = (-exp(-y^2 / 2)) - (-exp(-0^2 / 2)) :=
    λ y, interval_integral.integral_eq_sub_of_has_deriv_at (λ x hx, A x) I.interval_integrable,
  simp_rw [this],
  have L : tendsto (λ (i : ℝ), 1 - exp (-i ^ 2 / 2)) at_top (𝓝 (1 - 0)),
  { refine tendsto_const_nhds.sub _,
    apply tendsto_exp_at_bot.comp,
    refine tendsto.at_bot_div_const zero_lt_two _,
    exact tendsto_neg_at_top_at_bot.comp (tendsto_pow_at_top one_le_two) },
  simpa using L,
end

theorem integral_gaussian :
  (∫ x, real.exp (-x^2 / 2)) = sqrt (2 * π) :=
begin
  refine (sq_eq_sq _ (sqrt_nonneg _)).1 _,
  { exact integral_nonneg (λ x, (exp_pos _).le) },
  calc
  (∫ x, real.exp (-x^2 / 2)) ^ 2
      = ∫ p : ℝ × ℝ, real.exp (-p.1 ^ 2 / 2) * real.exp (-p.2 ^ 2 / 2) :
    by { rw [pow_two, ← integral_prod_mul], refl }
  ... = ∫ p : ℝ × ℝ, real.exp (- (p.1 ^ 2 + p.2^2) / 2) :
    by { congr, ext p, simp only [← real.exp_add, neg_add_rev, real.exp_eq_exp], ring }
  ... = ∫ p in polar_coord.target, p.1 * real.exp (- ((p.1 * cos p.2) ^ 2 + (p.1 * sin p.2)^2) / 2) :
    (integral_comp_polar_coord_symm (λ p, real.exp (- (p.1^2 + p.2^2) / 2))).symm
  ... = (∫ r in Ioi (0 : ℝ), r * real.exp (-r^2 / 2)) * (∫ θ in Ioo (-π) π, 1) :
    begin
      rw ← set_integral_prod_mul,
      congr' with p,
      rw mul_one,
      congr,
      conv_rhs { rw [← one_mul (p.1^2), ← sin_sq_add_cos_sq p.2], },
      ring_exp,
    end
  ... = 2 * π :
    begin
      have : 0 ≤ π + π, by linarith [real.pi_pos],
      simp only [integral_const, measure.restrict_apply', measurable_set_Ioo, univ_inter, this,
          sub_neg_eq_add, algebra.id.smul_eq_mul, mul_one, volume_Ioo, two_mul,
          ennreal.to_real_of_real, integral_mul_exp_neg_sq_div_two, one_mul],
    end
  ... = (sqrt (2 * π)) ^ 2 :
    by { rw sq_sqrt, exact mul_nonneg zero_le_two pi_pos.le }
end
