/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import analysis.normed_space.inner_product
import measure_theory.set_integral

/-! # `L^2` space

-/

noncomputable theory
open topological_space measure_theory measure_theory.Lp
open_locale nnreal ennreal

namespace measure_theory

variables {α E F 𝕜 : Type*} [is_R_or_C 𝕜] [measurable_space α] {μ : measure α}
  [measurable_space E] [inner_product_space 𝕜 E] [borel_space E] [second_countable_topology E]
  [normed_group F] [measurable_space F] [borel_space F] [second_countable_topology F]

local notation `⟪`x`, `y`⟫` := @inner 𝕜 E _ x y

lemma two_mul_le_add_sq (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 :=
begin
  suffices h_nonneg : 0 ≤ a ^ 2 + b ^ 2 - 2 * a * b, by rwa sub_nonneg at h_nonneg,
  calc 0 ≤ (a - b) ^ 2               : pow_two_nonneg _
     ... = a ^ 2 + b ^ 2 - 2 * a * b : by ring,
end

lemma snorm_rpow_two_norm_lt_top (f : Lp F 2 μ) : snorm (λ x, ∥f x∥ ^ (2 : ℝ)) 1 μ < ∞ :=
begin
  have h_two : ennreal.of_real (2 : ℝ) = 2, by simp [zero_le_one],
  rw [snorm_norm_rpow f zero_lt_two, one_mul, h_two],
  exact ennreal.rpow_lt_top_of_nonneg zero_le_two (Lp.snorm_ne_top f),
end

lemma snorm_inner_lt_top (f g : Lp E 2 μ) : snorm (λ (x : α), ⟪f x, g x⟫) 1 μ < ∞ :=
begin
  have h : ∀ x, is_R_or_C.abs ⟪f x, g x⟫ ≤ ∥f x∥ * ∥g x∥, from λ x, abs_inner_le_norm _ _,
  have h' : ∀ x, is_R_or_C.abs ⟪f x, g x⟫ ≤ is_R_or_C.abs (∥f x∥^2 + ∥g x∥^2),
  { refine λ x, le_trans (h x) _,
    rw [is_R_or_C.abs_to_real, abs_eq_self.mpr],
    swap, { exact add_nonneg (by simp) (by simp), },
    refine le_trans _ (half_le_self (add_nonneg (pow_two_nonneg _) (pow_two_nonneg _))),
    refine (le_div_iff (@zero_lt_two ℝ _ _)).mpr (le_trans (le_of_eq _) (two_mul_le_add_sq _ _)),
    ring, },
  simp_rw [← is_R_or_C.norm_eq_abs, ← real.rpow_nat_cast] at h',
  refine (snorm_mono_ae (ae_of_all _ h')).trans_lt ((snorm_add_le _ _ le_rfl).trans_lt _),
  { exact (Lp.ae_measurable f).norm.rpow_const, },
  { exact (Lp.ae_measurable g).norm.rpow_const, },
  simp only [nat.cast_bit0, ennreal.add_lt_top, nat.cast_one],
  exact ⟨snorm_rpow_two_norm_lt_top f, snorm_rpow_two_norm_lt_top g⟩,
end

section inner_product_space

variables [measurable_space 𝕜] [borel_space 𝕜]

include 𝕜

instance : has_inner 𝕜 (Lp E 2 μ) := ⟨λ f g, ∫ a, ⟪f a, g a⟫ ∂μ⟩

lemma inner_def (f g : Lp E 2 μ) : inner f g = ∫ a : α, ⟪f a, g a⟫ ∂μ := rfl

lemma integral_inner_eq_sq_snorm (f : Lp E 2 μ) :
  ∫ a, (inner (f a) (f a) : 𝕜) ∂μ = ennreal.to_real ∫⁻ a, (nnnorm (f a) : ℝ≥0∞) ^ (2:ℝ) ∂μ :=
begin
  simp_rw inner_self_eq_norm_sq_to_K,
  norm_cast,
  rw integral_eq_lintegral_of_nonneg_ae,
  swap, { exact filter.eventually_of_forall (λ x, pow_two_nonneg _), },
  swap, { exact (Lp.ae_measurable f).norm.pow, },
  congr,
  ext1 x,
  have h_two : (2 : ℝ) = ((2 : ℕ) : ℝ), by simp,
  rw [← real.rpow_nat_cast _ 2, ← h_two,
    ← ennreal.of_real_rpow_of_nonneg (norm_nonneg _) zero_le_two, of_real_norm_eq_coe_nnnorm],
  norm_cast,
end

private lemma norm_sq_eq_inner' (f : Lp E 2 μ) : ∥f∥ ^ 2 = is_R_or_C.re (inner f f : 𝕜) :=
begin
  have h_two : (2 : ℝ≥0∞).to_real = 2 := by simp,
  rw [inner_def, integral_inner_eq_sq_snorm, norm_def, ← ennreal.to_real_pow, is_R_or_C.of_real_re,
    ennreal.to_real_eq_to_real (ennreal.pow_lt_top (Lp.snorm_lt_top f) 2) _],
  { rw [←ennreal.rpow_nat_cast, snorm_eq_snorm' ennreal.two_ne_zero ennreal.two_ne_top, snorm',
      ← ennreal.rpow_mul, one_div, h_two],
    simp, },
  { refine lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top zero_lt_two _,
    rw [← h_two, ← snorm_eq_snorm' ennreal.two_ne_zero ennreal.two_ne_top],
    exact Lp.snorm_lt_top f, },
end

lemma mem_L1_inner (f g : Lp E 2 μ) :
  ae_eq_fun.mk (λ x, ⟪f x, g x⟫) ((Lp.ae_measurable f).inner (Lp.ae_measurable g)) ∈ Lp 𝕜 1 μ :=
by { simp_rw [mem_Lp_iff_snorm_lt_top, snorm_ae_eq_fun], exact snorm_inner_lt_top f g, }

lemma integrable_inner (f g : Lp E 2 μ) : integrable (λ x : α, ⟪f x, g x⟫) μ :=
(integrable_congr (ae_eq_fun.coe_fn_mk (λ x, ⟪f x, g x⟫)
    ((Lp.ae_measurable f).inner (Lp.ae_measurable g)))).mp
  (ae_eq_fun.integrable_iff_mem_L1.mpr (mem_L1_inner f g))

private lemma add_left' (f f' g : Lp E 2 μ) : (inner (f + f') g : 𝕜) = inner f g + inner f' g :=
begin
  simp_rw [inner_def, ← integral_add (integrable_inner f g) (integrable_inner f' g),
    ←inner_add_left],
  refine integral_congr_ae ((coe_fn_add f f').mono (λ x hx, _)),
  congr,
  rwa pi.add_apply at hx,
end

private lemma smul_left' (f g : Lp E 2 μ) (r : 𝕜) :
  inner (r • f) g = is_R_or_C.conj r * inner f g :=
begin
  rw [inner_def, inner_def, ← smul_eq_mul, ← integral_smul],
  refine integral_congr_ae ((coe_fn_smul r f).mono (λ x hx, _)),
  rw [smul_eq_mul, ← inner_smul_left],
  congr,
  rwa pi.smul_apply at hx,
end

instance : inner_product_space 𝕜 (Lp E 2 μ) :=
{ norm_sq_eq_inner := norm_sq_eq_inner',
  conj_sym := λ _ _, by simp_rw [inner_def, ← integral_conj, inner_conj_sym],
  add_left := add_left',
  smul_left := smul_left', }

end inner_product_space

end measure_theory
