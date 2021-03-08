/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import analysis.normed_space.inner_product
import measure_theory.bochner_integration

/-! # `L^2` space

-/

noncomputable theory
open topological_space measure_theory measure_theory.Lp
open_locale nnreal ennreal

local attribute [instance] fact_one_le_one_ennreal fact_one_le_two_ennreal fact_one_le_top_ennreal

variables {α E F G : Type*} [measurable_space α] {p : ℝ≥0∞} {q : ℝ} {μ : measure α}
  [measurable_space E]
  [normed_group F] [normed_group G]
  [inner_product_space ℝ E] [borel_space E] [second_countable_topology E]

namespace measure_theory

/-- The inner product in L2 is the integral of the inner product of the two functions. -/
def L2_inner (f g : Lp E 2 μ) : ℝ := ∫ a : α, (inner (f a) (g a)) ∂μ

instance : has_inner ℝ (Lp E 2 μ) := {inner := L2_inner }

lemma ennreal.to_real_pow (x : ℝ≥0∞) (n : ℕ) : ennreal.to_real x ^ n = ennreal.to_real (x ^ n) :=
by rw [←ennreal.rpow_nat_cast, ←ennreal.to_real_rpow, real.rpow_nat_cast]

lemma ae_measurable.inner {α} [measurable_space α] {μ : measure α} {f g : α → E}
  (hf : ae_measurable f μ) (hg : ae_measurable g μ) :
  ae_measurable (λ x : α, (inner (f x) (g x) : ℝ)) μ :=
begin
  use (λ x : α, (inner (hf.mk f x) (hg.mk g x) : ℝ)),
  split,
  { exact measurable.inner hf.measurable_mk hg.measurable_mk, },
  refine hf.ae_eq_mk.mp (hg.ae_eq_mk.mono (λ x hxg hxf, _)),
  dsimp only,
  congr,
  { exact hxf, },
  { exact hxg, },
end

lemma integral_inner_eq_sq_snorm (f : Lp E 2 μ) :
  ∫ (a : α), inner (f a) (f a) ∂μ =
    ennreal.to_real ∫⁻ (a : α), (nnnorm (f a) : ennreal) ^ (2:ℝ) ∂μ :=
begin
  rw integral_eq_lintegral_of_nonneg_ae,
  swap, { refine filter.eventually_of_forall (λ x, _),
    simp_rw pi.zero_apply,
    have h_inner : inner (f x) (f x) = ∥ f x ∥ ^ 2,
      by { rw [norm_sq_eq_inner, ←real_inner_eq_re_inner], refl, },
    rw h_inner,
    simp only [norm_nonneg, pow_nonneg], },
  swap, { exact ae_measurable.inner (Lp.ae_measurable f) (Lp.ae_measurable f), },
  congr,
  ext1 x,
  rw [←of_real_norm_eq_coe_nnnorm,
    ennreal.of_real_rpow_of_nonneg_of_pos (norm_nonneg _) zero_lt_two],
  congr,
  have h_two : (2 : ℝ) = ((2 : ℕ) : ℝ), by simp,
  rw [h_two, real.rpow_nat_cast, norm_sq_eq_inner, ←real_inner_eq_re_inner],
  refl,
end

private lemma norm_sq_eq_inner' (f : Lp E 2 μ) : ∥f∥ ^ 2 = L2_inner f f :=
begin
  have h_two : (2 : ℝ≥0∞).to_real = 2 := by simp,
  rw [L2_inner, integral_inner_eq_sq_snorm, norm_def, ennreal.to_real_pow,
    ennreal.to_real_eq_to_real (ennreal.pow_lt_top (Lp.snorm_lt_top f) 2) _],
  swap,
  { refine lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top zero_lt_two _,
    rw [← h_two, ← snorm_eq_snorm' ennreal.two_ne_zero ennreal.two_ne_top],
    exact Lp.snorm_lt_top f, },
  rw [←ennreal.rpow_nat_cast, snorm_eq_snorm' ennreal.two_ne_zero ennreal.two_ne_top, snorm',
    ← ennreal.rpow_mul, one_div, h_two],
  simp,
end

private lemma conj_sym' (f g : Lp E 2 μ) : is_R_or_C.conj (L2_inner f g) = L2_inner g f :=
begin
  simp_rw L2_inner,
  have h : is_R_or_C.conj (∫ (a : α), inner (f a) (g a) ∂μ) = ∫ (a : α), inner (f a) (g a) ∂μ,
    by { rw is_R_or_C.eq_conj_iff_real, simp, },
  rw h,
  congr' 1 with a,
  simp_rw ←inner_conj_sym (f a) (g a),
  rw is_R_or_C.eq_conj_iff_real,
  simp,
end

lemma norm_rpow {x : ℝ} {q : ℝ} (hx_nonneg : 0 ≤ x) : ∥x ^ q∥ = ∥x∥ ^ q :=
begin
  have h_rpow_nonneg : 0 ≤ x ^ q, from real.rpow_nonneg_of_nonneg hx_nonneg _,
  rw [real.norm_eq_abs, real.norm_eq_abs, abs_eq_self.mpr hx_nonneg, abs_eq_self.mpr h_rpow_nonneg],
end

lemma nnnorm_rpow {x : ℝ} {q : ℝ} (hx_nonneg : 0 ≤ x) : nnnorm (x ^ q) = (nnnorm x) ^ q :=
begin
  ext,
  rw [nnreal.coe_rpow, coe_nnnorm, coe_nnnorm],
  exact norm_rpow hx_nonneg,
end

lemma ess_sup_norm_rpow (f : α → E) (q : ℝ) (hq_pos : 0 < q) :
  ess_sup (λ (x : α), (nnnorm (∥f x∥ ^ q) : ℝ≥0∞)) μ = ess_sup (λ (x : α), ↑(nnnorm (f x))) μ ^ q :=
begin
  have h_rpow : ess_sup (λ (x : α), (nnnorm (∥f x∥ ^ q) : ℝ≥0∞)) μ
    = ess_sup (λ (x : α), (↑(nnnorm (f x))) ^ q) μ,
  { congr,
    ext1 x,
    nth_rewrite 1 ← nnnorm_norm,
    rw [ennreal.coe_rpow_of_nonneg _ hq_pos.le, ennreal.coe_eq_coe, nnnorm_rpow (norm_nonneg _)], },
  rw h_rpow,
  have h_rpow_mono := ennreal.rpow_left_strict_mono_of_pos hq_pos,
  have h_rpow_surj := (ennreal.rpow_left_bijective hq_pos.ne.symm).2,
  let iso := h_rpow_mono.order_iso_of_surjective _ h_rpow_surj,
  exact (iso.ess_sup_apply (λ x, ((nnnorm (f x)) : ℝ≥0∞)) μ).symm,
end

lemma snorm_norm_rpow (f : α → E) (q : ℝ) (hq_pos : 0 < q) :
  snorm (λ x, ∥f x∥ ^ q) p μ = (snorm f (p * ennreal.of_real q) μ) ^ q :=
begin
  by_cases h0 : p = 0,
  { simp [h0, ennreal.zero_rpow_of_pos hq_pos], },
  by_cases hp_top : p = ∞,
  { simp only [hp_top, snorm_exponent_top, ennreal.top_mul, hq_pos.not_le, ennreal.of_real_eq_zero,
      if_false, snorm_exponent_top, snorm_ess_sup],
    exact ess_sup_norm_rpow f q hq_pos, },
  rw [snorm_eq_snorm' h0 hp_top, snorm_eq_snorm' _ _],
  swap, { refine mul_ne_zero h0 _, rwa [ne.def, ennreal.of_real_eq_zero, not_le], },
  swap, { exact ennreal.mul_ne_top hp_top ennreal.of_real_ne_top, },
  rw [ennreal.to_real_mul, ennreal.to_real_of_real hq_pos.le],
  exact snorm'_norm_rpow f p.to_real q hq_pos,
end

lemma two_mul_le_add_sq (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 :=
begin
  suffices h_nonneg : 0 ≤ a ^ 2 + b ^ 2 - 2 * a * b, by rwa sub_nonneg at h_nonneg,
  calc 0 ≤ (a - b) ^ 2               : pow_two_nonneg _
     ... = a ^ 2 + b ^ 2 - 2 * a * b : by ring,
end

lemma snorm_rpow_two_norm_lt_top (f : Lp E 2 μ) :
  snorm (λ (x : α), ∥f x∥ ^ (2 : ℝ)) 1 μ < ∞ :=
begin
  have h_two : ennreal.of_real (2 : ℝ) = 2, by simp [zero_le_one],
  rw [snorm_norm_rpow f 2 zero_lt_two, one_mul, h_two],
  exact ennreal.rpow_lt_top_of_nonneg zero_le_two (Lp.snorm_ne_top f),
end

lemma mem_L1_inner {α} [measurable_space α] {μ : measure α} (f g : Lp E 2 μ) :
  ae_eq_fun.mk (λ (x : α), inner (f x) (g x))
    (ae_measurable.inner (Lp.ae_measurable f) (Lp.ae_measurable g)) ∈ Lp ℝ 1 μ :=
begin
  simp_rw [mem_Lp_iff_snorm_lt_top, snorm_ae_eq_fun],
  have h : ∀ x, abs (inner (f x) (g x) : ℝ) ≤ ∥f x∥ * ∥g x∥, from λ x, abs_real_inner_le_norm _ _,
  have h' : ∀ x, abs (inner (f x) (g x) : ℝ) ≤ abs ((λ x, ∥f x∥^2 + ∥g x∥^2) x),
  { refine λ x, le_trans (h x) _,
    rw abs_eq_self.mpr,
    swap, { exact add_nonneg (by simp) (by simp), },
    refine le_trans _ (half_le_self _),
    { rw  le_div_iff _,
      { dsimp only,
        rw [mul_comm _ (2 : ℝ), ← mul_assoc],
        exact two_mul_le_add_sq _ _, },
      { exact zero_lt_two, }, },
    { exact add_nonneg (pow_two_nonneg _) (pow_two_nonneg _), } },
  simp_rw [← real.norm_eq_abs, ← real.rpow_nat_cast] at h',
  refine lt_of_le_of_lt (snorm_mono_ae (ae_of_all _ h')) ((snorm_add_le _ _ le_rfl).trans_lt _),
  { exact ae_measurable.rpow_const (ae_measurable.norm (Lp.ae_measurable f)), },
  { exact ae_measurable.rpow_const (ae_measurable.norm (Lp.ae_measurable g)), },
  have h_two : ((2 : ℕ) : ℝ) = 2, by simp only [nat.cast_bit0, nat.cast_one],
  simp_rw h_two,
  exact ennreal.add_lt_top.mpr ⟨snorm_rpow_two_norm_lt_top f, snorm_rpow_two_norm_lt_top g⟩,
end

lemma integrable_inner {α} [measurable_space α] {μ : measure α} (f g : Lp E 2 μ) :
  ae_eq_fun.integrable (ae_eq_fun.mk (λ x : α, (inner (f x) (g x) : ℝ))
    (ae_measurable.inner (Lp.ae_measurable f) (Lp.ae_measurable g))) :=
ae_eq_fun.integrable_iff_mem_L1.mpr (mem_L1_inner f g)

private lemma add_left' (f f' g : Lp E 2 μ) :
  L2_inner (f + f') g = L2_inner f g + L2_inner f' g :=
begin
  simp_rw L2_inner,
  rw ← integral_add
    ((integrable_congr (ae_eq_fun.coe_fn_mk (λ (x : α), inner (f x) (g x)) _).symm).mpr
      (integrable_inner f g))
    ((integrable_congr (ae_eq_fun.coe_fn_mk (λ (x : α), inner (f' x) (g x)) _).symm).mpr
      (integrable_inner f' g)),
  refine integral_congr_ae _,
  simp_rw ←inner_add_left,
  refine (coe_fn_add f f').mono (λ x hx, _),
  dsimp only,
  congr,
  rwa pi.add_apply at hx,
end

private lemma smul_left' (f g : Lp E 2 μ) (r : ℝ) :
  L2_inner (r • f) g = is_R_or_C.conj r * L2_inner f g :=
begin
  simp_rw L2_inner,
  rw ← integral_mul_left,
  refine integral_congr_ae _,
  simp_rw ←inner_smul_left,
  refine (coe_fn_smul r f).mono (λ x hx, _),
  dsimp only,
  congr,
  rwa pi.smul_apply at hx,
end

instance : inner_product_space ℝ (Lp E 2 μ) :=
{ norm_sq_eq_inner := λ f, by { simp_rw [inner, ← norm_sq_eq_inner' f], refl, },
  conj_sym := λ f g, by { simp_rw inner, exact conj_sym' g f, },
  add_left := add_left',
  smul_left := smul_left', }

end measure_theory
