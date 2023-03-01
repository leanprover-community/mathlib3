/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import analysis.inner_product_space.basic
import measure_theory.integral.set_integral

/-! # `L^2` space

If `E` is an inner product space over `𝕜` (`ℝ` or `ℂ`), then `Lp E 2 μ` (defined in `lp_space.lean`)
is also an inner product space, with inner product defined as `inner f g = ∫ a, ⟪f a, g a⟫ ∂μ`.

### Main results

* `mem_L1_inner` : for `f` and `g` in `Lp E 2 μ`, the pointwise inner product `λ x, ⟪f x, g x⟫`
  belongs to `Lp 𝕜 1 μ`.
* `integrable_inner` : for `f` and `g` in `Lp E 2 μ`, the pointwise inner product `λ x, ⟪f x, g x⟫`
  is integrable.
* `L2.inner_product_space` : `Lp E 2 μ` is an inner product space.

-/

noncomputable theory
open topological_space measure_theory measure_theory.Lp
open_locale nnreal ennreal measure_theory

namespace measure_theory

section

variables {α F : Type*} {m : measurable_space α} {μ : measure α} [normed_add_comm_group F]

lemma mem_ℒp.integrable_sq {f : α → ℝ} (h : mem_ℒp f 2 μ) :
  integrable (λ x, (f x)^2) μ :=
by simpa [← mem_ℒp_one_iff_integrable]
  using h.norm_rpow two_ne_zero ennreal.two_ne_top

lemma mem_ℒp_two_iff_integrable_sq_norm {f : α → F} (hf : ae_strongly_measurable f μ) :
  mem_ℒp f 2 μ ↔ integrable (λ x, ‖f x‖^2) μ :=
begin
  rw ← mem_ℒp_one_iff_integrable,
  convert (mem_ℒp_norm_rpow_iff hf two_ne_zero ennreal.two_ne_top).symm,
  { simp },
  { rw [div_eq_mul_inv, ennreal.mul_inv_cancel two_ne_zero ennreal.two_ne_top] }
end

lemma mem_ℒp_two_iff_integrable_sq {f : α → ℝ} (hf : ae_strongly_measurable f μ) :
  mem_ℒp f 2 μ ↔ integrable (λ x, (f x)^2) μ :=
begin
  convert mem_ℒp_two_iff_integrable_sq_norm hf,
  ext x,
  simp,
end

end

namespace L2

variables {α E F 𝕜 : Type*} [is_R_or_C 𝕜] [measurable_space α] {μ : measure α}
  [inner_product_space 𝕜 E] [normed_add_comm_group F]


local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

lemma snorm_rpow_two_norm_lt_top (f : Lp F 2 μ) : snorm (λ x, ‖f x‖ ^ (2 : ℝ)) 1 μ < ∞ :=
begin
  have h_two : ennreal.of_real (2 : ℝ) = 2, by simp [zero_le_one],
  rw [snorm_norm_rpow f zero_lt_two, one_mul, h_two],
  exact ennreal.rpow_lt_top_of_nonneg zero_le_two (Lp.snorm_ne_top f),
end

lemma snorm_inner_lt_top (f g : α →₂[μ] E) : snorm (λ (x : α), ⟪f x, g x⟫) 1 μ < ∞ :=
begin
  have h : ∀ x, is_R_or_C.abs ⟪f x, g x⟫ ≤ ‖f x‖ * ‖g x‖, from λ x, abs_inner_le_norm _ _,
  have h' : ∀ x, is_R_or_C.abs ⟪f x, g x⟫ ≤ is_R_or_C.abs (‖f x‖^2 + ‖g x‖^2),
  { refine λ x, le_trans (h x) _,
    rw [is_R_or_C.abs_to_real, abs_eq_self.mpr],
    swap, { exact add_nonneg (by simp) (by simp), },
    refine le_trans _ (half_le_self (add_nonneg (sq_nonneg _) (sq_nonneg _))),
    refine (le_div_iff (zero_lt_two' ℝ)).mpr ((le_of_eq _).trans (two_mul_le_add_sq _ _)),
    ring, },
  simp_rw [← is_R_or_C.norm_eq_abs, ← real.rpow_nat_cast] at h',
  refine (snorm_mono_ae (ae_of_all _ h')).trans_lt ((snorm_add_le _ _ le_rfl).trans_lt _),
  { exact ((Lp.ae_strongly_measurable f).norm.ae_measurable.pow_const _).ae_strongly_measurable },
  { exact ((Lp.ae_strongly_measurable g).norm.ae_measurable.pow_const _).ae_strongly_measurable },
  simp only [nat.cast_bit0, ennreal.add_lt_top, nat.cast_one],
  exact ⟨snorm_rpow_two_norm_lt_top f, snorm_rpow_two_norm_lt_top g⟩,
end

section inner_product_space
open_locale complex_conjugate

include 𝕜

instance : has_inner 𝕜 (α →₂[μ] E) := ⟨λ f g, ∫ a, ⟪f a, g a⟫ ∂μ⟩

lemma inner_def (f g : α →₂[μ] E) : ⟪f, g⟫ = ∫ a : α, ⟪f a, g a⟫ ∂μ := rfl

lemma integral_inner_eq_sq_snorm (f : α →₂[μ] E) :
  ∫ a, ⟪f a, f a⟫ ∂μ = ennreal.to_real ∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ (2:ℝ) ∂μ :=
begin
  simp_rw inner_self_eq_norm_sq_to_K,
  norm_cast,
  rw integral_eq_lintegral_of_nonneg_ae,
  rotate,
  { exact filter.eventually_of_forall (λ x, sq_nonneg _), },
  { exact ((Lp.ae_strongly_measurable f).norm.ae_measurable.pow_const _).ae_strongly_measurable },
  congr,
  ext1 x,
  have h_two : (2 : ℝ) = ((2 : ℕ) : ℝ), by simp,
  rw [← real.rpow_nat_cast _ 2, ← h_two,
    ← ennreal.of_real_rpow_of_nonneg (norm_nonneg _) zero_le_two, of_real_norm_eq_coe_nnnorm],
  norm_cast,
end

private lemma norm_sq_eq_inner' (f : α →₂[μ] E) : ‖f‖ ^ 2 = is_R_or_C.re ⟪f, f⟫ :=
begin
  have h_two : (2 : ℝ≥0∞).to_real = 2 := by simp,
  rw [inner_def, integral_inner_eq_sq_snorm, norm_def, ← ennreal.to_real_pow, is_R_or_C.of_real_re,
    ennreal.to_real_eq_to_real (ennreal.pow_ne_top (Lp.snorm_ne_top f)) _],
  { rw [←ennreal.rpow_nat_cast, snorm_eq_snorm' two_ne_zero ennreal.two_ne_top, snorm',
      ← ennreal.rpow_mul, one_div, h_two],
    simp, },
  { refine (lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top zero_lt_two _).ne,
    rw [← h_two, ← snorm_eq_snorm' two_ne_zero ennreal.two_ne_top],
    exact Lp.snorm_lt_top f, },
end

lemma mem_L1_inner (f g : α →₂[μ] E) :
  ae_eq_fun.mk (λ x, ⟪f x, g x⟫)
    ((Lp.ae_strongly_measurable f).inner (Lp.ae_strongly_measurable g)) ∈ Lp 𝕜 1 μ :=
by { simp_rw [mem_Lp_iff_snorm_lt_top, snorm_ae_eq_fun], exact snorm_inner_lt_top f g, }

lemma integrable_inner (f g : α →₂[μ] E) : integrable (λ x : α, ⟪f x, g x⟫) μ :=
(integrable_congr (ae_eq_fun.coe_fn_mk (λ x, ⟪f x, g x⟫)
    ((Lp.ae_strongly_measurable f).inner (Lp.ae_strongly_measurable g)))).mp
  (ae_eq_fun.integrable_iff_mem_L1.mpr (mem_L1_inner f g))

private lemma add_left' (f f' g : α →₂[μ] E) : ⟪f + f', g⟫ = inner f g + inner f' g :=
begin
  simp_rw [inner_def, ← integral_add (integrable_inner f g) (integrable_inner f' g),
    ←inner_add_left],
  refine integral_congr_ae ((coe_fn_add f f').mono (λ x hx, _)),
  congr,
  rwa pi.add_apply at hx,
end

private lemma smul_left' (f g : α →₂[μ] E) (r : 𝕜) :
  ⟪r • f, g⟫ = conj r * inner f g :=
begin
  rw [inner_def, inner_def, ← smul_eq_mul, ← integral_smul],
  refine integral_congr_ae ((coe_fn_smul r f).mono (λ x hx, _)),
  rw [smul_eq_mul, ← inner_smul_left],
  congr,
  rwa pi.smul_apply at hx,
end

instance inner_product_space : inner_product_space 𝕜 (α →₂[μ] E) :=
{ norm_sq_eq_inner := norm_sq_eq_inner',
  conj_sym := λ _ _, by simp_rw [inner_def, ← integral_conj, inner_conj_sym],
  add_left := add_left',
  smul_left := smul_left', }

end inner_product_space

section indicator_const_Lp

variables (𝕜) {s : set α}

/-- The inner product in `L2` of the indicator of a set `indicator_const_Lp 2 hs hμs c` and `f` is
equal to the integral of the inner product over `s`: `∫ x in s, ⟪c, f x⟫ ∂μ`. -/
lemma inner_indicator_const_Lp_eq_set_integral_inner (f : Lp E 2 μ) (hs : measurable_set s) (c : E)
  (hμs : μ s ≠ ∞) :
  (⟪indicator_const_Lp 2 hs hμs c, f⟫ : 𝕜) = ∫ x in s, ⟪c, f x⟫ ∂μ :=
begin
  rw [inner_def, ← integral_add_compl hs (L2.integrable_inner _ f)],
  have h_left : ∫ x in s, ⟪(indicator_const_Lp 2 hs hμs c) x, f x⟫ ∂μ = ∫ x in s, ⟪c, f x⟫ ∂μ,
  { suffices h_ae_eq : ∀ᵐ x ∂μ, x ∈ s → ⟪indicator_const_Lp 2 hs hμs c x, f x⟫ = ⟪c, f x⟫,
      from set_integral_congr_ae hs h_ae_eq,
    have h_indicator : ∀ᵐ (x : α) ∂μ, x ∈ s → (indicator_const_Lp 2 hs hμs c x) = c,
      from indicator_const_Lp_coe_fn_mem,
    refine h_indicator.mono (λ x hx hxs, _),
    congr,
    exact hx hxs, },
  have h_right : ∫ x in sᶜ, ⟪(indicator_const_Lp 2 hs hμs c) x, f x⟫ ∂μ = 0,
  { suffices h_ae_eq : ∀ᵐ x ∂μ, x ∉ s → ⟪indicator_const_Lp 2 hs hμs c x, f x⟫ = 0,
    { simp_rw ← set.mem_compl_iff at h_ae_eq,
      suffices h_int_zero : ∫ x in sᶜ, inner (indicator_const_Lp 2 hs hμs c x) (f x) ∂μ
        = ∫ x in sᶜ, (0 : 𝕜) ∂μ,
      { rw h_int_zero,
        simp, },
      exact set_integral_congr_ae hs.compl h_ae_eq, },
    have h_indicator : ∀ᵐ (x : α) ∂μ, x ∉ s → (indicator_const_Lp 2 hs hμs c x) = 0,
      from indicator_const_Lp_coe_fn_nmem,
    refine h_indicator.mono (λ x hx hxs, _),
    rw hx hxs,
    exact inner_zero_left, },
  rw [h_left, h_right, add_zero],
end

/-- The inner product in `L2` of the indicator of a set `indicator_const_Lp 2 hs hμs c` and `f` is
equal to the inner product of the constant `c` and the integral of `f` over `s`. -/
lemma inner_indicator_const_Lp_eq_inner_set_integral [complete_space E] [normed_space ℝ E]
  (hs : measurable_set s) (hμs : μ s ≠ ∞) (c : E) (f : Lp E 2 μ) :
  (⟪indicator_const_Lp 2 hs hμs c, f⟫ : 𝕜) = ⟪c, ∫ x in s, f x ∂μ⟫ :=
by rw [← integral_inner (integrable_on_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs),
    L2.inner_indicator_const_Lp_eq_set_integral_inner]

variables {𝕜}

/-- The inner product in `L2` of the indicator of a set `indicator_const_Lp 2 hs hμs (1 : 𝕜)` and
a real or complex function `f` is equal to the integral of `f` over `s`. -/
lemma inner_indicator_const_Lp_one (hs : measurable_set s) (hμs : μ s ≠ ∞) (f : Lp 𝕜 2 μ) :
  ⟪indicator_const_Lp 2 hs hμs (1 : 𝕜), f⟫ = ∫ x in s, f x ∂μ :=
by { rw L2.inner_indicator_const_Lp_eq_inner_set_integral 𝕜 hs hμs (1 : 𝕜) f, simp, }

end indicator_const_Lp

end L2

section inner_continuous

variables {α : Type*} [topological_space α] [measure_space α] [borel_space α] {𝕜 : Type*}
  [is_R_or_C 𝕜]
variables (μ : measure α) [is_finite_measure μ]

open_locale bounded_continuous_function complex_conjugate

local notation `⟪`x`, `y`⟫` := @inner 𝕜 (α →₂[μ] 𝕜) _ x y

/-- For bounded continuous functions `f`, `g` on a finite-measure topological space `α`, the L^2
inner product is the integral of their pointwise inner product. -/
lemma bounded_continuous_function.inner_to_Lp (f g : α →ᵇ 𝕜) :
  ⟪bounded_continuous_function.to_Lp 2 μ 𝕜 f, bounded_continuous_function.to_Lp 2 μ 𝕜 g⟫
  = ∫ x, conj (f x) * g x ∂μ :=
begin
  apply integral_congr_ae,
  have hf_ae := f.coe_fn_to_Lp 2 μ 𝕜,
  have hg_ae := g.coe_fn_to_Lp 2 μ 𝕜,
  filter_upwards [hf_ae, hg_ae] with _ hf hg,
  rw [hf, hg],
  simp
end

variables [compact_space α]

/-- For continuous functions `f`, `g` on a compact, finite-measure topological space `α`, the L^2
inner product is the integral of their pointwise inner product. -/
lemma continuous_map.inner_to_Lp (f g : C(α, 𝕜)) :
  ⟪continuous_map.to_Lp 2 μ 𝕜 f, continuous_map.to_Lp 2 μ 𝕜 g⟫
  = ∫ x, conj (f x) * g x ∂μ :=
begin
  apply integral_congr_ae,
  have hf_ae := f.coe_fn_to_Lp μ,
  have hg_ae := g.coe_fn_to_Lp μ,
  filter_upwards [hf_ae, hg_ae] with _ hf hg,
  rw [hf, hg],
  simp
end

end inner_continuous

end measure_theory
