/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import probability_theory.density

/-
Right now, pdf is defined such that `μ.with_density f` must agree with
`map X ℙ` everywhere, while in introductory probability courses, is condition
is often relaxed such that they only need to agree on intervals of the form `(-∞, x]`.
While, these conditions are not equivalent in general, for finite measures, it is the case.

pf. Use Dykin's π-λ theorem.

With that in mind, we can show that if `F(x) := map X ℙ (-∞, x]` is differentiable,
by FTC `f := F'` satisfies `∫ x in a..b, f x ∂μ = F b - F a = map X ℙ (a, b]`, hence, implying
`μ.with_density f` equals `map X ℙ` and thus, `f =ᵐ[μ] pdf X`.

This allows us to use traditional methods for find the pdf of transformations, namely
`pdf g(X) x = pdf X (g⁻¹ x) * g'`.

-/

noncomputable theory
open_locale classical measure_theory nnreal ennreal interval

namespace measure_theory

open set topological_space measurable_space measure

-- variables {α E F : Type*}
-- variables [normed_group E] [measurable_space E] [second_countable_topology E] [linear_order E]
--   [order_topology E] [normed_space ℝ E] [complete_space E] [borel_space E]
-- variables [normed_group F] [measurable_space F] [second_countable_topology F] [linear_order F]
--   [order_topology F] [normed_space ℝ F] [complete_space F] [borel_space F]
--   [linear_order F] [order_topology F]

#check ext_of_generate_finite
#check borel_eq_generate_Iio
#check ext_of_Iic

variables {α : Type*} [measurable_space α]
variables {𝕜 : Type*} [measurable_space 𝕜] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 ℝ]

def cdf [preorder 𝕜] (X : α → 𝕜) (ℙ : measure α) (x : 𝕜) :=
(map X ℙ (Iic x)).to_real

section

variables [preorder 𝕜] {ℙ : measure α} [is_finite_measure ℙ] {X : α → 𝕜}

lemma cdf_mono (hX : measurable X) : monotone (cdf X ℙ) :=
begin
  haveI := is_finite_measure_map ℙ hX,
  intros x y hle,
  exact ennreal.to_real_mono (measure_lt_top _ _).ne (measure_mono (Iic_subset_Iic.2 hle))
end

end

section

variables {ℙ : measure α} [is_finite_measure ℙ] {μ : measure 𝕜}

variables [second_countable_topology 𝕜] [complete_space 𝕜] [borel_space 𝕜] [normed_space ℝ 𝕜]
  [linear_order 𝕜] [order_topology 𝕜]

lemma deriv_nonneg_of_mono {f : 𝕜 → ℝ}
  (hf : differentiable ℝ f) (hfmono : monotone f) (x : 𝕜) :
  0 ≤ deriv f x :=
begin
  sorry
end

lemma deriv_cdf_nonneg {X : α → 𝕜} (hX : measurable X) (h : differentiable ℝ (cdf X ℙ)) (x : 𝕜) :
  0 ≤ deriv (cdf X ℙ) x :=
deriv_nonneg_of_mono h (cdf_mono hX) x

lemma integral_deriv_cdf {X : α → 𝕜} (hX : measurable X) (h : differentiable ℝ (cdf X ℙ)) :
  ∫ x, deriv (cdf X ℙ) x ∂μ = (ℙ set.univ).to_real :=
begin
  sorry
end

lemma pdf_integrable (X : α → 𝕜) :
  integrable (λ x, (pdf X ℙ μ x).to_real) μ :=
begin
  refine integrable_to_real_of_lintegral_ne_top (measurable_pdf X ℙ μ).ae_measurable _,
  by_cases hpdf : has_pdf X ℙ μ,
  { haveI := hpdf,
    rw measure.pdf.lintegral_eq_measure_univ,
    exact (measure_lt_top ℙ _).ne },
  { simp_rw [pdf, dif_neg hpdf, lintegral_zero_fun],
    exact ennreal.zero_ne_top }
end

#check ennreal.to_real_of_real
#check is_finite_measure_with_density

-- don't need `hX`
lemma set_integral_pdf_eq_set_integral_deriv_cdf {X : α → 𝕜} (hX : measurable X)
  (h : differentiable ℝ (cdf X ℙ)) {s : set 𝕜} (hs : measurable_set s) (hμs : μ s < ∞) :
  ∫ (x : 𝕜) in s, (pdf X ℙ μ x).to_real ∂μ = ∫ (x : 𝕜) in s, deriv (cdf X ℙ) x ∂μ :=
begin
  have : deriv (cdf X ℙ) = λ x, (ennreal.of_real (deriv (cdf X ℙ) x)).to_real,
  { ext x,
    rw ennreal.to_real_of_real,
    exact deriv_cdf_nonneg hX h x },
  rw [this, integral_to_real (measurable_pdf X ℙ μ).ae_measurable, integral_to_real],
  { rw [← with_density_apply _ hs, ← with_density_apply _ hs],
    suffices : μ.with_density (pdf X ℙ μ) =
      μ.with_density (λ x, ennreal.of_real (deriv (cdf X ℙ) x)),
    { rw this },
    haveI : is_finite_measure ( μ.with_density (pdf X ℙ μ)),
    { refine is_finite_measure_with_density _,
      by_cases hpdf : has_pdf X ℙ μ,
      { haveI := hpdf,
        rw measure.pdf.lintegral_eq_measure_univ,
        exact (measure_lt_top ℙ _).ne },
      { simp_rw [pdf, dif_neg hpdf, lintegral_zero_fun],
        exact ennreal.zero_ne_top } },
    refine ext_of_Ioc _ _ _ _; sorry
  },
  { sorry },
  { exact ae_of_all _ (λ _, ennreal.of_real_lt_top) },
  { refine ae_lt_top (measurable_pdf X ℙ μ)
      (ne_of_lt (lt_of_le_of_lt (lintegral_mono_set (set.subset_univ _)) _)),
    rw set_lintegral_univ,
    by_cases hpdf : has_pdf X ℙ μ,
    { haveI := hpdf,
      rw measure.pdf.lintegral_eq_measure_univ,
      exact measure_lt_top ℙ _ },
    { simp_rw [pdf, dif_neg hpdf],
      rw lintegral_zero_fun,
      exact with_top.zero_lt_top } }
end

lemma pdf_ae_eq_of_cdf (X : α → 𝕜) (h : differentiable ℝ (cdf X ℙ)) :
  (λ x, (pdf X ℙ μ x).to_real) =ᵐ[μ] deriv (cdf X ℙ) :=
begin
  refine integrable.ae_eq_of_forall_set_integral_eq _ _ (pdf_integrable X) _ _;
  sorry
end

end

end measure_theory
