/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import measure_theory.measure.vector_measure
import measure_theory.function.ae_eq_of_integral

/-!

# Vector measure defined by an integral

Given a measure `μ` and an integrable function `f : α → E`, we can define a vector measure `v` such
that for all measurable set `s`, `v i = ∫ x in s, f x ∂μ`. This definition is useful for
the Radon-Nikodym theorem for signed measures.

## Main definitions

* `measure_theory.measure.with_densityᵥ`: the vector measure formed by integrating a function `f`
  with respect to a measure `μ` on some set if `f` is integrable, and `0` otherwise.

-/

noncomputable theory
open_locale classical measure_theory nnreal ennreal

variables {α β : Type*} {m : measurable_space α}

namespace measure_theory

open topological_space

variables {μ ν : measure α}
variables {E : Type*} [normed_group E] [measurable_space E] [second_countable_topology E]
  [normed_space ℝ E] [complete_space E] [borel_space E]

/-- Given a measure `μ` and an integrable function `f`, `μ.with_densityᵥ f` is
the vector measure which maps the set `s` to `∫ₛ f ∂μ`. -/
def measure.with_densityᵥ {m : measurable_space α} (μ : measure α) (f : α → E) :
  vector_measure α E :=
if hf : integrable f μ then
{ measure_of' := λ s, if measurable_set s then ∫ x in s, f x ∂μ else 0,
  empty' := by simp,
  not_measurable' := λ s hs, if_neg hs,
  m_Union' := λ s hs₁ hs₂,
  begin
    convert has_sum_integral_Union hs₁ hs₂ hf,
    { ext n, rw if_pos (hs₁ n) },
    { rw if_pos (measurable_set.Union hs₁) }
  end }
else 0

open measure

include m

variables {f g : α → E}

lemma with_densityᵥ_apply (hf : integrable f μ) {s : set α} (hs : measurable_set s) :
  μ.with_densityᵥ f s = ∫ x in s, f x ∂μ :=
by { rw [with_densityᵥ, dif_pos hf], exact dif_pos hs }

@[simp] lemma with_densityᵥ_zero : μ.with_densityᵥ (0 : α → E) = 0 :=
by { ext1 s hs, erw [with_densityᵥ_apply (integrable_zero α E μ) hs], simp, }

@[simp] lemma with_densityᵥ_neg : μ.with_densityᵥ (-f) = -μ.with_densityᵥ f :=
begin
  by_cases hf : integrable f μ,
  { ext1 i hi,
    rw [vector_measure.neg_apply, with_densityᵥ_apply hf hi,
        ← integral_neg, with_densityᵥ_apply hf.neg hi],
    refl },
  { rw [with_densityᵥ, with_densityᵥ, dif_neg hf, dif_neg, neg_zero],
    rwa integrable_neg_iff }
end

lemma with_densityᵥ_neg' : μ.with_densityᵥ (λ x, -f x) = -μ.with_densityᵥ f :=
with_densityᵥ_neg

@[simp] lemma with_densityᵥ_add (hf : integrable f μ) (hg : integrable g μ) :
  μ.with_densityᵥ (f + g) = μ.with_densityᵥ f + μ.with_densityᵥ g :=
begin
  ext1 i hi,
  rw [with_densityᵥ_apply (hf.add hg) hi, vector_measure.add_apply,
      with_densityᵥ_apply hf hi, with_densityᵥ_apply hg hi],
  simp_rw [pi.add_apply],
  rw integral_add; rw ← integrable_on_univ,
  { exact hf.integrable_on.restrict measurable_set.univ },
  { exact hg.integrable_on.restrict measurable_set.univ }
end

lemma with_densityᵥ_add' (hf : integrable f μ) (hg : integrable g μ) :
  μ.with_densityᵥ (λ x, f x + g x) = μ.with_densityᵥ f + μ.with_densityᵥ g :=
with_densityᵥ_add hf hg

@[simp] lemma with_densityᵥ_sub (hf : integrable f μ) (hg : integrable g μ) :
  μ.with_densityᵥ (f - g) = μ.with_densityᵥ f - μ.with_densityᵥ g :=
by rw [sub_eq_add_neg, sub_eq_add_neg, with_densityᵥ_add hf hg.neg, with_densityᵥ_neg]

lemma with_densityᵥ_sub' (hf : integrable f μ) (hg : integrable g μ) :
  μ.with_densityᵥ (λ x, f x - g x) = μ.with_densityᵥ f - μ.with_densityᵥ g :=
with_densityᵥ_sub hf hg

@[simp] lemma with_densityᵥ_smul {𝕜 : Type*} [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E]
  [smul_comm_class ℝ 𝕜 E] [measurable_space 𝕜] [opens_measurable_space 𝕜] (r : 𝕜) :
  μ.with_densityᵥ (r • f) = r • μ.with_densityᵥ f :=
begin
  by_cases hf : integrable f μ,
  { ext1 i hi,
    rw [with_densityᵥ_apply (hf.smul r) hi, vector_measure.smul_apply,
        with_densityᵥ_apply hf hi, ← integral_smul r f],
    refl },
  { by_cases hr : r = 0,
    { rw [hr, zero_smul, zero_smul, with_densityᵥ_zero] },
    { rw [with_densityᵥ, with_densityᵥ, dif_neg hf, dif_neg, smul_zero],
      rwa integrable_smul_iff hr f } }
end

lemma with_densityᵥ_smul' {𝕜 : Type*} [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E]
  [smul_comm_class ℝ 𝕜 E] [measurable_space 𝕜] [opens_measurable_space 𝕜] (r : 𝕜) :
  μ.with_densityᵥ (λ x, r • f x) = r • μ.with_densityᵥ f :=
with_densityᵥ_smul r

lemma measure.with_densityᵥ_absolutely_continuous (μ : measure α) (f : α → ℝ) :
  μ.with_densityᵥ f ≪ μ.to_ennreal_vector_measure :=
begin
  by_cases hf : integrable f μ,
  { refine vector_measure.absolutely_continuous.mk (λ i hi₁ hi₂, _),
    rw to_ennreal_vector_measure_apply_measurable hi₁ at hi₂,
    rw [with_densityᵥ_apply hf hi₁, measure.restrict_zero_set hi₂, integral_zero_measure] },
  { rw [with_densityᵥ, dif_neg hf],
    exact vector_measure.absolutely_continuous.zero _ }
end

/-- Having the same density implies the underlying functions are equal almost everywhere. -/
lemma integrable.ae_eq_of_with_densityᵥ_eq {f g : α → E} (hf : integrable f μ) (hg : integrable g μ)
  (hfg : μ.with_densityᵥ f = μ.with_densityᵥ g) :
  f =ᵐ[μ] g :=
begin
  refine hf.ae_eq_of_forall_set_integral_eq f g hg (λ i hi _, _),
  rw [← with_densityᵥ_apply hf hi, hfg, with_densityᵥ_apply hg hi]
end

lemma with_densityᵥ_eq.congr_ae {f g : α → E} (h : f =ᵐ[μ] g) :
  μ.with_densityᵥ f = μ.with_densityᵥ g :=
begin
  by_cases hf : integrable f μ,
  { ext i hi,
    rw [with_densityᵥ_apply hf hi, with_densityᵥ_apply (hf.congr h) hi],
    exact integral_congr_ae (ae_restrict_of_ae h) },
  { have hg : ¬ integrable g μ,
    { intro hg, exact hf (hg.congr h.symm) },
    rw [with_densityᵥ, with_densityᵥ, dif_neg hf, dif_neg hg] }
end

lemma integrable.with_densityᵥ_eq_iff {f g : α → E}
  (hf : integrable f μ) (hg : integrable g μ) :
  μ.with_densityᵥ f = μ.with_densityᵥ g ↔ f =ᵐ[μ] g :=
⟨λ hfg, hf.ae_eq_of_with_densityᵥ_eq hg hfg, λ h, with_densityᵥ_eq.congr_ae h⟩

section signed_measure

lemma with_densityᵥ_to_real {f : α → ℝ≥0∞} (hfm : ae_measurable f μ) (hf : ∫⁻ x, f x ∂μ ≠ ∞) :
  μ.with_densityᵥ (λ x, (f x).to_real) =
  @to_signed_measure α _ (μ.with_density f) (is_finite_measure_with_density hf) :=
begin
  have hfi := integrable_to_real_of_lintegral_ne_top hfm hf,
  ext i hi,
  rw [with_densityᵥ_apply hfi hi, to_signed_measure_apply_measurable hi,
      with_density_apply _ hi, integral_to_real hfm.restrict],
  refine ae_lt_top' hfm.restrict (ne_top_of_le_ne_top hf _),
  conv_rhs { rw ← set_lintegral_univ },
  exact lintegral_mono_set (set.subset_univ _),
end

lemma with_densityᵥ_eq_with_density_pos_part_sub_with_density_neg_part
  {f : α → ℝ} (hfi : integrable f μ) :
  μ.with_densityᵥ f =
  @to_signed_measure α _ (μ.with_density (λ x, ennreal.of_real $ f x))
    (is_finite_measure_with_density_of_real hfi.2) -
  @to_signed_measure α _ (μ.with_density (λ x, ennreal.of_real $ -f x))
    (is_finite_measure_with_density_of_real hfi.neg.2) :=
begin
  ext i hi,
  rw [with_densityᵥ_apply hfi hi,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfi.integrable_on,
      vector_measure.sub_apply, to_signed_measure_apply_measurable hi,
      to_signed_measure_apply_measurable hi, with_density_apply _ hi, with_density_apply _ hi],
end

end signed_measure

end measure_theory
