/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import measure_theory.measure.vector_measure
import measure_theory.integral.set_integral

/-!

# Signed measure defined by an integral

Given a measure `μ` and an integrable function `f`, we can define a signed measure `s` such
that for all measurable set `i`, `s i = ∫ x in i, f x ∂μ`. This definition is useful for
the Radon-Nikodym theorem for signed measures.

## Main definitions

* `measure_theory.measure.with_density_signed_measure`: the signed measure formed by integrating
  a function `f` with respect to a measure `μ` on some set.

## Implementation Notes

Instead of defining the signed measure through the relation `s i = ∫ x in i, f x ∂μ`, we
defined it as the difference between `μ.with_density f⁺` and `μ.with_density f⁻`. This method
allows us to avoid proving the summability condition for vector measures.

-/

noncomputable theory
open_locale classical measure_theory nnreal ennreal

variables {α β : Type*} {m : measurable_space α}

namespace measure_theory

namespace measure

include m

open topological_space

variables {μ ν : measure α} {f g : α → ℝ}

lemma is_finite_measure_of_real_of_integrable (hf : integrable f μ) :
  is_finite_measure (μ.with_density (λ x, ennreal.of_real (f x))) :=
is_finite_measure_with_density
  $ lt_of_le_of_lt (lintegral_mono $ λ x, show ennreal.of_real (f x) ≤ ∥f x∥₊,
    by exact ennreal.of_real_le_of_le_to_real (by simpa using le_abs_self (f x))) hf.2

/-- Given a measure `μ` and an integrable function `f`, `μ.with_density_signed_measure f` is
the signed measure which maps the set `i` to `∫ᵢ f⁺ ∂μ - ∫ᵢ f⁻ ∂μ`. -/
def with_density_signed_measure {m : measurable_space α}
  (μ : measure α) (f : α → ℝ) : signed_measure α :=
if hf : integrable f μ then
  @to_signed_measure α m (μ.with_density (λ x, ennreal.of_real (f x)))
  (is_finite_measure_of_real_of_integrable hf)
  -
  @to_signed_measure α m (μ.with_density (λ x, ennreal.of_real (-f x)))
  (is_finite_measure_of_real_of_integrable (integrable_neg_iff.2 hf))
else 0

lemma with_density_signed_measure_apply (hf : integrable f μ)
  {i : set α} (hi : measurable_set i) :
  μ.with_density_signed_measure f i = ∫ x in i, f x ∂μ :=
begin
  rw integral_eq_lintegral_pos_part_sub_lintegral_neg_part,
  { rw [with_density_signed_measure, dif_pos hf],
    simp [if_pos hi, with_density_apply _ hi] },
  { rw ← integrable_on_univ,
    exact hf.integrable_on.restrict measurable_set.univ },
end

@[simp]
lemma with_density_signed_measure_zero :
  μ.with_density_signed_measure 0 = 0 :=
begin
  ext1 i hi,
  erw [with_density_signed_measure_apply (integrable_zero α ℝ μ) hi],
  simp,
end

@[simp]
lemma with_density_signed_measure_neg (hf : integrable f μ) :
  μ.with_density_signed_measure (-f) = -μ.with_density_signed_measure f :=
begin
  ext1 i hi,
  rw [vector_measure.neg_apply, with_density_signed_measure_apply hf hi,
      ← integral_neg, with_density_signed_measure_apply hf.neg hi],
  refl
end

@[simp]
lemma with_density_signed_measure_add (hf : integrable f μ) (hg : integrable g μ) :
  μ.with_density_signed_measure (f + g) =
  μ.with_density_signed_measure f + μ.with_density_signed_measure g :=
begin
  ext1 i hi,
  rw [with_density_signed_measure_apply (hf.add hg) hi, vector_measure.add_apply,
      with_density_signed_measure_apply hf hi, with_density_signed_measure_apply hg hi],
  simp_rw [pi.add_apply],
  rw integral_add; rw ← integrable_on_univ,
  { exact hf.integrable_on.restrict measurable_set.univ },
  { exact hg.integrable_on.restrict measurable_set.univ }
end

@[simp]
lemma with_density_signed_measure_sub (hf : integrable f μ) (hg : integrable g μ) :
  μ.with_density_signed_measure (f - g) =
  μ.with_density_signed_measure f - μ.with_density_signed_measure g :=
by rw [sub_eq_add_neg, sub_eq_add_neg, with_density_signed_measure_add hf hg.neg,
       with_density_signed_measure_neg hg]

@[simp]
lemma with_density_signed_measure_smul (r : ℝ) (hf : integrable f μ) :
  μ.with_density_signed_measure (r • f) = r • μ.with_density_signed_measure f :=
begin
  ext1 i hi,
  rw [with_density_signed_measure_apply (hf.smul r) hi, vector_measure.smul_apply,
      with_density_signed_measure_apply hf hi, ← integral_smul],
  refl
end

lemma with_density_signed_measure_absolutely_continuous
  (μ : measure α) (f : α → ℝ) :
  μ.with_density_signed_measure f ≪ μ.to_ennreal_vector_measure :=
begin
  by_cases hf : integrable f μ,
  { refine vector_measure.absolutely_continuous.mk (λ i hi₁ hi₂, _),
    rw to_ennreal_vector_measure_apply_measurable hi₁ at hi₂,
    rw [with_density_signed_measure_apply hf hi₁, measure.restrict_zero_set hi₂,
        integral_zero_measure] },
  { rw [with_density_signed_measure, dif_neg hf],
    exact vector_measure.absolutely_continuous.zero _ }
end

end measure

end measure_theory
