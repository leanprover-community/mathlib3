/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import probability.kernel.composition

/-!
# Integral

## Main definitions

* `foo_bar`

## Main statements

* `foo_bar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open measure_theory filter

open_locale nnreal ennreal measure_theory probability_theory

namespace probability_theory

variables {α β E : Type*} {mα : measurable_space α} {mβ : measurable_space β}
  [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]
  {f : β → E} {g : α → β} {a : α} {s : set β}
  {κ : kernel α β}

include mα mβ

lemma integral_const {μ : measure β}  :
  ∫ x, f x ∂(kernel.const α μ a) = ∫ x, f x ∂μ :=
by rw kernel.const_apply

lemma integral_deterministic' (hg : measurable g) (hf : strongly_measurable f) :
  ∫ x, f x ∂(kernel.deterministic hg a) = f (g a) :=
by rw [kernel.deterministic_apply, integral_dirac' _ _ hf]

lemma integral_deterministic (hg : measurable g) [measurable_singleton_class β] :
  ∫ x, f x ∂(kernel.deterministic hg a) = f (g a) :=
by rw [kernel.deterministic_apply, integral_dirac _ (g a)]

lemma integral_restrict (hs : measurable_set s) :
  ∫ x, f x ∂(kernel.restrict κ hs a) = ∫ x in s, f x ∂(κ a) :=
by rw kernel.restrict_apply

lemma integral_with_density [kernel.is_s_finite_kernel κ]
  {g : α → β → ℝ≥0} (hg : measurable (function.uncurry g)) :
  ∫ b, f b ∂(kernel.with_density κ (λ a b, g a b) a) = ∫ b, (g a b) • f b ∂(κ a) :=
begin
  rw [kernel.with_density_apply, integral_with_density_eq_integral_smul],
  { exact measurable.of_uncurry_left hg, },
  { exact measurable_coe_nnreal_ennreal.comp hg, },
end

end probability_theory
