/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Sébastien Gouëzel, Yury Kudryashov
-/
import measure_theory.integral.set_integral
import measure_theory.measure.lebesgue.basic

/-! # Properties of integration with respect to the Lebesgue measure -/

open set filter measure_theory measure_theory.measure topological_space

section region_between

variable {α : Type*}
variables [measurable_space α] {μ : measure α} {f g : α → ℝ} {s : set α}

theorem volume_region_between_eq_integral' [sigma_finite μ]
  (f_int : integrable_on f s μ) (g_int : integrable_on g s μ)
  (hs : measurable_set s) (hfg : f ≤ᵐ[μ.restrict s] g ) :
  μ.prod volume (region_between f g s) = ennreal.of_real (∫ y in s, (g - f) y ∂μ) :=
begin
  have h : g - f =ᵐ[μ.restrict s] (λ x, real.to_nnreal (g x - f x)),
    from hfg.mono (λ x hx, (real.coe_to_nnreal _ $ sub_nonneg.2 hx).symm),
  rw [volume_region_between_eq_lintegral f_int.ae_measurable g_int.ae_measurable hs,
    integral_congr_ae h, lintegral_congr_ae,
    lintegral_coe_eq_integral _ ((integrable_congr h).mp (g_int.sub f_int))],
  simpa only,
end

/-- If two functions are integrable on a measurable set, and one function is less than
    or equal to the other on that set, then the volume of the region
    between the two functions can be represented as an integral. -/
theorem volume_region_between_eq_integral [sigma_finite μ]
  (f_int : integrable_on f s μ) (g_int : integrable_on g s μ)
  (hs : measurable_set s) (hfg : ∀ x ∈ s, f x ≤ g x) :
  μ.prod volume (region_between f g s) = ennreal.of_real (∫ y in s, (g - f) y ∂μ) :=
volume_region_between_eq_integral' f_int g_int hs
  ((ae_restrict_iff' hs).mpr (eventually_of_forall hfg))

end region_between

section summable_norm_Icc

open continuous_map

/- The following lemma is a minor variation on `integrable_of_summable_norm_restrict` in
`measure_theory.integral.set_integral`, but it is placed here because it needs to know that
`Icc a b` has volume `b - a`. -/

/-- If the sequence with `n`-th term the the sup norm of `λ x, f (x + n)` on the interval `Icc 0 1`,
for `n ∈ ℤ`, is summable, then `f` is integrable on `ℝ`. -/
lemma real.integrable_of_summable_norm_Icc {E : Type*} [normed_add_comm_group E] {f : C(ℝ, E)}
  (hf : summable (λ n : ℤ, ‖(f.comp $ continuous_map.add_right n).restrict (Icc 0 1)‖)) :
  integrable f :=
begin
  refine integrable_of_summable_norm_restrict (summable_of_nonneg_of_le
    (λ n : ℤ, mul_nonneg (norm_nonneg (f.restrict (⟨Icc n (n + 1), is_compact_Icc⟩ : compacts ℝ)))
    ennreal.to_real_nonneg) (λ n, _) hf) (Union_Icc_int_cast ℝ),
  simp only [compacts.coe_mk, real.volume_Icc, add_sub_cancel', ennreal.to_real_of_real zero_le_one,
    mul_one, norm_le _ (norm_nonneg _)],
  intro x,
  have := ((f.comp $ continuous_map.add_right n).restrict (Icc 0 1)).norm_coe_le_norm
    ⟨x - n, ⟨sub_nonneg.mpr x.2.1, sub_le_iff_le_add'.mpr x.2.2⟩⟩,
  simpa only [continuous_map.restrict_apply, comp_apply, coe_add_right, subtype.coe_mk,
    sub_add_cancel]
    using this,
end

end summable_norm_Icc

/-!
### Substituting `-x` for `x`

These lemmas are stated in terms of either `Iic` or `Ioi` (neglecting `Iio` and `Ici`) to match
mathlib's conventions for integrals over finite intervals (see `interval_integral`). For the case
of finite integrals, see `interval_integral.integral_comp_neg`.
-/

@[simp] lemma integral_comp_neg_Iic {E : Type*}
  [normed_add_comm_group E] [normed_space ℝ E] [complete_space E] (c : ℝ) (f : ℝ → E) :
  ∫ x in Iic c, f (-x) = ∫ x in Ioi (-c), f x :=
begin
  have A : measurable_embedding (λ x : ℝ, -x),
    from (homeomorph.neg ℝ).closed_embedding.measurable_embedding,
  have := A.set_integral_map f (Ici (-c)),
  rw measure.map_neg_eq_self (volume : measure ℝ) at this,
  simp_rw [←integral_Ici_eq_integral_Ioi, this, neg_preimage, preimage_neg_Ici, neg_neg],
end

@[simp] lemma integral_comp_neg_Ioi {E : Type*}
  [normed_add_comm_group E] [normed_space ℝ E] [complete_space E] (c : ℝ) (f : ℝ → E) :
  ∫ x in Ioi c, f (-x) = ∫ x in Iic (-c), f x :=
begin
  rw [←neg_neg c, ←integral_comp_neg_Iic],
  simp only [neg_neg],
end
