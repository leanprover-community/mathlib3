/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.inner_product_space.orientation
import measure_theory.measure.haar_lebesgue

/-!
# Volume forms and measures on inner product spaces

A volume form induces a Lebesgue measure on general finite-dimensional real vector spaces. In this
file, we discuss the specific situation of inner product spaces, where an orientation gives
rise to a canonical volume form. We show that the measure coming from this volume form gives
measure `1` to the parallelogram spanned by any orthonormal basis, and that it coincides with
the canonical `volume` from the `measure_space` instance.
-/

open finite_dimensional measure_theory measure_theory.measure set

variables {ι F : Type*} [fintype ι] [inner_product_space ℝ F] [finite_dimensional ℝ F]
[measurable_space F] [borel_space F]

section

variables {m n : ℕ} [_i : fact (finrank ℝ F = n)]
include _i

/-- The volume form coming from an orientation in an inner product space gives measure `1` to the
parallelogram associated to any orthonormal basis. This is a rephrasing of
`abs_volume_form_apply_of_orthonormal` in terms of measures. -/
lemma orientation.add_haar_orthonormal_basis
  (o : orientation ℝ F (fin n)) (b : orthonormal_basis ι ℝ F) :
  o.volume_form.measure (parallelogram b) = 1 :=
begin
  have e : ι ≃ fin n,
  { refine fintype.equiv_fin_of_card_eq _,
    rw [← _i.out, finrank_eq_card_basis b.to_basis] },
  have A : ⇑b = (b.reindex e) ∘ e,
  { ext x,
    simp only [orthonormal_basis.coe_reindex, function.comp_app, equiv.symm_apply_apply] },
  rw [A, parallelogram_comp, alternating_map.measure_parallelogram,
    o.abs_volume_form_apply_of_orthonormal, ennreal.of_real_one],
end

/-- In an oriented inner product space, the measure coming from the canonical volume form
associated to an orientation coincides with the volume. -/
lemma orientation.add_haar_eq_volume (o : orientation ℝ F (fin n)) :
  o.volume_form.measure = volume :=
begin
  have A : o.volume_form.measure ((std_orthonormal_basis ℝ F).to_basis.parallelogram) = 1,
    from orientation.add_haar_orthonormal_basis o (std_orthonormal_basis ℝ F),
  rw [add_haar_measure_unique o.volume_form.measure
    ((std_orthonormal_basis ℝ F).to_basis.parallelogram), A, one_smul],
  simp only [volume, basis.add_haar],
end

end

/-- The volume measure in a finite-dimensional inner product space gives measure `1` to the
parallelogram spanned by any orthonormal basis. -/
lemma orthonormal_basis.volume_parallelogram (b : orthonormal_basis ι ℝ F) :
  volume (parallelogram b) = 1 :=
begin
  haveI : fact (finrank ℝ F = finrank ℝ F) := ⟨rfl⟩,
  let o := (std_orthonormal_basis ℝ F).to_basis.orientation,
  rw ← o.add_haar_eq_volume,
  exact o.add_haar_orthonormal_basis b,
end
