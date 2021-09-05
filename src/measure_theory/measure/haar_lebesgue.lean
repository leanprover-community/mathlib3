/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.measure.lebesgue
import measure_theory.measure.haar
import linear_algebra.finite_dimensional

/-!
# Relationship between the Haar and Lebesgue measures

We prove that the Haar measure and Lebesgue measure are equal on `ℝ` and on `ℝ^ι`.
-/

open topological_space set

/-- The interval `[0,1]` as a compact set with non-empty interior. -/
def topological_space.positive_compacts.Icc01 : positive_compacts ℝ :=
⟨Icc 0 1, is_compact_Icc, by simp_rw [interior_Icc, nonempty_Ioo, zero_lt_one]⟩

universe u

/-- The set `[0,1]^n` as a compact set with non-empty interior. -/
def topological_space.positive_compacts.pi_Icc01 (ι : Type*) [fintype ι] :
  positive_compacts (ι → ℝ) :=
⟨set.pi set.univ (λ i, Icc 0 1), is_compact_univ_pi (λ i, is_compact_Icc),
begin
  rw interior_pi_set,
  simp only [interior_Icc, univ_pi_nonempty_iff, nonempty_Ioo, implies_true_iff, zero_lt_one],
end⟩

namespace measure_theory

open measure topological_space.positive_compacts

lemma is_add_left_invariant_real_volume : is_add_left_invariant ⇑(volume : measure ℝ) :=
by simp [← map_add_left_eq_self, real.map_volume_add_left]

/-- The Haar measure equals the Lebesgue measure on `ℝ`. -/
lemma haar_measure_eq_volume : add_haar_measure Icc01 = volume :=
begin
  convert (add_haar_measure_unique _ Icc01).symm,
  { simp [Icc01] },
  { apply_instance },
  { exact is_add_left_invariant_real_volume }
end

instance : is_add_haar_measure (volume : measure ℝ) :=
by { rw ← haar_measure_eq_volume, apply_instance }

lemma is_add_left_invariant_real_volume_pi (ι : Type*) [fintype ι] :
  is_add_left_invariant ⇑(volume : measure (ι → ℝ)) :=
by simp [← map_add_left_eq_self, real.map_volume_pi_add_left]

/-- The Haar measure equals the Lebesgue measure on `ℝ^ι`. -/
lemma haar_measure_eq_volume_pi (ι : Type*) [fintype ι] :
  add_haar_measure (pi_Icc01 ι) = volume :=
begin
  convert (add_haar_measure_unique _ (pi_Icc01 ι)).symm,
  { simp only [pi_Icc01, volume_pi_pi (λ i, Icc (0 : ℝ) 1) (λ (i : ι), measurable_set_Icc),
      finset.prod_const_one, ennreal.of_real_one, real.volume_Icc, one_smul, sub_zero] },
  { apply_instance },
  { exact is_add_left_invariant_real_volume_pi ι }
end

instance is_add_haar_measure_volume_pi (ι : Type*) [fintype ι] :
  is_add_haar_measure (volume : measure (ι → ℝ)) :=
by { rw ← haar_measure_eq_volume_pi, apply_instance }

open finite_dimensional

lemma map_linear_map_haar_pi_eq_smul_haar
  {ι : Type*} [fintype ι] {f : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} (hf : f.det ≠ 0)
  (μ : measure (ι → ℝ)) [is_add_haar_measure μ] :
  measure.map f μ = ennreal.of_real (abs (f.det)⁻¹) • μ :=
begin
  /- We have already proved the result for the Lebesgue product measure, using matrices.
  We deduce it for any Haar measure by uniqueness (up to scalar multiplication). -/
  have := add_haar_measure_unique (is_add_left_invariant_add_haar μ) (pi_Icc01 ι),
  conv_lhs { rw this }, conv_rhs { rw this },
  simp [haar_measure_eq_volume_pi, real.map_linear_map_volume_pi_eq_smul_volume hf, smul_smul,
    mul_comm],
end

lemma finite_dimensional_of_haar_measure
  {E : Type*} [normed_group E] [normed_space ℝ E] [measurable_space E]
  [borel_space E] (μ : measure E) [is_add_haar_measure μ] :
  finite_dimensional ℝ E :=
sorry



lemma map_linear_map_haar_eq_smul_haar
  {E : Type*} [normed_group E] [normed_space ℝ E] [measurable_space E] [borel_space E]
  (μ : measure E) [is_add_haar_measure μ]
  {f : E →ₗ[ℝ] E} (hf : f.det ≠ 0) :
  measure.map f μ = ennreal.of_real (abs (f.det)⁻¹) • μ :=
begin
  haveI : finite_dimensional ℝ E := finite_dimensional_of_haar_measure μ,
  -- we reduce to the case of `E = ι → ℝ`, for which we have already proved the result using
  -- matrices in `map_linear_map_haar_pi_eq_smul_haar`.
  let ι := fin (finrank ℝ E),
  haveI : finite_dimensional ℝ (ι → ℝ) := by apply_instance,
  have : finrank ℝ E = finrank ℝ (ι → ℝ), by simp,
  have e : E ≃ₗ[ℝ] ι → ℝ := linear_equiv.of_finrank_eq E (ι → ℝ) this,
  -- next line is to avoid `g` getting reduced by `simp`.
  obtain ⟨g, hg⟩ : ∃ g, g = (e : E →ₗ[ℝ] (ι → ℝ)).comp (f.comp (e.symm : (ι → ℝ) →ₗ[ℝ] E)) :=
    ⟨_, rfl⟩,
  have gdet : g.det = f.det, by { rw [hg], exact linear_map.det_conj f e },
  rw ← gdet at hf ⊢,
  have fg : f = (e.symm : (ι → ℝ) →ₗ[ℝ] E).comp (g.comp (e : E →ₗ[ℝ] (ι → ℝ))),
  { ext x,
    simp only [linear_equiv.coe_coe, function.comp_app, linear_map.coe_comp,
      linear_equiv.symm_apply_apply, hg] },
  simp only [fg, linear_equiv.coe_coe, linear_map.coe_comp],
  have Ce : continuous e := (e : E →ₗ[ℝ] (ι → ℝ)).continuous_of_finite_dimensional,
  have Cg : continuous g := linear_map.continuous_of_finite_dimensional g,
  have Cesymm : continuous e.symm := (e.symm : (ι → ℝ) →ₗ[ℝ] E).continuous_of_finite_dimensional,
  rw [← map_map Cesymm.measurable (Cg.comp Ce).measurable, ← map_map Cg.measurable Ce.measurable],
  haveI : is_add_haar_measure (map e μ) := is_add_haar_measure_map μ e.to_add_equiv Ce Cesymm,
  have ecomp : (e.symm) ∘ e = id,
    by { ext x, simp only [id.def, function.comp_app, linear_equiv.symm_apply_apply] },
  rw [map_linear_map_haar_pi_eq_smul_haar hf (map e μ), linear_map.map_smul,
    map_map Cesymm.measurable Ce.measurable, ecomp, map_id]
end


end measure_theory
