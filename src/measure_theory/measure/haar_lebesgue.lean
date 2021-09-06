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
We deduce basic properties of any Haar measure on a finite dimensional real vector space:
* `map_linear_map_add_haar_eq_smul_add_haar`: a linear map rescales the Haar measure by the
  absolute value of its determinant.

-/

open topological_space set
open_locale ennreal pointwise

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

open measure topological_space.positive_compacts finite_dimensional

/-!
### The Lebesgue measure is a Haar measure on `ℝ` and on `ℝ^ι`.
-/

lemma is_add_left_invariant_real_volume : is_add_left_invariant ⇑(volume : measure ℝ) :=
by simp [← map_add_left_eq_self, real.map_volume_add_left]

/-- The Haar measure equals the Lebesgue measure on `ℝ`. -/
lemma add_haar_measure_eq_volume : add_haar_measure Icc01 = volume :=
begin
  convert (add_haar_measure_unique _ Icc01).symm,
  { simp [Icc01] },
  { apply_instance },
  { exact is_add_left_invariant_real_volume }
end

instance : is_add_haar_measure (volume : measure ℝ) :=
by { rw ← add_haar_measure_eq_volume, apply_instance }

lemma is_add_left_invariant_real_volume_pi (ι : Type*) [fintype ι] :
  is_add_left_invariant ⇑(volume : measure (ι → ℝ)) :=
by simp [← map_add_left_eq_self, real.map_volume_pi_add_left]

/-- The Haar measure equals the Lebesgue measure on `ℝ^ι`. -/
lemma add_haar_measure_eq_volume_pi (ι : Type*) [fintype ι] :
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
by { rw ← add_haar_measure_eq_volume_pi, apply_instance }

/-!
### Applying a linear map rescales Haar measure by the determinant

We first prove this on `ι → ℝ`, using that this is already known for the product Lebesgue
measure (thanks to matrices computations). Then, we extend this to any finite-dimensional real
vector space by using a linear equiv with a space of the form `ι → ℝ`, and arguing that such a
linear equiv maps Haar measure to Haar measure.
-/

lemma map_linear_map_add_haar_pi_eq_smul_add_haar
  {ι : Type*} [fintype ι] {f : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} (hf : f.det ≠ 0)
  (μ : measure (ι → ℝ)) [is_add_haar_measure μ] :
  measure.map f μ = ennreal.of_real (abs (f.det)⁻¹) • μ :=
begin
  /- We have already proved the result for the Lebesgue product measure, using matrices.
  We deduce it for any Haar measure by uniqueness (up to scalar multiplication). -/
  have := add_haar_measure_unique (is_add_left_invariant_add_haar μ) (pi_Icc01 ι),
  conv_lhs { rw this }, conv_rhs { rw this },
  simp [add_haar_measure_eq_volume_pi, real.map_linear_map_volume_pi_eq_smul_volume_pi hf,
    smul_smul, mul_comm],
end

lemma map_linear_map_add_haar_eq_smul_add_haar
  {E : Type*} [normed_group E] [normed_space ℝ E] [measurable_space E] [borel_space E]
  [finite_dimensional ℝ E] (μ : measure E) [is_add_haar_measure μ]
  {f : E →ₗ[ℝ] E} (hf : f.det ≠ 0) :
  measure.map f μ = ennreal.of_real (abs (f.det)⁻¹) • μ :=
begin
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
  rw [map_linear_map_add_haar_pi_eq_smul_add_haar hf (map e μ), linear_map.map_smul,
    map_map Cesymm.measurable Ce.measurable, ecomp, map_id]
end

@[simp] lemma haar_preimage_linear_map
  {E : Type*} [normed_group E] [normed_space ℝ E] [measurable_space E] [borel_space E]
  [finite_dimensional ℝ E] (μ : measure E) [is_add_haar_measure μ]
  {f : E →ₗ[ℝ] E} (hf : f.det ≠ 0) (s : set E) :
  μ (f ⁻¹' s) = ennreal.of_real (abs (f.det)⁻¹) * μ s :=
calc μ (f ⁻¹' s) = measure.map f μ s :
  ((f.equiv_of_det_ne_zero hf).to_continuous_linear_equiv.to_homeomorph
    .to_measurable_equiv.map_apply s).symm
... = ennreal.of_real (abs (f.det)⁻¹) * μ s :
  by { rw map_linear_map_add_haar_eq_smul_add_haar μ hf, refl }

/-!
### Basic properties of Haar measures on real vector spaces
-/

@[simp] lemma add_haar_ball
  {E : Type*} [normed_group E] [measurable_space E]
  [borel_space E] (μ : measure E) [is_add_haar_measure μ] (x : E) (r : ℝ) :
  μ (metric.ball x r) = μ (metric.ball (0 : E) r) :=
begin
  have : metric.ball (0 : E) r = ((+) x) ⁻¹' (metric.ball x r), by { ext y, simp [dist_eq_norm] },
  rw [this, add_haar_preimage_add]
end

variables {E : Type*} [normed_group E] [measurable_space E] [normed_space ℝ E]
  [finite_dimensional ℝ E]
  [borel_space E] (μ : measure E) [is_add_haar_measure μ]

lemma map_haar_smul {r : ℝ} (hr : r ≠ 0) :
  measure.map ((•) r) μ = ennreal.of_real (abs (r^(finrank ℝ E))⁻¹) • μ :=
begin
  let f : E →ₗ[ℝ] E := r • 1,
  change measure.map f μ = _,
  have hf : f.det ≠ 0,
  { simp only [mul_one, linear_map.det_smul, ne.def, monoid_hom.map_one],
    assume h,
    exact hr (pow_eq_zero h) },
  simp only [map_linear_map_add_haar_eq_smul_add_haar μ hf, mul_one, linear_map.det_smul,
    monoid_hom.map_one],
end

open_locale pointwise

lemma haar_preimage_smul {r : ℝ} (hr : r ≠ 0) (s : set E) :
  μ (((•) r) ⁻¹' s) = ennreal.of_real (abs (r^(finrank ℝ E))⁻¹) * μ s :=
calc μ (((•) r) ⁻¹' s) = measure.map ((•) r) μ s :
begin
  let a : units ℝ := is_unit.unit (is_unit_iff_ne_zero.2 hr),
  let Z : E ≃ₜ E := homeomorph.smul a,
  convert (Z.to_measurable_equiv.map_apply s).symm,
  refl,
end

#exit

  ((f.equiv_of_det_ne_zero hf).to_continuous_linear_equiv.to_homeomorph
    .to_measurable_equiv.map_apply s).symm
... = ennreal.of_real (abs (f.det)⁻¹) * μ s :
  by { rw map_linear_map_add_haar_eq_smul_add_haar μ hf, refl }



end measure_theory


#exit


lemma smul_map_volume_mul_left {a : ℝ} (h : a ≠ 0) :
  ennreal.of_real (abs a) • measure.map ((*) a) volume = volume :=
begin
  refine (real.measure_ext_Ioo_rat $ λ p q, _).symm,
  cases lt_or_gt_of_ne h with h h,
  { simp only [real.volume_Ioo, measure.smul_apply, ← ennreal.of_real_mul (le_of_lt $ neg_pos.2 h),
      measure.map_apply (measurable_const_mul a) measurable_set_Ioo, neg_sub_neg,
      ← neg_mul_eq_neg_mul, preimage_const_mul_Ioo_of_neg _ _ h, abs_of_neg h, mul_sub,
      mul_div_cancel' _ (ne_of_lt h)] },
  { simp only [real.volume_Ioo, measure.smul_apply, ← ennreal.of_real_mul (le_of_lt h),
      measure.map_apply (measurable_const_mul a) measurable_set_Ioo, preimage_const_mul_Ioo _ _ h,
      abs_of_pos h, mul_sub, mul_div_cancel' _ (ne_of_gt h)] }
end

lemma map_volume_mul_left {a : ℝ} (h : a ≠ 0) :
  measure.map ((*) a) volume = ennreal.of_real (abs a⁻¹) • volume :=
by conv_rhs { rw [← real.smul_map_volume_mul_left h, smul_smul,
  ← ennreal.of_real_mul (abs_nonneg _), ← abs_mul, inv_mul_cancel h, abs_one, ennreal.of_real_one,
  one_smul] }

@[simp] lemma volume_preimage_mul_left {a : ℝ} (h : a ≠ 0) (s : set ℝ) :
  volume (((*) a) ⁻¹' s) = ennreal.of_real (abs a⁻¹) * volume s :=
calc volume (((*) a) ⁻¹' s) = measure.map ((*) a) volume s :
  ((homeomorph.mul_left' a h).to_measurable_equiv.map_apply s).symm
... = ennreal.of_real (abs a⁻¹) * volume s : by { rw map_volume_mul_left h, refl }

lemma smul_map_volume_mul_right {a : ℝ} (h : a ≠ 0) :
  ennreal.of_real (abs a) • measure.map (* a) volume = volume :=
by simpa only [mul_comm] using real.smul_map_volume_mul_left h

lemma map_volume_mul_right {a : ℝ} (h : a ≠ 0) :
  measure.map (* a) volume = ennreal.of_real (abs a⁻¹) • volume :=
by simpa only [mul_comm] using real.map_volume_mul_left h

@[simp] lemma volume_preimage_mul_right {a : ℝ} (h : a ≠ 0) (s : set ℝ) :
  volume ((* a) ⁻¹' s) = ennreal.of_real (abs a⁻¹) * volume s :=
by simpa only [mul_comm] using volume_preimage_mul_left h s

lemma map_volume_neg : measure.map has_neg.neg (volume : measure ℝ) = volume :=
eq.symm $ real.measure_ext_Ioo_rat $ λ p q,
  by simp [show measure.map has_neg.neg volume (Ioo (p : ℝ) q) = _,
    from measure.map_apply measurable_neg measurable_set_Ioo]

@[simp] lemma volume_preimage_neg (s : set ℝ) : volume (-s) = volume s :=
calc volume (has_neg.neg ⁻¹' s) = measure.map (has_neg.neg) volume s :
  ((homeomorph.neg ℝ).to_measurable_equiv.map_apply s).symm
... = volume s : by rw map_volume_neg
