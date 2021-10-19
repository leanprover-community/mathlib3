/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
import analysis.complex.isometry
import analysis.normed_space.conformal_linear_map

/-!
# Conformal maps between complex vector spaces

We prove the sufficient and necessary conditions for a real-linear map between complex vector spaces
to be conformal.

## Main results

* `is_conformal_map_complex_linear`: a nonzero complex linear map into an arbitrary complex
                                     normed space is conformal.
* `is_conformal_map_complex_linear_conj`: the composition of a nonzero complex linear map with
                                          `conj` is complex linear.
* `is_conformal_map_iff_is_complex_or_conj_linear`: a real linear map between the complex
                                                            plane is conformal iff it's complex
                                                            linear or the composition of
                                                            some complex linear map and `conj`.

## Warning

Antiholomorphic functions such as the complex conjugate are considered as conformal functions in
this file.
-/

noncomputable theory

open complex continuous_linear_map

lemma is_conformal_map_conj : is_conformal_map (conj_lie : ℂ →L[ℝ] ℂ) :=
conj_lie.to_linear_isometry.is_conformal_map

section conformal_into_complex_normed

variables {E : Type*} [normed_group E] [normed_space ℝ E] [normed_space ℂ E]
  [is_scalar_tower ℝ ℂ E] {z : ℂ} {g : ℂ →L[ℝ] E} {f : ℂ → E}

lemma is_conformal_map_complex_linear
  {map : ℂ →L[ℂ] E} (nonzero : map ≠ 0) : is_conformal_map (map.restrict_scalars ℝ) :=
begin
  have minor₁ : ∥map 1∥ ≠ 0,
  { simpa [ext_ring_iff] using nonzero },
  refine ⟨∥map 1∥, minor₁, ⟨∥map 1∥⁻¹ • map, _⟩, _⟩,
  { intros x,
    simp only [linear_map.smul_apply],
    have : x = x • 1 := by rw [smul_eq_mul, mul_one],
    nth_rewrite 0 [this],
    rw [_root_.coe_coe map, linear_map.coe_coe_is_scalar_tower],
    simp only [map.coe_coe, map.map_smul, norm_smul, normed_field.norm_inv, norm_norm],
    field_simp [minor₁], },
  { ext1,
    rw [← linear_isometry.coe_to_linear_map],
    simp [minor₁], },
end

lemma is_conformal_map_complex_linear_conj
  {map : ℂ →L[ℂ] E} (nonzero : map ≠ 0) :
  is_conformal_map ((map.restrict_scalars ℝ).comp (conj_cle : ℂ →L[ℝ] ℂ)) :=
(is_conformal_map_complex_linear nonzero).comp is_conformal_map_conj

end conformal_into_complex_normed

section conformal_into_complex_plane

open continuous_linear_map

variables {f : ℂ → ℂ} {z : ℂ} {g : ℂ →L[ℝ] ℂ}

lemma is_conformal_map.is_complex_or_conj_linear (h : is_conformal_map g) :
  (∃ (map : ℂ →L[ℂ] ℂ), map.restrict_scalars ℝ = g) ∨
  (∃ (map : ℂ →L[ℂ] ℂ), map.restrict_scalars ℝ = g ∘L ↑conj_cle) :=
begin
  rcases h with ⟨c, hc, li, hg⟩,
  rcases linear_isometry_complex (li.to_linear_isometry_equiv rfl) with ⟨a, ha⟩,
  let rot := c • (a : ℂ) • continuous_linear_map.id ℂ ℂ,
  cases ha,
  { refine or.intro_left _ ⟨rot, _⟩,
    ext1,
    simp only [coe_restrict_scalars', hg, ← li.coe_to_linear_isometry_equiv, ha,
               pi.smul_apply, continuous_linear_map.smul_apply, rotation_apply,
               continuous_linear_map.id_apply, smul_eq_mul], },
  { refine or.intro_right _ ⟨rot, _⟩,
    ext1,
    rw [continuous_linear_map.coe_comp', hg, ← li.coe_to_linear_isometry_equiv, ha],
    simp only [coe_restrict_scalars', function.comp_app, pi.smul_apply,
               linear_isometry_equiv.coe_trans, conj_lie_apply,
               rotation_apply, continuous_linear_equiv.coe_apply, conj_cle_apply],
    simp only [continuous_linear_map.smul_apply, continuous_linear_map.id_apply,
               smul_eq_mul, conj_conj], },
end

/-- A real continuous linear map on the complex plane is conformal if and only if the map or its
    conjugate is complex linear, and the map is nonvanishing. -/
lemma is_conformal_map_iff_is_complex_or_conj_linear:
  is_conformal_map g ↔
  ((∃ (map : ℂ →L[ℂ] ℂ), map.restrict_scalars ℝ = g) ∨
   (∃ (map : ℂ →L[ℂ] ℂ), map.restrict_scalars ℝ = g ∘L ↑conj_cle)) ∧ g ≠ 0 :=
begin
  split,
  { exact λ h, ⟨h.is_complex_or_conj_linear, h.ne_zero⟩, },
  { rintros ⟨⟨map, rfl⟩ | ⟨map, hmap⟩, h₂⟩,
    { refine is_conformal_map_complex_linear _,
      contrapose! h₂ with w,
      simp [w] },
    { have minor₁ : g = (map.restrict_scalars ℝ) ∘L ↑conj_cle,
      { ext1,
        simp [hmap] },
      rw minor₁ at ⊢ h₂,
      refine is_conformal_map_complex_linear_conj _,
      contrapose! h₂ with w,
      simp [w] } }
end

end conformal_into_complex_plane
