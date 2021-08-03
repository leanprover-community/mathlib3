/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
import analysis.complex.isometry
import analysis.calculus.conformal

/-!
# Complex Conformal Maps

We prove the sufficient and necessary conditions for a complex function to be conformal.

## Main results

* `conformal_at_of_holomorph_or_antiholomorph_at`: a holomorphic or antiholomorphic maps with
                                                   a nonzero differential into an arbitrary complex
                                                   normed space is conformal.
* `conformal_at_iff_holomorphic_or_antiholomorphic_at`: the main theorem for complex functions.

## Warning

Antiholomorphic functions such as the complex conjugate are considered as conformal functions in
this file.
-/

noncomputable theory

open complex continuous_linear_map

section conformal_into_complex_normed

variables {E : Type*} [normed_group E] [normed_space ℝ E] [normed_space ℂ E]
  [is_scalar_tower ℝ ℂ E] {z : ℂ} {g : ℂ →L[ℝ] E} {f : ℂ → E}

lemma is_conformal_map_complex_linear
  {map : ℂ →L[ℂ] E} (nonzero : map ≠ 0) : is_conformal_map (map.restrict_scalars ℝ) :=
begin
  have minor₀ : ∀ (x : ℂ), x = x • 1 := λ x, by rw [smul_eq_mul, mul_one],
  have minor₁ : ∥map 1∥ ≠ 0,
  { contrapose! nonzero with w,
    ext1,
    rw [continuous_linear_map.zero_apply],
    exact norm_eq_zero.mp w, },
  refine ⟨∥map 1∥, minor₁, _⟩,
  let li' := ∥map 1∥⁻¹ • map,
  have key : ∀ (x : ℂ), ∥li' x∥ = ∥x∥,
  { intros x,
    simp only [li', continuous_linear_map.smul_apply],
    nth_rewrite 0 [minor₀ x],
    simp only [map.map_smul, norm_smul, normed_field.norm_inv, norm_norm],
    field_simp [minor₁], },
  let li : ℂ →ₗᵢ[ℝ] E := ⟨li', key⟩,
  have minor₂ : (li : ℂ → E) = li' := rfl,
  refine ⟨li, _⟩,
  ext1,
  simp only [minor₂, li', pi.smul_apply, continuous_linear_map.smul_apply, smul_smul],
  field_simp [minor₁],
end

lemma is_conformal_map_conj : is_conformal_map conj_cle.to_continuous_linear_map :=
⟨1, one_ne_zero, conj_lie.to_linear_isometry, by rw one_smul; refl⟩

lemma is_conformal_map_complex_linear_conj
  {map : ℂ →L[ℂ] E} (nonzero : map ≠ 0) :
  is_conformal_map ((map.restrict_scalars ℝ).comp conj_cle.to_continuous_linear_map) :=
is_conformal_map_conj.comp (is_conformal_map_complex_linear nonzero)

end conformal_into_complex_normed

section conformal_into_complex_plane

open continuous_linear_map

variables {f : ℂ → ℂ} {z : ℂ} {g : ℂ →L[ℝ] ℂ}

lemma is_complex_or_conj_complex_linear (h : is_conformal_map g) :
  (∃ (map : ℂ →L[ℂ] ℂ), map.restrict_scalars ℝ = g) ∨
  (∃ (map : ℂ →L[ℂ] ℂ), map.restrict_scalars ℝ = g.comp conj_cle.to_continuous_linear_map) :=
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
               rotation_apply, continuous_linear_equiv.coe_def_rev,
               continuous_linear_equiv.coe_apply, conj_cle_apply],
    simp only [continuous_linear_map.smul_apply, continuous_linear_map.id_apply,
               smul_eq_mul, conj_conj], },
end

/-- A real continuous linear map on the complex plane is conformal if and only if the map or its
    conjugate is complex linear, and the map is nonvanishing. -/
lemma is_complex_or_conj_complex_linear_iff_is_conformal_map :
  ((∃ (map : ℂ →L[ℂ] ℂ), map.restrict_scalars ℝ = g) ∨
   (∃ (map : ℂ →L[ℂ] ℂ), map.restrict_scalars ℝ = g.comp conj_cle.to_continuous_linear_map))
  ∧ g ≠ 0 ↔ is_conformal_map g :=
begin
  split,
  { rintros ⟨h₁, h₂⟩,
    cases h₁,
    { rcases h₁ with ⟨map, hmap⟩,
      rw ← hmap,
      refine is_conformal_map_complex_linear _,
      contrapose! h₂ with w,
      ext1,
      simp only [← hmap, coe_restrict_scalars', w, continuous_linear_map.zero_apply], },
    { rcases h₁ with ⟨map, hmap⟩,
      have minor₁ : g = (map.restrict_scalars ℝ).comp conj_cle.to_continuous_linear_map,
      { ext1,
        rw hmap,
        simp only [coe_comp', function.comp_app, conj_cle.coe_def_rev, conj_cle.coe_coe,
                  conj_cle_apply, conj_conj], },
      rw minor₁,
      refine is_conformal_map_complex_linear_conj _,
      contrapose! h₂ with w,
      ext1,
      simp only [minor₁, coe_comp', coe_restrict_scalars', w,
                 function.comp_app, continuous_linear_map.zero_apply], }, },
  { exact λ h, ⟨is_complex_or_conj_complex_linear h, h.ne_zero⟩, },
end

end conformal_into_complex_plane
