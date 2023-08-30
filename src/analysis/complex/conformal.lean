/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
import analysis.complex.isometry
import analysis.normed_space.conformal_linear_map
import analysis.normed_space.finite_dimension

/-!
# Conformal maps between complex vector spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
open_locale complex_conjugate

lemma is_conformal_map_conj : is_conformal_map (conj_lie : ℂ →L[ℝ] ℂ) :=
conj_lie.to_linear_isometry.is_conformal_map

section conformal_into_complex_normed

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [normed_space ℂ E]
  {z : ℂ} {g : ℂ →L[ℝ] E} {f : ℂ → E}

lemma is_conformal_map_complex_linear {map : ℂ →L[ℂ] E} (nonzero : map ≠ 0) :
  is_conformal_map (map.restrict_scalars ℝ) :=
begin
  have minor₁ : ‖map 1‖ ≠ 0,
  { simpa only [ext_ring_iff, ne.def, norm_eq_zero] using nonzero},
  refine ⟨‖map 1‖, minor₁, ⟨‖map 1‖⁻¹ • map, _⟩, _⟩,
  { intros x,
    simp only [linear_map.smul_apply],
    have : x = x • 1 := by rw [smul_eq_mul, mul_one],
    nth_rewrite 0 [this],
    rw [_root_.coe_coe map, linear_map.coe_coe_is_scalar_tower],
    simp only [map.coe_coe, map.map_smul, norm_smul, norm_inv, norm_norm],
    field_simp only [one_mul] },
  { ext1,
    simp only [minor₁, linear_map.smul_apply, _root_.coe_coe, linear_map.coe_coe_is_scalar_tower,
      continuous_linear_map.coe_coe, coe_restrict_scalars', coe_smul',
      linear_isometry.coe_to_continuous_linear_map, linear_isometry.coe_mk, pi.smul_apply,
      smul_inv_smul₀, ne.def, not_false_iff] },
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
  rcases h with ⟨c, hc, li, rfl⟩,
  obtain ⟨li, rfl⟩ : ∃ li' : ℂ ≃ₗᵢ[ℝ] ℂ, li'.to_linear_isometry = li,
    from ⟨li.to_linear_isometry_equiv rfl, by { ext1, refl }⟩,
  rcases linear_isometry_complex li with ⟨a, rfl|rfl⟩,
  -- let rot := c • (a : ℂ) • continuous_linear_map.id ℂ ℂ,
  { refine or.inl ⟨c • (a : ℂ) • continuous_linear_map.id ℂ ℂ, _⟩,
    ext1,
    simp only [coe_restrict_scalars', smul_apply, linear_isometry.coe_to_continuous_linear_map,
      linear_isometry_equiv.coe_to_linear_isometry, rotation_apply, id_apply, smul_eq_mul] },
  { refine or.inr ⟨c • (a : ℂ) • continuous_linear_map.id ℂ ℂ, _⟩,
    ext1,
    simp only [coe_restrict_scalars', smul_apply, linear_isometry.coe_to_continuous_linear_map,
      linear_isometry_equiv.coe_to_linear_isometry, rotation_apply, id_apply, smul_eq_mul,
      comp_apply, linear_isometry_equiv.trans_apply, continuous_linear_equiv.coe_coe,
      conj_cle_apply, conj_lie_apply, conj_conj] },
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
      simp only [w, restrict_scalars_zero]},
    { have minor₁ : g = (map.restrict_scalars ℝ) ∘L ↑conj_cle,
      { ext1,
        simp only [hmap, coe_comp', continuous_linear_equiv.coe_coe, function.comp_app,
          conj_cle_apply, star_ring_end_self_apply]},
      rw minor₁ at ⊢ h₂,
      refine is_conformal_map_complex_linear_conj _,
      contrapose! h₂ with w,
      simp only [w, restrict_scalars_zero, zero_comp]} }
end

end conformal_into_complex_plane
