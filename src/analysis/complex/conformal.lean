/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
import analysis.complex.isometry
import analysis.complex.real_deriv
import analysis.calculus.conformal

/-!
# Complex Conformal Maps

We prove the sufficient and necessary conditions for a complex function to be conformal.

## Main results

* `is_complex_or_conj_complex_linear_iff_is_conformal_map`: the main theorem for linear maps.
* `conformal_at_iff_holomorphic_or_antiholomorphic_at`: the main theorem for complex functions.

## Warning

Antiholomorphic functions such as the complex conjugate are considered as conformal functions in
this file.
-/

noncomputable theory

open complex linear_isometry linear_isometry_equiv continuous_linear_map
     finite_dimensional linear_map

section complex_normed_space

variables {E : Type*} [normed_group E] [normed_space ℝ E] [normed_space ℂ E]
  [is_scalar_tower ℝ ℂ E] {z : ℂ} {g : ℂ →L[ℝ] E} {f : ℂ → E}

lemma differentiable_at_iff_exists_linear_map (hf : differentiable_at ℝ f z) :
  differentiable_at ℂ f z ↔ ∃ (g' : ℂ →L[ℂ] E), g'.restrict_scalars ℝ = fderiv ℝ f z :=
sorry

lemma antiholomorph_at_iff_exists_complex_linear_conj (hf : differentiable_at ℝ f z) :
  differentiable_at ℂ (f ∘ conj) (conj z) ↔
  ∃ (g' : ℂ →L[ℂ] E), g'.restrict_scalars ℝ =
  (fderiv ℝ f z).comp conj_cle.to_continuous_linear_map :=
sorry

lemma is_conformal_map_of_eq_complex_linear (nonzero : g ≠ 0)
  (H : ∃ (map : ℂ →L[ℂ] E), map.restrict_scalars ℝ = g) : is_conformal_map g :=
begin
  rcases H with ⟨map, h⟩,
  have minor₀ : ∀ x, g x = x • g 1,
  { intro x,
    nth_rewrite 0 ← mul_one x,
    rw [← smul_eq_mul, ← h, coe_restrict_scalars', map.map_smul], },
  have minor₁ : ∥g 1∥ ≠ 0,
  { contrapose! nonzero with w,
    ext1 x,
    rw [continuous_linear_map.zero_apply, minor₀ x, norm_eq_zero.mp w, smul_zero], },
  refine ⟨∥g 1∥, minor₁, _⟩,
  let li' := ∥g 1∥⁻¹ • g,
  have key : ∀ (x : ℂ), ∥li' x∥ = ∥x∥,
  { intros x,
    simp only [li', continuous_linear_map.smul_apply, minor₀ x,
               norm_smul, normed_field.norm_inv, norm_norm],
    field_simp [minor₁], },
  let li : ℂ →ₗᵢ[ℝ] E := ⟨li', key⟩,
  have minor₂ : (li : ℂ → E) = li' := rfl,
  refine ⟨li, _⟩,
  ext1,
  simp only [minor₂, li', pi.smul_apply, continuous_linear_map.smul_apply, smul_smul],
  field_simp [minor₁],
end

lemma is_conformal_map_of_eq_linear_conj (nonzero : g ≠ 0)
  (h : ∃ (map : ℂ →L[ℂ] E), map.restrict_scalars ℝ = g.comp conj_cle.to_continuous_linear_map) :
  is_conformal_map g :=
begin
  have nonzero' : g.comp conj_cle.to_continuous_linear_map ≠ 0,
  { contrapose! nonzero with w,
    simp only [continuous_linear_map.ext_iff, continuous_linear_map.zero_apply,
               continuous_linear_map.coe_comp', function.comp_app,
               continuous_linear_equiv.coe_def_rev, continuous_linear_equiv.coe_apply,
               conj_cle_apply] at w,
    ext1,
    rw [← conj_conj x, w, continuous_linear_map.zero_apply], },
  rcases is_conformal_map_of_eq_complex_linear nonzero' h with ⟨c, hc, li, hg'⟩,
  refine ⟨c, hc, li.comp conj_lie.to_linear_isometry, _⟩,
  have key : (g : ℂ → E) = (c • li) ∘ conj_lie,
  { rw ← hg',
    funext,
    simp only [continuous_linear_map.coe_comp',function.comp_app,
               continuous_linear_equiv.coe_def_rev, continuous_linear_equiv.coe_apply,
               conj_lie_apply, conj_cle_apply, conj_conj], },
  funext,
  simp only [conj_cle_apply, pi.smul_apply,
             linear_isometry.coe_comp, coe_to_linear_isometry],
  rw [key, function.comp_app, pi.smul_apply],
end

/-- A real differentiable function of the complex plane into some complex normed space `E` is
    conformal at a point `z` if it is holomorphic or antiholomorphic at that point -/
lemma conformal_at_of_holomorph_or_antiholomorph_at_aux
  (hf : differentiable_at ℝ f z) (hf' : fderiv ℝ f z ≠ 0)
  (h : differentiable_at ℂ f z ∨ differentiable_at ℂ (f ∘ conj) (conj z)) :
  conformal_at f z :=
begin
  rw [conformal_at_iff_is_conformal_map_fderiv],
  rw [differentiable_at_iff_exists_linear_map hf,
      antiholomorph_at_iff_exists_complex_linear_conj hf] at h,
  cases h,
  { exact is_conformal_map_of_eq_complex_linear hf' h, },
  { exact is_conformal_map_of_eq_linear_conj hf' h, },
end

end complex_normed_space

section complex_conformal_linear_map

variables {f : ℂ → ℂ} {z : ℂ} {g : ℂ →L[ℝ] ℂ}

lemma is_complex_or_conj_complex_linear (h : is_conformal_map g) :
  (∃ (map : ℂ →L[ℂ] ℂ), map.restrict_scalars ℝ = g) ∨
  (∃ (map : ℂ →L[ℂ] ℂ), map.restrict_scalars ℝ = g.comp conj_cle.to_continuous_linear_map) :=
begin
  rcases h with ⟨c, hc, li, hg⟩,
  rcases linear_isometry_complex (li.to_linear_isometry_equiv rfl) with ⟨a, ha⟩,
  cases ha,
  { refine or.intro_left _ ⟨c • rotation_clm a, _⟩,
    ext1,
    simp only [coe_restrict_scalars', continuous_linear_map.smul_apply, coe_rotation_clm, ← ha,
               li.coe_to_linear_isometry_equiv, hg, pi.smul_apply], },
  { let map := c • (rotation_clm a),
    refine or.intro_right _ ⟨map, _⟩,
    ext1,
    rw [continuous_linear_map.coe_comp', hg, ← li.coe_to_linear_isometry_equiv, ha],
    simp only [coe_restrict_scalars', function.comp_app, pi.smul_apply,
               linear_isometry_equiv.coe_trans, conj_lie_apply,
               rotation_apply, map, continuous_linear_equiv.coe_def_rev,
               continuous_linear_equiv.coe_apply, conj_cle_apply],
    simp only [smul_coe, smul_eq_mul, function.comp_app, continuous_linear_map.smul_apply,
               rotation_clm_apply, linear_map.coe_to_continuous_linear_map',
               rotation_apply, conj.map_mul, conj_conj], },
end

/-- A real continuous linear map on the complex plane is conformal if and only if the map or its
    conjugate is complex linear, and the map is nonvanishing. -/
lemma is_complex_or_conj_complex_linear_iff_is_conformal_map :
  ((∃ (map : ℂ →L[ℂ] ℂ), map.restrict_scalars ℝ = g) ∨
   (∃ (map : ℂ →L[ℂ] ℂ), map.restrict_scalars ℝ = g.comp conj_cle.to_continuous_linear_map))
  ∧ g ≠ 0 ↔ is_conformal_map g :=
iff.intro
  (λ h, h.1.rec_on
    (is_conformal_map_of_eq_complex_linear h.2)
    $ is_conformal_map_of_eq_linear_conj h.2)
  (λ h, ⟨is_complex_or_conj_complex_linear h, h.ne_zero⟩)

end complex_conformal_linear_map

section complex_conformal_map

variables {f : ℂ → ℂ} {z : ℂ}

lemma conformal_at_iff_holomorphic_or_antiholomorph_at_aux (hf : differentiable_at ℝ f z) :
  conformal_at f z ↔
  (differentiable_at ℂ f z ∨ differentiable_at ℂ (f ∘ conj) (conj z)) ∧ fderiv ℝ f z ≠ 0 :=
by rw [conformal_at_iff_is_conformal_map_fderiv,
       ← is_complex_or_conj_complex_linear_iff_is_conformal_map,
       differentiable_at_iff_exists_linear_map hf,
       antiholomorph_at_iff_exists_complex_linear_conj hf]

/-- A complex function is conformal if and only if the function is holomorphic or antiholomorphic
    with a nonvanishing differential. -/
lemma conformal_at_iff_holomorphic_or_antiholomorphic_at :
  conformal_at f z ↔
  (differentiable_at ℂ f z ∨ differentiable_at ℂ (f ∘ conj) (conj z)) ∧ fderiv ℝ f z ≠ 0 :=
iff.intro
  (λ h, (conformal_at_iff_holomorphic_or_antiholomorph_at_aux h.differentiable_at).mp h)
  (λ h, by
    { have : differentiable_at ℝ f z :=
        by_contra (λ w, h.2 $ fderiv_zero_of_not_differentiable_at w),
      exact (conformal_at_iff_holomorphic_or_antiholomorph_at_aux this).mpr h, } )

end complex_conformal_map
