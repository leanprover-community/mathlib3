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

* `is_complex_or_conj_complex_linear_iff_is_conformal_map`: the main theorem for linear maps.
* `conformal_at_iff_holomorphic_or_antiholomorph`: the main theorem for complex functions.

## Warning

Antiholomorphic functions such as the complex conjugate are considered as conformal functions in
this file.
-/

noncomputable theory

section complex_conformal_linear_map

variables {f : ℂ → ℂ} {z : ℂ} {g : ℂ →L[ℝ] ℂ}

open complex linear_isometry linear_isometry_equiv continuous_linear_map
     finite_dimensional linear_map

lemma is_complex_linear_iff_holomorph (hf : differentiable_at ℝ f z) :
  differentiable_at ℂ f z ↔ is_linear_map ℂ (fderiv ℝ f z) :=
sorry

lemma is_conj_complex_linear_iff_antiholomorph (hf : differentiable_at ℝ f z) :
  differentiable_at ℂ (conj ∘ f) z ↔ is_linear_map ℂ (conj ∘ (fderiv ℝ f z)) :=
sorry

lemma is_conformal_map_of_complex_linear (nonzero : g ≠ 0)
  (h : is_linear_map ℂ g) : is_conformal_map g :=
begin
  have minor₀ : ∀ x, g x = x • g 1,
  { intro x,
    nth_rewrite 0 ← mul_one x,
    rw [← smul_eq_mul, h.map_smul], },
  have minor₁ : ∥g 1∥ ≠ 0,
  { contrapose! nonzero with w,
    ext1 x,
    rw [continuous_linear_map.zero_apply, minor₀ x, norm_eq_zero.mp w, smul_zero], },
  have minor₂ : complex.abs ((g 1) / ∥g 1∥) = 1,
  { rw [complex.abs_div, abs_of_real, ← norm_eq_abs, abs_norm_eq_norm, div_self minor₁], },
  have minor₃ : (∥g 1∥ : ℂ) ≠ 0 := of_real_ne_zero.mpr minor₁,
  let rot := rotation ⟨(g 1) / ∥g 1∥, (mem_circle_iff_abs _).mpr minor₂⟩,
  have key : (g : ℂ → ℂ) = ∥g 1∥ • rot,
  { funext x,
    rw [pi.smul_apply, rotation_apply, minor₀ x,
        smul_eq_mul, set_like.coe_mk, smul_coe,
        ← mul_assoc, mul_div_cancel' _ minor₃, mul_comm], },
  exact ⟨∥g 1∥, minor₁, rot.to_linear_isometry, key⟩,
end

lemma is_conformal_map_of_conj_linear (nonzero : g ≠ 0)
  (h : is_linear_map ℂ (conj ∘ g)) : is_conformal_map g :=
begin
  have nonzero' : conj_cle.to_continuous_linear_map.comp g ≠ 0,
  { contrapose! nonzero with w,
    simp only [continuous_linear_map.ext_iff, continuous_linear_map.zero_apply,
               continuous_linear_map.coe_comp', function.comp_app,
               continuous_linear_equiv.coe_def_rev, continuous_linear_equiv.coe_apply,
               conj_cle_apply, conj_eq_zero] at w,
    exact continuous_linear_map.ext w, },
  rcases is_conformal_map_of_complex_linear nonzero' h with ⟨c, hc, li, hg'⟩,
  refine ⟨c, hc, conj_lie.to_linear_isometry.comp li, _⟩,
  have key : (g : ℂ → ℂ) = conj_lie ∘ (c • li),
  { rw ← hg',
    funext,
    simp only [continuous_linear_map.coe_comp',function.comp_app,
               continuous_linear_equiv.coe_def_rev, continuous_linear_equiv.coe_apply,
               conj_lie_apply, conj_cle_apply, conj_conj], },
  funext,
  simp only [function.comp_app, conj_cle_apply, pi.smul_apply,
             linear_isometry.coe_comp, coe_to_linear_isometry],
  rw [key, function.comp_app, pi.smul_apply],
  exact conj_lie.map_smul' c (li x),
end

lemma is_complex_or_conj_complex_linear (h : is_conformal_map g) :
  is_linear_map ℂ g ∨ is_linear_map ℂ (conj ∘ g) :=
begin
  rcases h with ⟨c, hc, li, hg⟩,
  rcases linear_isometry_complex (li.to_linear_isometry_equiv rfl) with ⟨a, ha⟩,
  cases ha,
  { have : is_linear_map ℂ g :=
    { map_add := g.map_add,
      map_smul := λ c₁ x₁, by { rw [hg, ← li.coe_to_linear_isometry_equiv, ha],
        simp only [pi.smul_apply, rotation_apply, smul_eq_mul, smul_coe], ring, }, },
    exact or.intro_left _ this, },
  { let map := (conj c) • (rotation_clm a⁻¹),
    have : conj ∘ g = map,
    { funext,
      rw [hg, ← li.coe_to_linear_isometry_equiv, ha],
      simp only [function.comp_app, pi.smul_apply, linear_isometry_equiv.coe_trans,
                 conj_lie_apply, rotation_apply, map],
      simp only [smul_coe, smul_eq_mul, function.comp_app, continuous_linear_map.smul_apply,
                 rotation_clm_apply, linear_map.coe_to_continuous_linear_map',
                 rotation_apply, conj.map_mul, coe_inv_circle_eq_conj, conj_conj], },
    rw this,
    exact or.intro_right _ map.to_linear_map.is_linear, },
end

/-- A real continuous linear map is conformal if and only if the map or its conjugate is complex
    linear, and the map is nonvanishing. -/
lemma is_complex_or_conj_complex_linear_iff_is_conformal_map :
  (is_linear_map ℂ g ∨ is_linear_map ℂ (conj ∘ g)) ∧ g ≠ 0 ↔ is_conformal_map g :=
iff.intro
  (λ h, h.1.rec_on (is_conformal_map_of_complex_linear h.2) (is_conformal_map_of_conj_linear h.2))
  (λ h, ⟨is_complex_or_conj_complex_linear h, h.ne_zero⟩)

lemma conformal_at_iff_holomorphic_or_antiholomorph_aux (hf : differentiable_at ℝ f z) :
  conformal_at f z ↔
  (differentiable_at ℂ f z ∨ differentiable_at ℂ (conj ∘ f) z) ∧ fderiv ℝ f z ≠ 0 :=
by rw [conformal_at_iff_is_conformal_map_fderiv,
      ← is_complex_or_conj_complex_linear_iff_is_conformal_map,
      is_complex_linear_iff_holomorph hf, is_conj_complex_linear_iff_antiholomorph hf]

/-- A complex function is conformal if and only if the function is holomorphic or antiholomorphic
    with a nonvanishing differential. -/
lemma conformal_at_iff_holomorphic_or_antiholomorphic :
  conformal_at f z ↔
  (differentiable_at ℂ f z ∨ differentiable_at ℂ (conj ∘ f) z) ∧ fderiv ℝ f z ≠ 0 :=
iff.intro
  (λ h, (conformal_at_iff_holomorphic_or_antiholomorph_aux h.differentiable_at).mp h)
  (λ h, by
    { have : differentiable_at ℝ f z :=
        by_contra (λ w, h.2 $ fderiv_zero_of_not_differentiable_at w),
      exact (conformal_at_iff_holomorphic_or_antiholomorph_aux this).mpr h, } )

end complex_conformal_linear_map
