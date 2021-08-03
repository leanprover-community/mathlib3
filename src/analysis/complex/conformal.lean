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

section into_complex_normed_space

variables {E : Type*} [normed_group E] [normed_space ℝ E] [normed_space ℂ E]
  [is_scalar_tower ℝ ℂ E] {z : ℂ} {f : ℂ → E}

/-- A real differentiable function of the complex plane into some complex normed space `E` is
    conformal at a point `z` if it is holomorphic or antiholomorphic at that point -/
lemma conformal_at_of_holomorph_or_antiholomorph_at
  (hf : differentiable_at ℝ f z) (hf' : fderiv ℝ f z ≠ 0)
  (h : differentiable_at ℂ f z ∨ differentiable_at ℂ (f ∘ conj) (conj z)) :
  conformal_at f z :=
begin
  rw [conformal_at_iff_is_conformal_map_fderiv],
  cases h with h₁ h₂,
  { rw [differentiable_at_iff_exists_linear_map ℝ hf] at h₁;
       [skip, apply_instance, apply_instance, apply_instance],
    rcases h₁ with ⟨map, hmap⟩,
    rw ← hmap,
    refine is_conformal_map_complex_linear _,
    contrapose! hf' with w,
    ext1,
    simp only [← hmap, coe_restrict_scalars', w, continuous_linear_map.zero_apply], },
  { rw [antiholomorph_at_iff_exists_complex_linear_conj hf] at h₂,
    rcases h₂ with ⟨map, hmap⟩,
    have minor₁ : fderiv ℝ f z = (map.restrict_scalars ℝ).comp conj_cle.to_continuous_linear_map,
    { ext1,
      rw hmap,
      simp only [coe_comp', function.comp_app, conj_cle.coe_def_rev, conj_cle.coe_coe,
                 conj_cle_apply, conj_conj], },
    rw minor₁,
    refine is_conformal_map_complex_linear_conj _,
    contrapose! hf' with w,
    rw minor₁,
    ext1,
    simp only [coe_comp', function.comp_app, conj_cle.coe_def_rev, conj_cle.coe_coe,
               conj_cle_apply, coe_restrict_scalars', w, continuous_linear_map.zero_apply], },
end

end into_complex_normed_space

section into_the_complex_plane

variables {f : ℂ → ℂ} {z : ℂ}

lemma conformal_at_iff_holomorphic_or_antiholomorph_at_aux (hf : differentiable_at ℝ f z) :
  conformal_at f z ↔
  (differentiable_at ℂ f z ∨ differentiable_at ℂ (f ∘ conj) (conj z)) ∧ fderiv ℝ f z ≠ 0 :=
by rw [conformal_at_iff_is_conformal_map_fderiv,
       ← is_complex_or_conj_complex_linear_iff_is_conformal_map,
       differentiable_at_iff_exists_linear_map ℝ hf,
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

end into_the_complex_plane
