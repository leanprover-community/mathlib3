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

* `conformal_at_iff_holomorphic_or_antiholomorphic_at`: the main theorem for complex functions.

## Warning

Antiholomorphic functions such as the complex conjugate are considered as conformal functions in
this file.
-/

noncomputable theory

section complex_conformal_map

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

end complex_conformal_map
