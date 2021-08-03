/-
Copyright (c) Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.calculus.times_cont_diff
import analysis.complex.basic
import analysis.calculus.conformal

/-! # Real differentiability of complex-differentiable functions

`has_deriv_at.real_of_complex` expresses that, if a function on `ℂ` is differentiable (over `ℂ`),
then its restriction to `ℝ` is differentiable over `ℝ`, with derivative the real part of the
complex derivative.
-/


section real_deriv_of_complex
/-! ### Differentiability of the restriction to `ℝ` of complex functions -/
open complex
variables {e : ℂ → ℂ} {e' : ℂ} {z : ℝ}

/-- If a complex function is differentiable at a real point, then the induced real function is also
differentiable at this point, with a derivative equal to the real part of the complex derivative. -/
theorem has_strict_deriv_at.real_of_complex (h : has_strict_deriv_at e e' z) :
  has_strict_deriv_at (λx:ℝ, (e x).re) e'.re z :=
begin
  have A : has_strict_fderiv_at (coe : ℝ → ℂ) of_real_clm z := of_real_clm.has_strict_fderiv_at,
  have B : has_strict_fderiv_at e
    ((continuous_linear_map.smul_right 1 e' : ℂ →L[ℂ] ℂ).restrict_scalars ℝ)
    (of_real_clm z) :=
    h.has_strict_fderiv_at.restrict_scalars ℝ,
  have C : has_strict_fderiv_at re re_clm (e (of_real_clm z)) := re_clm.has_strict_fderiv_at,
  simpa using (C.comp z (B.comp z A)).has_strict_deriv_at
end

/-- If a complex function is differentiable at a real point, then the induced real function is also
differentiable at this point, with a derivative equal to the real part of the complex derivative. -/
theorem has_deriv_at.real_of_complex (h : has_deriv_at e e' z) :
  has_deriv_at (λx:ℝ, (e x).re) e'.re z :=
begin
  have A : has_fderiv_at (coe : ℝ → ℂ) of_real_clm z := of_real_clm.has_fderiv_at,
  have B : has_fderiv_at e ((continuous_linear_map.smul_right 1 e' : ℂ →L[ℂ] ℂ).restrict_scalars ℝ)
    (of_real_clm z) :=
    h.has_fderiv_at.restrict_scalars ℝ,
  have C : has_fderiv_at re re_clm (e (of_real_clm z)) := re_clm.has_fderiv_at,
  simpa using (C.comp z (B.comp z A)).has_deriv_at
end

theorem times_cont_diff_at.real_of_complex {n : with_top ℕ} (h : times_cont_diff_at ℂ n e z) :
  times_cont_diff_at ℝ n (λ x : ℝ, (e x).re) z :=
begin
  have A : times_cont_diff_at ℝ n (coe : ℝ → ℂ) z,
    from of_real_clm.times_cont_diff.times_cont_diff_at,
  have B : times_cont_diff_at ℝ n e z := h.restrict_scalars ℝ,
  have C : times_cont_diff_at ℝ n re (e z), from re_clm.times_cont_diff.times_cont_diff_at,
  exact C.comp z (B.comp z A)
end

theorem times_cont_diff.real_of_complex {n : with_top ℕ} (h : times_cont_diff ℂ n e) :
  times_cont_diff ℝ n (λ x : ℝ, (e x).re) :=
times_cont_diff_iff_times_cont_diff_at.2 $ λ x,
  h.times_cont_diff_at.real_of_complex

end real_deriv_of_complex

section complex_fderiv_properties
/-! ### Antiholomorphy and conformality of complex functions -/
open complex continuous_linear_map

variables {E : Type*} [normed_group E] [normed_space ℝ E]
  {z : ℂ} {f : ℂ → E}

lemma has_fderiv_at_conj (z : ℂ) : has_fderiv_at conj conj_cle.to_continuous_linear_map z :=
conj_cle.has_fderiv_at

lemma fderiv_conj_eq_conj_fderiv {z : ℂ} (h : differentiable_at ℝ f z) :
  (fderiv ℝ f z).comp conj_cle.to_continuous_linear_map = fderiv ℝ (f ∘ conj) (conj z) :=
begin
  rw ← conj_conj z at h,
  let p := fderiv.comp (conj z) h (has_fderiv_at_conj $ conj z).differentiable_at,
  rw [conj_conj, (has_fderiv_at_conj $ conj z).fderiv] at p,
  exact p.symm,
end

variables [normed_space ℂ E] [is_scalar_tower ℝ ℂ E]

/-- A (real-differentiable) complex function `f` is antiholomorphic if and only if there exists some
    complex linear map `g'` that equals to the composition of `f`'s differential and the conjugate
    function -/
lemma antiholomorph_at_iff_exists_complex_linear_conj
  (hf : differentiable_at ℝ f z) : differentiable_at ℂ (f ∘ conj) (conj z) ↔
  ∃ (g' : ℂ →L[ℂ] E), g'.restrict_scalars ℝ =
  (fderiv ℝ f z).comp conj_cle.to_continuous_linear_map :=
begin
  split,
  { intros h,
    rw ← conj_conj z at hf,
    rcases (differentiable_at_iff_exists_linear_map ℝ $
      hf.comp (conj z) (has_fderiv_at_conj $ conj z).differentiable_at).mp h with ⟨f', hf'⟩,
    rw conj_conj at hf,
    rw ← fderiv_conj_eq_conj_fderiv hf at hf',
    exact ⟨f', hf'⟩, },
  { rintros ⟨g', hg'⟩,
    rw ← conj_conj z at hf hg',
    exact ⟨g', has_fderiv_at_of_eq ℝ
      (hf.has_fderiv_at.comp (conj z) $ has_fderiv_at_conj $ conj z) hg'⟩, },
end

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

end complex_fderiv_properties
