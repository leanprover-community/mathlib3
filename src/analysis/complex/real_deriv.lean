/-
Copyright (c) Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.calculus.times_cont_diff
import analysis.complex.basic

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
