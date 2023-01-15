/-
Copyright (c) Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yourong Zang
-/
import analysis.calculus.cont_diff
import analysis.complex.conformal
import analysis.calculus.conformal.normed_space

/-! # Real differentiability of complex-differentiable functions

`has_deriv_at.real_of_complex` expresses that, if a function on `ℂ` is differentiable (over `ℂ`),
then its restriction to `ℝ` is differentiable over `ℝ`, with derivative the real part of the
complex derivative.

`differentiable_at.conformal_at` states that a real-differentiable function with a nonvanishing
differential from the complex plane into an arbitrary complex-normed space is conformal at a point
if it's holomorphic at that point. This is a version of Cauchy-Riemann equations.

`conformal_at_iff_differentiable_at_or_differentiable_at_comp_conj` proves that a real-differential
function with a nonvanishing differential between the complex plane is conformal at a point if and
only if it's holomorphic or antiholomorphic at that point.

## TODO

* The classical form of Cauchy-Riemann equations
* On a connected open set `u`, a function which is `conformal_at` each point is either holomorphic
throughout or antiholomorphic throughout.

## Warning

We do NOT require conformal functions to be orientation-preserving in this file.
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

/-- If a complex function `e` is differentiable at a real point, then the function `ℝ → ℝ` given by
the real part of `e` is also differentiable at this point, with a derivative equal to the real part
of the complex derivative. -/
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

theorem cont_diff_at.real_of_complex {n : ℕ∞} (h : cont_diff_at ℂ n e z) :
  cont_diff_at ℝ n (λ x : ℝ, (e x).re) z :=
begin
  have A : cont_diff_at ℝ n (coe : ℝ → ℂ) z,
    from of_real_clm.cont_diff.cont_diff_at,
  have B : cont_diff_at ℝ n e z := h.restrict_scalars ℝ,
  have C : cont_diff_at ℝ n re (e z), from re_clm.cont_diff.cont_diff_at,
  exact C.comp z (B.comp z A)
end

theorem cont_diff.real_of_complex {n : ℕ∞} (h : cont_diff ℂ n e) :
  cont_diff ℝ n (λ x : ℝ, (e x).re) :=
cont_diff_iff_cont_diff_at.2 $ λ x,
  h.cont_diff_at.real_of_complex

variables {E : Type*} [normed_add_comm_group E] [normed_space ℂ E]

lemma has_strict_deriv_at.complex_to_real_fderiv' {f : ℂ → E} {x : ℂ} {f' : E}
  (h : has_strict_deriv_at f f' x) :
  has_strict_fderiv_at f (re_clm.smul_right f' + I • im_clm.smul_right f') x :=
by simpa only [complex.restrict_scalars_one_smul_right']
  using h.has_strict_fderiv_at.restrict_scalars ℝ

lemma has_deriv_at.complex_to_real_fderiv' {f : ℂ → E} {x : ℂ} {f' : E} (h : has_deriv_at f f' x) :
  has_fderiv_at f (re_clm.smul_right f' + I • im_clm.smul_right f') x :=
by simpa only [complex.restrict_scalars_one_smul_right']
  using h.has_fderiv_at.restrict_scalars ℝ

lemma has_deriv_within_at.complex_to_real_fderiv' {f : ℂ → E} {s : set ℂ} {x : ℂ} {f' : E}
  (h : has_deriv_within_at f f' s x) :
  has_fderiv_within_at f (re_clm.smul_right f' + I • im_clm.smul_right f') s x :=
by simpa only [complex.restrict_scalars_one_smul_right']
  using h.has_fderiv_within_at.restrict_scalars ℝ

lemma has_strict_deriv_at.complex_to_real_fderiv {f : ℂ → ℂ} {f' x : ℂ}
  (h : has_strict_deriv_at f f' x) :
  has_strict_fderiv_at f (f' • (1 : ℂ →L[ℝ] ℂ)) x :=
by simpa only [complex.restrict_scalars_one_smul_right]
  using h.has_strict_fderiv_at.restrict_scalars ℝ

lemma has_deriv_at.complex_to_real_fderiv {f : ℂ → ℂ} {f' x : ℂ} (h : has_deriv_at f f' x) :
  has_fderiv_at f (f' • (1 : ℂ →L[ℝ] ℂ)) x :=
by simpa only [complex.restrict_scalars_one_smul_right]
  using h.has_fderiv_at.restrict_scalars ℝ

lemma has_deriv_within_at.complex_to_real_fderiv {f : ℂ → ℂ} {s : set ℂ} {f' x : ℂ}
  (h : has_deriv_within_at f f' s x) :
  has_fderiv_within_at f (f' • (1 : ℂ →L[ℝ] ℂ)) s x :=
by simpa only [complex.restrict_scalars_one_smul_right]
  using h.has_fderiv_within_at.restrict_scalars ℝ

/-- If a complex function `e` is differentiable at a real point, then its restriction to `ℝ` is
differentiable there as a function `ℝ → ℂ`, with the same derivative. -/
lemma has_deriv_at.comp_of_real (hf : has_deriv_at e e' ↑z) : has_deriv_at (λ (y:ℝ), e ↑y) e' z :=
by simpa only [of_real_clm_apply, of_real_one, mul_one]
  using hf.comp z of_real_clm.has_deriv_at

/-- If a function `f : ℝ → ℝ` is differentiable at a (real) point `x`, then it is also
differentiable as a function `ℝ → ℂ`. -/
lemma has_deriv_at.of_real_comp {f : ℝ → ℝ} {u : ℝ} (hf : has_deriv_at f u z) :
has_deriv_at (λ (y:ℝ), ↑(f y) : ℝ → ℂ) u z :=
by simpa only [of_real_clm_apply, of_real_one, real_smul, mul_one]
  using of_real_clm.has_deriv_at.scomp z hf

end real_deriv_of_complex

section conformality
/-! ### Conformality of real-differentiable complex maps -/
open complex continuous_linear_map
open_locale complex_conjugate

variables {E : Type*} [normed_add_comm_group E] [normed_space ℂ E] {z : ℂ} {f : ℂ → E}

/-- A real differentiable function of the complex plane into some complex normed space `E` is
    conformal at a point `z` if it is holomorphic at that point with a nonvanishing differential.
    This is a version of the Cauchy-Riemann equations. -/
lemma differentiable_at.conformal_at (h : differentiable_at ℂ f z) (hf' : deriv f z ≠ 0) :
  conformal_at f z :=
begin
  rw [conformal_at_iff_is_conformal_map_fderiv, (h.has_fderiv_at.restrict_scalars ℝ).fderiv],
  apply is_conformal_map_complex_linear,
  simpa only [ne.def, ext_ring_iff]
end

/-- A complex function is conformal if and only if the function is holomorphic or antiholomorphic
    with a nonvanishing differential. -/
lemma conformal_at_iff_differentiable_at_or_differentiable_at_comp_conj {f : ℂ → ℂ} {z : ℂ} :
  conformal_at f z ↔
  (differentiable_at ℂ f z ∨ differentiable_at ℂ (f ∘ conj) (conj z)) ∧ fderiv ℝ f z ≠ 0 :=
begin
  rw conformal_at_iff_is_conformal_map_fderiv,
  rw is_conformal_map_iff_is_complex_or_conj_linear,
  apply and_congr_left,
  intros h,
  have h_diff := h.imp_symm fderiv_zero_of_not_differentiable_at,
  apply or_congr,
  { rw differentiable_at_iff_restrict_scalars ℝ h_diff },
  rw ← conj_conj z at h_diff,
  rw differentiable_at_iff_restrict_scalars ℝ (h_diff.comp _ conj_cle.differentiable_at),
  refine exists_congr (λ g, rfl.congr _),
  have : fderiv ℝ conj (conj z) = _ := conj_cle.fderiv,
  simp [fderiv.comp _ h_diff conj_cle.differentiable_at, this, conj_conj],
end

end conformality
