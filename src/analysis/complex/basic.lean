/-
Copyright (c) Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.calculus.deriv
import analysis.normed_space.finite_dimension

/-!
# Normed space structure on `ℂ`.

This file gathers basic facts on complex numbers of an analytic nature.

## Main results

This file registers `ℂ` as a normed field, expresses basic properties of the norm, and gives
tools on the real vector space structure of `ℂ`. Notably, in the namespace `complex`,
it defines functions:

* `linear_map.re`
* `continuous_linear_map.re`
* `linear_map.im`
* `continuous_linear_map.im`
* `linear_map.of_real`
* `continuous_linear_map.of_real`

They are bundled versions of the real part, the imaginary part, and the embedding of `ℝ` in `ℂ`,
as `ℝ`-linear maps.

`has_deriv_at_real_of_complex` expresses that, if a function on `ℂ` is differentiable (over `ℂ`),
then its restriction to `ℝ` is differentiable over `ℝ`, with derivative the real part of the
complex derivative.
-/
noncomputable theory


namespace complex

instance : normed_field ℂ :=
{ norm := abs,
  dist_eq := λ _ _, rfl,
  norm_mul' := abs_mul,
  .. complex.field }

instance : nondiscrete_normed_field ℂ :=
{ non_trivial := ⟨2, by simp [norm]; norm_num⟩ }

instance normed_algebra_over_reals : normed_algebra ℝ ℂ :=
{ norm_algebra_map_eq := abs_of_real,
  ..complex.algebra_over_reals }

@[simp] lemma norm_eq_abs (z : ℂ) : ∥z∥ = abs z := rfl

@[simp] lemma norm_real (r : ℝ) : ∥(r : ℂ)∥ = ∥r∥ := abs_of_real _

@[simp] lemma norm_rat (r : ℚ) : ∥(r : ℂ)∥ = _root_.abs (r : ℝ) :=
suffices ∥((r : ℝ) : ℂ)∥ = _root_.abs r, by simpa,
by rw [norm_real, real.norm_eq_abs]

@[simp] lemma norm_nat (n : ℕ) : ∥(n : ℂ)∥ = n := abs_of_nat _

@[simp] lemma norm_int {n : ℤ} : ∥(n : ℂ)∥ = _root_.abs n :=
suffices ∥((n : ℝ) : ℂ)∥ = _root_.abs n, by simpa,
by rw [norm_real, real.norm_eq_abs]

lemma norm_int_of_nonneg {n : ℤ} (hn : 0 ≤ n) : ∥(n : ℂ)∥ = n :=
by rw [norm_int, _root_.abs_of_nonneg]; exact int.cast_nonneg.2 hn

/-- Over the complex numbers, any finite-dimensional spaces is proper (and therefore complete).
We can register this as an instance, as it will not cause problems in instance resolution since
the properness of `ℂ` is already known and there is no metavariable. -/
instance finite_dimensional.proper
  (E : Type) [normed_group E] [normed_space ℂ E] [finite_dimensional ℂ E] : proper_space E :=
finite_dimensional.proper ℂ E
attribute [instance, priority 900] complex.finite_dimensional.proper

/-- A complex normed vector space is also a real normed vector space. -/
instance normed_space.restrict_scalars_real (E : Type*) [normed_group E] [normed_space ℂ E] :
  normed_space ℝ E := normed_space.restrict_scalars ℝ ℂ
attribute [instance, priority 900] complex.normed_space.restrict_scalars_real

/-- Linear map version of the real part function, from `ℂ` to `ℝ`. -/
def linear_map.re : ℂ →ₗ[ℝ] ℝ :=
{ to_fun := λx, x.re,
  map_add' := by simp,
  map_smul' := λc x, by { change ((c : ℂ) * x).re = c * x.re, simp } }

@[simp] lemma linear_map.re_apply (z : ℂ) : linear_map.re z = z.re := rfl

/-- Continuous linear map version of the real part function, from `ℂ` to `ℝ`. -/
def continuous_linear_map.re : ℂ →L[ℝ] ℝ :=
linear_map.re.mk_continuous 1 $ λx, begin
  change _root_.abs (x.re) ≤ 1 * abs x,
  rw one_mul,
  exact abs_re_le_abs x
end

@[simp] lemma continuous_linear_map.re_coe :
  (coe (continuous_linear_map.re) : ℂ →ₗ[ℝ] ℝ) = linear_map.re := rfl

@[simp] lemma continuous_linear_map.re_apply (z : ℂ) :
  (continuous_linear_map.re : ℂ → ℝ) z = z.re := rfl

@[simp] lemma continuous_linear_map.re_norm :
  ∥continuous_linear_map.re∥ = 1 :=
begin
  apply le_antisymm (linear_map.mk_continuous_norm_le _ zero_le_one _),
  calc 1 = ∥continuous_linear_map.re (1 : ℂ)∥ : by simp
    ... ≤ ∥continuous_linear_map.re∥ : by { apply continuous_linear_map.unit_le_op_norm, simp }
end

/-- Linear map version of the imaginary part function, from `ℂ` to `ℝ`. -/
def linear_map.im : ℂ →ₗ[ℝ] ℝ :=
{ to_fun := λx, x.im,
  map_add' := by simp,
  map_smul' := λc x, by { change ((c : ℂ) * x).im = c * x.im, simp } }

@[simp] lemma linear_map.im_apply (z : ℂ) : linear_map.im z = z.im := rfl

/-- Continuous linear map version of the real part function, from `ℂ` to `ℝ`. -/
def continuous_linear_map.im : ℂ →L[ℝ] ℝ :=
linear_map.im.mk_continuous 1 $ λx, begin
  change _root_.abs (x.im) ≤ 1 * abs x,
  rw one_mul,
  exact complex.abs_im_le_abs x
end

@[simp] lemma continuous_linear_map.im_coe :
  (coe (continuous_linear_map.im) : ℂ →ₗ[ℝ] ℝ) = linear_map.im := rfl

@[simp] lemma continuous_linear_map.im_apply (z : ℂ) :
  (continuous_linear_map.im : ℂ → ℝ) z = z.im := rfl

@[simp] lemma continuous_linear_map.im_norm :
  ∥continuous_linear_map.im∥ = 1 :=
begin
  apply le_antisymm (linear_map.mk_continuous_norm_le _ zero_le_one _),
  calc 1 = ∥continuous_linear_map.im (I : ℂ)∥ : by simp
    ... ≤ ∥continuous_linear_map.im∥ :
      by { apply continuous_linear_map.unit_le_op_norm, rw ← abs_I, exact le_refl _ }
end

/-- Linear map version of the canonical embedding of `ℝ` in `ℂ`. -/
def linear_map.of_real : ℝ →ₗ[ℝ] ℂ :=
{ to_fun := λx, of_real x,
  map_add' := by simp,
  map_smul' := λc x, by { simp, refl } }

@[simp] lemma linear_map.of_real_apply (x : ℝ) : linear_map.of_real x = x := rfl

/-- Continuous linear map version of the canonical embedding of `ℝ` in `ℂ`. -/
def continuous_linear_map.of_real : ℝ →L[ℝ] ℂ :=
linear_map.of_real.mk_continuous 1 $ λx, by simp

@[simp] lemma continuous_linear_map.of_real_coe :
  (coe (continuous_linear_map.of_real) : ℝ →ₗ[ℝ] ℂ) = linear_map.of_real := rfl

@[simp] lemma continuous_linear_map.of_real_apply (x : ℝ) :
  (continuous_linear_map.of_real : ℝ → ℂ) x = x := rfl

@[simp] lemma continuous_linear_map.of_real_norm :
  ∥continuous_linear_map.of_real∥ = 1 :=
begin
  apply le_antisymm (linear_map.mk_continuous_norm_le _ zero_le_one _),
  calc 1 = ∥continuous_linear_map.of_real (1 : ℝ)∥ : by simp
    ... ≤ ∥continuous_linear_map.of_real∥ :
      by { apply continuous_linear_map.unit_le_op_norm, simp }
end

lemma continuous_linear_map.of_real_isometry :
  isometry continuous_linear_map.of_real :=
continuous_linear_map.isometry_iff_norm_image_eq_norm.2 (λx, by simp)

end complex

section real_deriv_of_complex
/-! ### Differentiability of the restriction to `ℝ` of complex functions -/
open complex
variables {e : ℂ → ℂ} {e' : ℂ} {z : ℝ}

/--
A preliminary lemma for `has_deriv_at_real_of_complex`,
which we only separate out to keep the maximum compile time per declaration low.
-/
lemma has_deriv_at_real_of_complex_aux (h : has_deriv_at e e' z) :
  has_deriv_at (⇑continuous_linear_map.re ∘ λ {z : ℝ}, e (continuous_linear_map.of_real z))
    (((continuous_linear_map.re.comp
       ((continuous_linear_map.smul_right (1 : ℂ →L[ℂ] ℂ) e').restrict_scalars ℝ)).comp
         continuous_linear_map.of_real) (1 : ℝ))
    z :=
begin
  have A : has_fderiv_at continuous_linear_map.of_real continuous_linear_map.of_real z :=
    continuous_linear_map.of_real.has_fderiv_at,
  have B : has_fderiv_at e ((continuous_linear_map.smul_right 1 e' : ℂ →L[ℂ] ℂ).restrict_scalars ℝ)
    (continuous_linear_map.of_real z) :=
    (has_deriv_at_iff_has_fderiv_at.1 h).restrict_scalars ℝ,
  have C : has_fderiv_at continuous_linear_map.re continuous_linear_map.re
    (e (continuous_linear_map.of_real z)) := continuous_linear_map.re.has_fderiv_at,
  exact has_fderiv_at_iff_has_deriv_at.1 (C.comp z (B.comp z A)),
end

/-- If a complex function is differentiable at a real point, then the induced real function is also
differentiable at this point, with a derivative equal to the real part of the complex derivative. -/
theorem has_deriv_at_real_of_complex (h : has_deriv_at e e' z) :
  has_deriv_at (λx:ℝ, (e x).re) e'.re z :=
begin
  rw (show (λx:ℝ, (e x).re) = (continuous_linear_map.re : ℂ → ℝ) ∘ e ∘ (continuous_linear_map.of_real : ℝ → ℂ),
    by { ext x, refl }),
  simpa using has_deriv_at_real_of_complex_aux h,
end

end real_deriv_of_complex
