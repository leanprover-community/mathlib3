/-
Copyright (c) Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.calculus.deriv analysis.normed_space.finite_dimension

/-!
# Basic facts of analytic nature on complex numbers

This file gathers various facts on complex numbers of an analytic nature.

## Main results

This file defines, in the namespace `complex`, functions
* `re_linear_map`
* `re_continuous_linear_map`
* `im_linear_map`
* `im_continuous_linear_map`
* `of_real_linear_map`
* `of_real_continuous_linear_map`

They are bundled versions of the real part, the imaginary part, and the embedding of `ℝ` in `ℂ`.

We also show that, if a function on `ℂ` is differentiable (over `ℂ`), then its restriction to `ℝ`
is differentiable over `ℝ` and express its derivative, in `has_deriv_at_real_of_complex`.
-/
noncomputable theory

set_option class.instance_max_depth 40

namespace complex

instance : normed_field ℂ :=
{ norm := complex.abs,
  dist_eq := λ _ _, rfl,
  norm_mul' := complex.abs_mul,
  .. complex.discrete_field }

instance : nondiscrete_normed_field ℂ :=
{ non_trivial := ⟨2, by simp [norm]; norm_num⟩ }

instance normed_algebra_over_reals : normed_algebra ℝ ℂ :=
{ norm_eq := abs_of_real,
  ..complex.algebra_over_reals }

@[simp] lemma norm_eq_abs (z : ℂ) : ∥z∥ = abs z := rfl

@[simp] lemma norm_real (r : ℝ) : ∥(r : ℂ)∥ = ∥r∥ := complex.abs_of_real _

@[simp] lemma norm_rat (r : ℚ) : ∥(r : ℂ)∥ = _root_.abs (r : ℝ) :=
suffices ∥((r : ℝ) : ℂ)∥ = _root_.abs r, by simpa,
by rw [norm_real, real.norm_eq_abs]

@[simp] lemma norm_nat (n : ℕ) : ∥(n : ℂ)∥ = n := complex.abs_of_nat _

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
def re_linear_map : ℂ →ₗ[ℝ] ℝ :=
{ to_fun := λx, x.re,
  add := by simp,
  smul := λc x, by { change ((c : ℂ) * x).re = c * x.re, simp } }

@[simp] lemma re_linear_map_apply (z : ℂ) : re_linear_map z = z.re := rfl

/-- Continuous linear map version of the real part function, from `ℂ` to `ℝ`. -/
def re_continuous_linear_map : ℂ →L[ℝ] ℝ :=
re_linear_map.with_bound ⟨1, λx, begin
  change _root_.abs (x.re) ≤ 1 * abs x,
  rw one_mul,
  exact complex.abs_re_le_abs x
end⟩

@[simp] lemma re_continuous_linear_map_coe :
  (coe (re_continuous_linear_map) : ℂ →ₗ[ℝ] ℝ) = re_linear_map := rfl

@[simp] lemma re_continuous_linear_map_apply (z : ℂ) :
  (re_continuous_linear_map : ℂ → ℝ) z = z.re := rfl

@[simp] lemma re_continuous_linear_map_norm :
  ∥re_continuous_linear_map∥ = 1 :=
begin
  apply le_antisymm,
  { refine continuous_linear_map.op_norm_le_bound _ (zero_le_one) (λx, _),
    rw one_mul,
    exact complex.abs_re_le_abs x },
  { calc 1 = ∥re_continuous_linear_map (1 : ℂ)∥ : by simp
    ... ≤ ∥re_continuous_linear_map∥ : by { apply continuous_linear_map.unit_le_op_norm, simp } }
end

/-- Linear map version of the imaginary part function, from `ℂ` to `ℝ`. -/
def im_linear_map : ℂ →ₗ[ℝ] ℝ :=
{ to_fun := λx, x.im,
  add := by simp,
  smul := λc x, by { change ((c : ℂ) * x).im = c * x.im, simp } }

@[simp] lemma im_linear_map_apply (z : ℂ) : im_linear_map z = z.im := rfl

/-- Continuous linear map version of the real part function, from `ℂ` to `ℝ`. -/
def im_continuous_linear_map : ℂ →L[ℝ] ℝ :=
im_linear_map.with_bound ⟨1, λx, begin
  change _root_.abs (x.im) ≤ 1 * abs x,
  rw one_mul,
  exact complex.abs_im_le_abs x
end⟩

@[simp] lemma im_continuous_linear_map_coe :
  (coe (im_continuous_linear_map) : ℂ →ₗ[ℝ] ℝ) = im_linear_map := rfl

@[simp] lemma im_continuous_linear_map_apply (z : ℂ) :
  (im_continuous_linear_map : ℂ → ℝ) z = z.im := rfl

@[simp] lemma im_continuous_linear_map_norm :
  ∥im_continuous_linear_map∥ = 1 :=
begin
  apply le_antisymm,
  { refine continuous_linear_map.op_norm_le_bound _ (zero_le_one) (λx, _),
    rw one_mul,
    exact complex.abs_im_le_abs x },
  { calc 1 = ∥im_continuous_linear_map (I : ℂ)∥ : by simp
    ... ≤ ∥im_continuous_linear_map∥ :
      by { apply continuous_linear_map.unit_le_op_norm, rw ← abs_I, exact le_refl _ } }
end

/-- Linear map version of the canonical embedding of `ℝ` in `ℂ`. -/
def of_real_linear_map : ℝ →ₗ[ℝ] ℂ :=
{ to_fun := λx, of_real x,
  add := by simp,
  smul := λc x, by { simp, refl } }

@[simp] lemma of_real_linear_map_apply (x : ℝ) : of_real_linear_map x = x := rfl

/-- Continuous linear map version of the canonical embedding of `ℝ` in `ℂ`. -/
def of_real_continuous_linear_map : ℝ →L[ℝ] ℂ :=
of_real_linear_map.with_bound ⟨1, λx, by simp⟩

@[simp] lemma of_real_continuous_linear_map_coe :
  (coe (of_real_continuous_linear_map) : ℝ →ₗ[ℝ] ℂ) = of_real_linear_map := rfl

@[simp] lemma of_real_continuous_linear_map_apply (x : ℝ) :
  (of_real_continuous_linear_map : ℝ → ℂ) x = x := rfl

@[simp] lemma of_real_continuous_linear_map_norm :
  ∥of_real_continuous_linear_map∥ = 1 :=
begin
  apply le_antisymm,
  { exact continuous_linear_map.op_norm_le_bound _ (zero_le_one) (λx, by simp) },
  { calc 1 = ∥of_real_continuous_linear_map (1 : ℝ)∥ : by simp
    ... ≤ ∥of_real_continuous_linear_map∥ :
      by { apply continuous_linear_map.unit_le_op_norm, simp } }
end

end complex

/- Restriction to `ℝ` of complex functions -/
section real_of_complex
open complex
variables {e : ℂ → ℂ} {e' : ℂ} {z : ℝ}

lemma has_deriv_at_real_of_complex (h : has_deriv_at e e' z) :
  has_deriv_at (λx:ℝ, (e x).re) e'.re z :=
begin
  have : (λx:ℝ, (e x).re) = (re_continuous_linear_map : ℂ → ℝ) ∘ e ∘ (of_real_continuous_linear_map : ℝ → ℂ),
    by { ext x, refl },
  rw this,
  have A : has_fderiv_at of_real_continuous_linear_map of_real_continuous_linear_map z :=
    of_real_continuous_linear_map.has_fderiv_at,
  have B : has_fderiv_at e ((continuous_linear_map.smul_right 1 e' : ℂ →L[ℂ] ℂ).restrict_scalars ℝ)
    (of_real_continuous_linear_map z) :=
    (has_deriv_at_iff_has_fderiv_at.1 h).restrict_scalars ℝ,
  have C : has_fderiv_at re_continuous_linear_map re_continuous_linear_map
    (e (of_real_continuous_linear_map z)) := re_continuous_linear_map.has_fderiv_at,
  convert has_fderiv_at_iff_has_deriv_at.1 (C.comp z (B.comp z A)),
  change e' = 1 * e',
  rw one_mul
end

end real_of_complex
