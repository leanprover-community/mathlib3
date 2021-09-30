/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import analysis.special_functions.exp_log
import data.set.intervals.infinite

/-!
# Trigonometric functions

## Main definitions

This file contains the definition of `π`.

See also `analysis.special_functions.trigonometric.inverse` and
`analysis.special_functions.trigonometric.arctan` for the inverse trigonometric functions.

See also `analysis.special_functions.complex.arg` and
`analysis.special_functions.complex.log` for the complex argument function
and the complex logarithm.

## Main statements

Many basic inequalities on the real trigonometric functions are established.

The continuity and differentiability of the usual trigonometric functions are proved, and their
derivatives are computed.

Several facts about the real trigonometric functions have the proofs deferred to
`analysis.special_functions.trigonometric.complex`,
as they are most easily proved by appealing to the corresponding fact for
complex trigonometric functions.

See also `analysis.special_functions.trigonometric.chebyshev` for the multiple angle formulas
in terms of Chebyshev polynomials.

## Tags

sin, cos, tan, angle
-/

noncomputable theory
open_locale classical topological_space filter
open set filter

namespace complex

/-- The complex sine function is everywhere strictly differentiable, with the derivative `cos x`. -/
lemma has_strict_deriv_at_sin (x : ℂ) : has_strict_deriv_at sin (cos x) x :=
begin
  simp only [cos, div_eq_mul_inv],
  convert ((((has_strict_deriv_at_id x).neg.mul_const I).cexp.sub
    ((has_strict_deriv_at_id x).mul_const I).cexp).mul_const I).mul_const (2:ℂ)⁻¹,
  simp only [function.comp, id],
  rw [sub_mul, mul_assoc, mul_assoc, I_mul_I, neg_one_mul, neg_neg, mul_one, one_mul, mul_assoc,
      I_mul_I, mul_neg_one, sub_neg_eq_add, add_comm]
end

/-- The complex sine function is everywhere differentiable, with the derivative `cos x`. -/
lemma has_deriv_at_sin (x : ℂ) : has_deriv_at sin (cos x) x :=
(has_strict_deriv_at_sin x).has_deriv_at

lemma times_cont_diff_sin {n} : times_cont_diff ℂ n sin :=
(((times_cont_diff_neg.mul times_cont_diff_const).cexp.sub
  (times_cont_diff_id.mul times_cont_diff_const).cexp).mul times_cont_diff_const).div_const

lemma differentiable_sin : differentiable ℂ sin :=
λx, (has_deriv_at_sin x).differentiable_at

lemma differentiable_at_sin {x : ℂ} : differentiable_at ℂ sin x :=
differentiable_sin x

@[simp] lemma deriv_sin : deriv sin = cos :=
funext $ λ x, (has_deriv_at_sin x).deriv

@[continuity]
lemma continuous_sin : continuous sin :=
differentiable_sin.continuous

lemma continuous_on_sin {s : set ℂ} : continuous_on sin s := continuous_sin.continuous_on

/-- The complex cosine function is everywhere strictly differentiable, with the derivative
`-sin x`. -/
lemma has_strict_deriv_at_cos (x : ℂ) : has_strict_deriv_at cos (-sin x) x :=
begin
  simp only [sin, div_eq_mul_inv, neg_mul_eq_neg_mul],
  convert (((has_strict_deriv_at_id x).mul_const I).cexp.add
    ((has_strict_deriv_at_id x).neg.mul_const I).cexp).mul_const (2:ℂ)⁻¹,
  simp only [function.comp, id],
  ring
end

/-- The complex cosine function is everywhere differentiable, with the derivative `-sin x`. -/
lemma has_deriv_at_cos (x : ℂ) : has_deriv_at cos (-sin x) x :=
(has_strict_deriv_at_cos x).has_deriv_at

lemma times_cont_diff_cos {n} : times_cont_diff ℂ n cos :=
((times_cont_diff_id.mul times_cont_diff_const).cexp.add
  (times_cont_diff_neg.mul times_cont_diff_const).cexp).div_const

lemma differentiable_cos : differentiable ℂ cos :=
λx, (has_deriv_at_cos x).differentiable_at

lemma differentiable_at_cos {x : ℂ} : differentiable_at ℂ cos x :=
differentiable_cos x

lemma deriv_cos {x : ℂ} : deriv cos x = -sin x :=
(has_deriv_at_cos x).deriv

@[simp] lemma deriv_cos' : deriv cos = (λ x, -sin x) :=
funext $ λ x, deriv_cos

@[continuity]
lemma continuous_cos : continuous cos :=
differentiable_cos.continuous

lemma continuous_on_cos {s : set ℂ} : continuous_on cos s := continuous_cos.continuous_on

/-- The complex hyperbolic sine function is everywhere strictly differentiable, with the derivative
`cosh x`. -/
lemma has_strict_deriv_at_sinh (x : ℂ) : has_strict_deriv_at sinh (cosh x) x :=
begin
  simp only [cosh, div_eq_mul_inv],
  convert ((has_strict_deriv_at_exp x).sub (has_strict_deriv_at_id x).neg.cexp).mul_const (2:ℂ)⁻¹,
  rw [id, mul_neg_one, sub_eq_add_neg, neg_neg]
end

/-- The complex hyperbolic sine function is everywhere differentiable, with the derivative
`cosh x`. -/
lemma has_deriv_at_sinh (x : ℂ) : has_deriv_at sinh (cosh x) x :=
(has_strict_deriv_at_sinh x).has_deriv_at

lemma times_cont_diff_sinh {n} : times_cont_diff ℂ n sinh :=
(times_cont_diff_exp.sub times_cont_diff_neg.cexp).div_const

lemma differentiable_sinh : differentiable ℂ sinh :=
λx, (has_deriv_at_sinh x).differentiable_at

lemma differentiable_at_sinh {x : ℂ} : differentiable_at ℂ sinh x :=
differentiable_sinh x

@[simp] lemma deriv_sinh : deriv sinh = cosh :=
funext $ λ x, (has_deriv_at_sinh x).deriv

@[continuity]
lemma continuous_sinh : continuous sinh :=
differentiable_sinh.continuous

/-- The complex hyperbolic cosine function is everywhere strictly differentiable, with the
derivative `sinh x`. -/
lemma has_strict_deriv_at_cosh (x : ℂ) : has_strict_deriv_at cosh (sinh x) x :=
begin
  simp only [sinh, div_eq_mul_inv],
  convert ((has_strict_deriv_at_exp x).add (has_strict_deriv_at_id x).neg.cexp).mul_const (2:ℂ)⁻¹,
  rw [id, mul_neg_one, sub_eq_add_neg]
end

/-- The complex hyperbolic cosine function is everywhere differentiable, with the derivative
`sinh x`. -/
lemma has_deriv_at_cosh (x : ℂ) : has_deriv_at cosh (sinh x) x :=
(has_strict_deriv_at_cosh x).has_deriv_at

lemma times_cont_diff_cosh {n} : times_cont_diff ℂ n cosh :=
(times_cont_diff_exp.add times_cont_diff_neg.cexp).div_const

lemma differentiable_cosh : differentiable ℂ cosh :=
λx, (has_deriv_at_cosh x).differentiable_at

lemma differentiable_at_cosh {x : ℂ} : differentiable_at ℂ cos x :=
differentiable_cos x

@[simp] lemma deriv_cosh : deriv cosh = sinh :=
funext $ λ x, (has_deriv_at_cosh x).deriv

@[continuity]
lemma continuous_cosh : continuous cosh :=
differentiable_cosh.continuous

end complex

section
/-! ### Simp lemmas for derivatives of `λ x, complex.cos (f x)` etc., `f : ℂ → ℂ` -/

variables {f : ℂ → ℂ} {f' x : ℂ} {s : set ℂ}

/-! #### `complex.cos` -/

lemma has_strict_deriv_at.ccos (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ x, complex.cos (f x)) (- complex.sin (f x) * f') x :=
(complex.has_strict_deriv_at_cos (f x)).comp x hf

lemma has_deriv_at.ccos (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, complex.cos (f x)) (- complex.sin (f x) * f') x :=
(complex.has_deriv_at_cos (f x)).comp x hf

lemma has_deriv_within_at.ccos (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, complex.cos (f x)) (- complex.sin (f x) * f') s x :=
(complex.has_deriv_at_cos (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_ccos (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  deriv_within (λx, complex.cos (f x)) s x = - complex.sin (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.ccos.deriv_within hxs

@[simp] lemma deriv_ccos (hc : differentiable_at ℂ f x) :
  deriv (λx, complex.cos (f x)) x = - complex.sin (f x) * (deriv f x) :=
hc.has_deriv_at.ccos.deriv

/-! #### `complex.sin` -/

lemma has_strict_deriv_at.csin (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ x, complex.sin (f x)) (complex.cos (f x) * f') x :=
(complex.has_strict_deriv_at_sin (f x)).comp x hf

lemma has_deriv_at.csin (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, complex.sin (f x)) (complex.cos (f x) * f') x :=
(complex.has_deriv_at_sin (f x)).comp x hf

lemma has_deriv_within_at.csin (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, complex.sin (f x)) (complex.cos (f x) * f') s x :=
(complex.has_deriv_at_sin (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_csin (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  deriv_within (λx, complex.sin (f x)) s x = complex.cos (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.csin.deriv_within hxs

@[simp] lemma deriv_csin (hc : differentiable_at ℂ f x) :
  deriv (λx, complex.sin (f x)) x = complex.cos (f x) * (deriv f x) :=
hc.has_deriv_at.csin.deriv

/-! #### `complex.cosh` -/

lemma has_strict_deriv_at.ccosh (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ x, complex.cosh (f x)) (complex.sinh (f x) * f') x :=
(complex.has_strict_deriv_at_cosh (f x)).comp x hf

lemma has_deriv_at.ccosh (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, complex.cosh (f x)) (complex.sinh (f x) * f') x :=
(complex.has_deriv_at_cosh (f x)).comp x hf

lemma has_deriv_within_at.ccosh (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, complex.cosh (f x)) (complex.sinh (f x) * f') s x :=
(complex.has_deriv_at_cosh (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_ccosh (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  deriv_within (λx, complex.cosh (f x)) s x = complex.sinh (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.ccosh.deriv_within hxs

@[simp] lemma deriv_ccosh (hc : differentiable_at ℂ f x) :
  deriv (λx, complex.cosh (f x)) x = complex.sinh (f x) * (deriv f x) :=
hc.has_deriv_at.ccosh.deriv

/-! #### `complex.sinh` -/

lemma has_strict_deriv_at.csinh (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ x, complex.sinh (f x)) (complex.cosh (f x) * f') x :=
(complex.has_strict_deriv_at_sinh (f x)).comp x hf

lemma has_deriv_at.csinh (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, complex.sinh (f x)) (complex.cosh (f x) * f') x :=
(complex.has_deriv_at_sinh (f x)).comp x hf

lemma has_deriv_within_at.csinh (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, complex.sinh (f x)) (complex.cosh (f x) * f') s x :=
(complex.has_deriv_at_sinh (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_csinh (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  deriv_within (λx, complex.sinh (f x)) s x = complex.cosh (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.csinh.deriv_within hxs

@[simp] lemma deriv_csinh (hc : differentiable_at ℂ f x) :
  deriv (λx, complex.sinh (f x)) x = complex.cosh (f x) * (deriv f x) :=
hc.has_deriv_at.csinh.deriv

end

section
/-! ### Simp lemmas for derivatives of `λ x, complex.cos (f x)` etc., `f : E → ℂ` -/

variables {E : Type*} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {f' : E →L[ℂ] ℂ}
  {x : E} {s : set E}

/-! #### `complex.cos` -/

lemma has_strict_fderiv_at.ccos (hf : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (λ x, complex.cos (f x)) (- complex.sin (f x) • f') x :=
(complex.has_strict_deriv_at_cos (f x)).comp_has_strict_fderiv_at x hf

lemma has_fderiv_at.ccos (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, complex.cos (f x)) (- complex.sin (f x) • f') x :=
(complex.has_deriv_at_cos (f x)).comp_has_fderiv_at x hf

lemma has_fderiv_within_at.ccos (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, complex.cos (f x)) (- complex.sin (f x) • f') s x :=
(complex.has_deriv_at_cos (f x)).comp_has_fderiv_within_at x hf

lemma differentiable_within_at.ccos (hf : differentiable_within_at ℂ f s x) :
  differentiable_within_at ℂ (λ x, complex.cos (f x)) s x :=
hf.has_fderiv_within_at.ccos.differentiable_within_at

@[simp] lemma differentiable_at.ccos (hc : differentiable_at ℂ f x) :
  differentiable_at ℂ (λx, complex.cos (f x)) x :=
hc.has_fderiv_at.ccos.differentiable_at

lemma differentiable_on.ccos (hc : differentiable_on ℂ f s) :
  differentiable_on ℂ (λx, complex.cos (f x)) s :=
λx h, (hc x h).ccos

@[simp] lemma differentiable.ccos (hc : differentiable ℂ f) :
  differentiable ℂ (λx, complex.cos (f x)) :=
λx, (hc x).ccos

lemma fderiv_within_ccos (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  fderiv_within ℂ (λx, complex.cos (f x)) s x = - complex.sin (f x) • (fderiv_within ℂ f s x) :=
hf.has_fderiv_within_at.ccos.fderiv_within hxs

@[simp] lemma fderiv_ccos (hc : differentiable_at ℂ f x) :
  fderiv ℂ (λx, complex.cos (f x)) x = - complex.sin (f x) • (fderiv ℂ f x) :=
hc.has_fderiv_at.ccos.fderiv

lemma times_cont_diff.ccos {n} (h : times_cont_diff ℂ n f) :
  times_cont_diff ℂ n (λ x, complex.cos (f x)) :=
complex.times_cont_diff_cos.comp h

lemma times_cont_diff_at.ccos {n} (hf : times_cont_diff_at ℂ n f x) :
  times_cont_diff_at ℂ n (λ x, complex.cos (f x)) x :=
complex.times_cont_diff_cos.times_cont_diff_at.comp x hf

lemma times_cont_diff_on.ccos {n} (hf : times_cont_diff_on ℂ n f s) :
  times_cont_diff_on ℂ n (λ x, complex.cos (f x)) s :=
complex.times_cont_diff_cos.comp_times_cont_diff_on  hf

lemma times_cont_diff_within_at.ccos {n} (hf : times_cont_diff_within_at ℂ n f s x) :
  times_cont_diff_within_at ℂ n (λ x, complex.cos (f x)) s x :=
complex.times_cont_diff_cos.times_cont_diff_at.comp_times_cont_diff_within_at x hf

/-! #### `complex.sin` -/

lemma has_strict_fderiv_at.csin (hf : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (λ x, complex.sin (f x)) (complex.cos (f x) • f') x :=
(complex.has_strict_deriv_at_sin (f x)).comp_has_strict_fderiv_at x hf

lemma has_fderiv_at.csin (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, complex.sin (f x)) (complex.cos (f x) • f') x :=
(complex.has_deriv_at_sin (f x)).comp_has_fderiv_at x hf

lemma has_fderiv_within_at.csin (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, complex.sin (f x)) (complex.cos (f x) • f') s x :=
(complex.has_deriv_at_sin (f x)).comp_has_fderiv_within_at x hf

lemma differentiable_within_at.csin (hf : differentiable_within_at ℂ f s x) :
  differentiable_within_at ℂ (λ x, complex.sin (f x)) s x :=
hf.has_fderiv_within_at.csin.differentiable_within_at

@[simp] lemma differentiable_at.csin (hc : differentiable_at ℂ f x) :
  differentiable_at ℂ (λx, complex.sin (f x)) x :=
hc.has_fderiv_at.csin.differentiable_at

lemma differentiable_on.csin (hc : differentiable_on ℂ f s) :
  differentiable_on ℂ (λx, complex.sin (f x)) s :=
λx h, (hc x h).csin

@[simp] lemma differentiable.csin (hc : differentiable ℂ f) :
  differentiable ℂ (λx, complex.sin (f x)) :=
λx, (hc x).csin

lemma fderiv_within_csin (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  fderiv_within ℂ (λx, complex.sin (f x)) s x = complex.cos (f x) • (fderiv_within ℂ f s x) :=
hf.has_fderiv_within_at.csin.fderiv_within hxs

@[simp] lemma fderiv_csin (hc : differentiable_at ℂ f x) :
  fderiv ℂ (λx, complex.sin (f x)) x = complex.cos (f x) • (fderiv ℂ f x) :=
hc.has_fderiv_at.csin.fderiv

lemma times_cont_diff.csin {n} (h : times_cont_diff ℂ n f) :
  times_cont_diff ℂ n (λ x, complex.sin (f x)) :=
complex.times_cont_diff_sin.comp h

lemma times_cont_diff_at.csin {n} (hf : times_cont_diff_at ℂ n f x) :
  times_cont_diff_at ℂ n (λ x, complex.sin (f x)) x :=
complex.times_cont_diff_sin.times_cont_diff_at.comp x hf

lemma times_cont_diff_on.csin {n} (hf : times_cont_diff_on ℂ n f s) :
  times_cont_diff_on ℂ n (λ x, complex.sin (f x)) s :=
complex.times_cont_diff_sin.comp_times_cont_diff_on  hf

lemma times_cont_diff_within_at.csin {n} (hf : times_cont_diff_within_at ℂ n f s x) :
  times_cont_diff_within_at ℂ n (λ x, complex.sin (f x)) s x :=
complex.times_cont_diff_sin.times_cont_diff_at.comp_times_cont_diff_within_at x hf

/-! #### `complex.cosh` -/

lemma has_strict_fderiv_at.ccosh (hf : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (λ x, complex.cosh (f x)) (complex.sinh (f x) • f') x :=
(complex.has_strict_deriv_at_cosh (f x)).comp_has_strict_fderiv_at x hf

lemma has_fderiv_at.ccosh (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, complex.cosh (f x)) (complex.sinh (f x) • f') x :=
(complex.has_deriv_at_cosh (f x)).comp_has_fderiv_at x hf

lemma has_fderiv_within_at.ccosh (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, complex.cosh (f x)) (complex.sinh (f x) • f') s x :=
(complex.has_deriv_at_cosh (f x)).comp_has_fderiv_within_at x hf

lemma differentiable_within_at.ccosh (hf : differentiable_within_at ℂ f s x) :
  differentiable_within_at ℂ (λ x, complex.cosh (f x)) s x :=
hf.has_fderiv_within_at.ccosh.differentiable_within_at

@[simp] lemma differentiable_at.ccosh (hc : differentiable_at ℂ f x) :
  differentiable_at ℂ (λx, complex.cosh (f x)) x :=
hc.has_fderiv_at.ccosh.differentiable_at

lemma differentiable_on.ccosh (hc : differentiable_on ℂ f s) :
  differentiable_on ℂ (λx, complex.cosh (f x)) s :=
λx h, (hc x h).ccosh

@[simp] lemma differentiable.ccosh (hc : differentiable ℂ f) :
  differentiable ℂ (λx, complex.cosh (f x)) :=
λx, (hc x).ccosh

lemma fderiv_within_ccosh (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  fderiv_within ℂ (λx, complex.cosh (f x)) s x = complex.sinh (f x) • (fderiv_within ℂ f s x) :=
hf.has_fderiv_within_at.ccosh.fderiv_within hxs

@[simp] lemma fderiv_ccosh (hc : differentiable_at ℂ f x) :
  fderiv ℂ (λx, complex.cosh (f x)) x = complex.sinh (f x) • (fderiv ℂ f x) :=
hc.has_fderiv_at.ccosh.fderiv

lemma times_cont_diff.ccosh {n} (h : times_cont_diff ℂ n f) :
  times_cont_diff ℂ n (λ x, complex.cosh (f x)) :=
complex.times_cont_diff_cosh.comp h

lemma times_cont_diff_at.ccosh {n} (hf : times_cont_diff_at ℂ n f x) :
  times_cont_diff_at ℂ n (λ x, complex.cosh (f x)) x :=
complex.times_cont_diff_cosh.times_cont_diff_at.comp x hf

lemma times_cont_diff_on.ccosh {n} (hf : times_cont_diff_on ℂ n f s) :
  times_cont_diff_on ℂ n (λ x, complex.cosh (f x)) s :=
complex.times_cont_diff_cosh.comp_times_cont_diff_on  hf

lemma times_cont_diff_within_at.ccosh {n} (hf : times_cont_diff_within_at ℂ n f s x) :
  times_cont_diff_within_at ℂ n (λ x, complex.cosh (f x)) s x :=
complex.times_cont_diff_cosh.times_cont_diff_at.comp_times_cont_diff_within_at x hf

/-! #### `complex.sinh` -/

lemma has_strict_fderiv_at.csinh (hf : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (λ x, complex.sinh (f x)) (complex.cosh (f x) • f') x :=
(complex.has_strict_deriv_at_sinh (f x)).comp_has_strict_fderiv_at x hf

lemma has_fderiv_at.csinh (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, complex.sinh (f x)) (complex.cosh (f x) • f') x :=
(complex.has_deriv_at_sinh (f x)).comp_has_fderiv_at x hf

lemma has_fderiv_within_at.csinh (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, complex.sinh (f x)) (complex.cosh (f x) • f') s x :=
(complex.has_deriv_at_sinh (f x)).comp_has_fderiv_within_at x hf

lemma differentiable_within_at.csinh (hf : differentiable_within_at ℂ f s x) :
  differentiable_within_at ℂ (λ x, complex.sinh (f x)) s x :=
hf.has_fderiv_within_at.csinh.differentiable_within_at

@[simp] lemma differentiable_at.csinh (hc : differentiable_at ℂ f x) :
  differentiable_at ℂ (λx, complex.sinh (f x)) x :=
hc.has_fderiv_at.csinh.differentiable_at

lemma differentiable_on.csinh (hc : differentiable_on ℂ f s) :
  differentiable_on ℂ (λx, complex.sinh (f x)) s :=
λx h, (hc x h).csinh

@[simp] lemma differentiable.csinh (hc : differentiable ℂ f) :
  differentiable ℂ (λx, complex.sinh (f x)) :=
λx, (hc x).csinh

lemma fderiv_within_csinh (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  fderiv_within ℂ (λx, complex.sinh (f x)) s x = complex.cosh (f x) • (fderiv_within ℂ f s x) :=
hf.has_fderiv_within_at.csinh.fderiv_within hxs

@[simp] lemma fderiv_csinh (hc : differentiable_at ℂ f x) :
  fderiv ℂ (λx, complex.sinh (f x)) x = complex.cosh (f x) • (fderiv ℂ f x) :=
hc.has_fderiv_at.csinh.fderiv

lemma times_cont_diff.csinh {n} (h : times_cont_diff ℂ n f) :
  times_cont_diff ℂ n (λ x, complex.sinh (f x)) :=
complex.times_cont_diff_sinh.comp h

lemma times_cont_diff_at.csinh {n} (hf : times_cont_diff_at ℂ n f x) :
  times_cont_diff_at ℂ n (λ x, complex.sinh (f x)) x :=
complex.times_cont_diff_sinh.times_cont_diff_at.comp x hf

lemma times_cont_diff_on.csinh {n} (hf : times_cont_diff_on ℂ n f s) :
  times_cont_diff_on ℂ n (λ x, complex.sinh (f x)) s :=
complex.times_cont_diff_sinh.comp_times_cont_diff_on  hf

lemma times_cont_diff_within_at.csinh {n} (hf : times_cont_diff_within_at ℂ n f s x) :
  times_cont_diff_within_at ℂ n (λ x, complex.sinh (f x)) s x :=
complex.times_cont_diff_sinh.times_cont_diff_at.comp_times_cont_diff_within_at x hf

end

namespace real

variables {x y z : ℝ}

lemma has_strict_deriv_at_sin (x : ℝ) : has_strict_deriv_at sin (cos x) x :=
(complex.has_strict_deriv_at_sin x).real_of_complex

lemma has_deriv_at_sin (x : ℝ) : has_deriv_at sin (cos x) x :=
(has_strict_deriv_at_sin x).has_deriv_at

lemma times_cont_diff_sin {n} : times_cont_diff ℝ n sin :=
complex.times_cont_diff_sin.real_of_complex

lemma differentiable_sin : differentiable ℝ sin :=
λx, (has_deriv_at_sin x).differentiable_at

lemma differentiable_at_sin : differentiable_at ℝ sin x :=
differentiable_sin x

@[simp] lemma deriv_sin : deriv sin = cos :=
funext $ λ x, (has_deriv_at_sin x).deriv

@[continuity]
lemma continuous_sin : continuous sin :=
differentiable_sin.continuous

lemma continuous_on_sin {s} : continuous_on sin s :=
continuous_sin.continuous_on

lemma has_strict_deriv_at_cos (x : ℝ) : has_strict_deriv_at cos (-sin x) x :=
(complex.has_strict_deriv_at_cos x).real_of_complex

lemma has_deriv_at_cos (x : ℝ) : has_deriv_at cos (-sin x) x :=
(complex.has_deriv_at_cos x).real_of_complex

lemma times_cont_diff_cos {n} : times_cont_diff ℝ n cos :=
complex.times_cont_diff_cos.real_of_complex

lemma differentiable_cos : differentiable ℝ cos :=
λx, (has_deriv_at_cos x).differentiable_at

lemma differentiable_at_cos : differentiable_at ℝ cos x :=
differentiable_cos x

lemma deriv_cos : deriv cos x = - sin x :=
(has_deriv_at_cos x).deriv

@[simp] lemma deriv_cos' : deriv cos = (λ x, - sin x) :=
funext $ λ _, deriv_cos

@[continuity]
lemma continuous_cos : continuous cos :=
differentiable_cos.continuous

lemma continuous_on_cos {s} : continuous_on cos s := continuous_cos.continuous_on

lemma has_strict_deriv_at_sinh (x : ℝ) : has_strict_deriv_at sinh (cosh x) x :=
(complex.has_strict_deriv_at_sinh x).real_of_complex

lemma has_deriv_at_sinh (x : ℝ) : has_deriv_at sinh (cosh x) x :=
(complex.has_deriv_at_sinh x).real_of_complex

lemma times_cont_diff_sinh {n} : times_cont_diff ℝ n sinh :=
complex.times_cont_diff_sinh.real_of_complex

lemma differentiable_sinh : differentiable ℝ sinh :=
λx, (has_deriv_at_sinh x).differentiable_at

lemma differentiable_at_sinh : differentiable_at ℝ sinh x :=
differentiable_sinh x

@[simp] lemma deriv_sinh : deriv sinh = cosh :=
funext $ λ x, (has_deriv_at_sinh x).deriv

@[continuity]
lemma continuous_sinh : continuous sinh :=
differentiable_sinh.continuous

lemma has_strict_deriv_at_cosh (x : ℝ) : has_strict_deriv_at cosh (sinh x) x :=
(complex.has_strict_deriv_at_cosh x).real_of_complex

lemma has_deriv_at_cosh (x : ℝ) : has_deriv_at cosh (sinh x) x :=
(complex.has_deriv_at_cosh x).real_of_complex

lemma times_cont_diff_cosh {n} : times_cont_diff ℝ n cosh :=
complex.times_cont_diff_cosh.real_of_complex

lemma differentiable_cosh : differentiable ℝ cosh :=
λx, (has_deriv_at_cosh x).differentiable_at

lemma differentiable_at_cosh : differentiable_at ℝ cosh x :=
differentiable_cosh x

@[simp] lemma deriv_cosh : deriv cosh = sinh :=
funext $ λ x, (has_deriv_at_cosh x).deriv

@[continuity]
lemma continuous_cosh : continuous cosh :=
differentiable_cosh.continuous

/-- `sinh` is strictly monotone. -/
lemma sinh_strict_mono : strict_mono sinh :=
strict_mono_of_deriv_pos differentiable_sinh (by { rw [real.deriv_sinh], exact cosh_pos })

end real

section
/-! ### Simp lemmas for derivatives of `λ x, real.cos (f x)` etc., `f : ℝ → ℝ` -/

variables {f : ℝ → ℝ} {f' x : ℝ} {s : set ℝ}

/-! #### `real.cos` -/

lemma has_strict_deriv_at.cos (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ x, real.cos (f x)) (- real.sin (f x) * f') x :=
(real.has_strict_deriv_at_cos (f x)).comp x hf

lemma has_deriv_at.cos (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, real.cos (f x)) (- real.sin (f x) * f') x :=
(real.has_deriv_at_cos (f x)).comp x hf

lemma has_deriv_within_at.cos (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, real.cos (f x)) (- real.sin (f x) * f') s x :=
(real.has_deriv_at_cos (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_cos (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λx, real.cos (f x)) s x = - real.sin (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.cos.deriv_within hxs

@[simp] lemma deriv_cos (hc : differentiable_at ℝ f x) :
  deriv (λx, real.cos (f x)) x = - real.sin (f x) * (deriv f x) :=
hc.has_deriv_at.cos.deriv

/-! #### `real.sin` -/

lemma has_strict_deriv_at.sin (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ x, real.sin (f x)) (real.cos (f x) * f') x :=
(real.has_strict_deriv_at_sin (f x)).comp x hf

lemma has_deriv_at.sin (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, real.sin (f x)) (real.cos (f x) * f') x :=
(real.has_deriv_at_sin (f x)).comp x hf

lemma has_deriv_within_at.sin (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, real.sin (f x)) (real.cos (f x) * f') s x :=
(real.has_deriv_at_sin (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_sin (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λx, real.sin (f x)) s x = real.cos (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.sin.deriv_within hxs

@[simp] lemma deriv_sin (hc : differentiable_at ℝ f x) :
  deriv (λx, real.sin (f x)) x = real.cos (f x) * (deriv f x) :=
hc.has_deriv_at.sin.deriv

/-! #### `real.cosh` -/

lemma has_strict_deriv_at.cosh (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ x, real.cosh (f x)) (real.sinh (f x) * f') x :=
(real.has_strict_deriv_at_cosh (f x)).comp x hf

lemma has_deriv_at.cosh (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, real.cosh (f x)) (real.sinh (f x) * f') x :=
(real.has_deriv_at_cosh (f x)).comp x hf

lemma has_deriv_within_at.cosh (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, real.cosh (f x)) (real.sinh (f x) * f') s x :=
(real.has_deriv_at_cosh (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_cosh (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λx, real.cosh (f x)) s x = real.sinh (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.cosh.deriv_within hxs

@[simp] lemma deriv_cosh (hc : differentiable_at ℝ f x) :
  deriv (λx, real.cosh (f x)) x = real.sinh (f x) * (deriv f x) :=
hc.has_deriv_at.cosh.deriv

/-! #### `real.sinh` -/

lemma has_strict_deriv_at.sinh (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ x, real.sinh (f x)) (real.cosh (f x) * f') x :=
(real.has_strict_deriv_at_sinh (f x)).comp x hf

lemma has_deriv_at.sinh (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, real.sinh (f x)) (real.cosh (f x) * f') x :=
(real.has_deriv_at_sinh (f x)).comp x hf

lemma has_deriv_within_at.sinh (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, real.sinh (f x)) (real.cosh (f x) * f') s x :=
(real.has_deriv_at_sinh (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_sinh (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λx, real.sinh (f x)) s x = real.cosh (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.sinh.deriv_within hxs

@[simp] lemma deriv_sinh (hc : differentiable_at ℝ f x) :
  deriv (λx, real.sinh (f x)) x = real.cosh (f x) * (deriv f x) :=
hc.has_deriv_at.sinh.deriv

end

section

/-! ### Simp lemmas for derivatives of `λ x, real.cos (f x)` etc., `f : E → ℝ` -/

variables {E : Type*} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {f' : E →L[ℝ] ℝ}
  {x : E} {s : set E}

/-! #### `real.cos` -/

lemma has_strict_fderiv_at.cos (hf : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (λ x, real.cos (f x)) (- real.sin (f x) • f') x :=
(real.has_strict_deriv_at_cos (f x)).comp_has_strict_fderiv_at x hf

lemma has_fderiv_at.cos (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, real.cos (f x)) (- real.sin (f x) • f') x :=
(real.has_deriv_at_cos (f x)).comp_has_fderiv_at x hf

lemma has_fderiv_within_at.cos (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, real.cos (f x)) (- real.sin (f x) • f') s x :=
(real.has_deriv_at_cos (f x)).comp_has_fderiv_within_at x hf

lemma differentiable_within_at.cos (hf : differentiable_within_at ℝ f s x) :
  differentiable_within_at ℝ (λ x, real.cos (f x)) s x :=
hf.has_fderiv_within_at.cos.differentiable_within_at

@[simp] lemma differentiable_at.cos (hc : differentiable_at ℝ f x) :
  differentiable_at ℝ (λx, real.cos (f x)) x :=
hc.has_fderiv_at.cos.differentiable_at

lemma differentiable_on.cos (hc : differentiable_on ℝ f s) :
  differentiable_on ℝ (λx, real.cos (f x)) s :=
λx h, (hc x h).cos

@[simp] lemma differentiable.cos (hc : differentiable ℝ f) :
  differentiable ℝ (λx, real.cos (f x)) :=
λx, (hc x).cos

lemma fderiv_within_cos (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  fderiv_within ℝ (λx, real.cos (f x)) s x = - real.sin (f x) • (fderiv_within ℝ f s x) :=
hf.has_fderiv_within_at.cos.fderiv_within hxs

@[simp] lemma fderiv_cos (hc : differentiable_at ℝ f x) :
  fderiv ℝ (λx, real.cos (f x)) x = - real.sin (f x) • (fderiv ℝ f x) :=
hc.has_fderiv_at.cos.fderiv

lemma times_cont_diff.cos {n} (h : times_cont_diff ℝ n f) :
  times_cont_diff ℝ n (λ x, real.cos (f x)) :=
real.times_cont_diff_cos.comp h

lemma times_cont_diff_at.cos {n} (hf : times_cont_diff_at ℝ n f x) :
  times_cont_diff_at ℝ n (λ x, real.cos (f x)) x :=
real.times_cont_diff_cos.times_cont_diff_at.comp x hf

lemma times_cont_diff_on.cos {n} (hf : times_cont_diff_on ℝ n f s) :
  times_cont_diff_on ℝ n (λ x, real.cos (f x)) s :=
real.times_cont_diff_cos.comp_times_cont_diff_on  hf

lemma times_cont_diff_within_at.cos {n} (hf : times_cont_diff_within_at ℝ n f s x) :
  times_cont_diff_within_at ℝ n (λ x, real.cos (f x)) s x :=
real.times_cont_diff_cos.times_cont_diff_at.comp_times_cont_diff_within_at x hf

/-! #### `real.sin` -/

lemma has_strict_fderiv_at.sin (hf : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (λ x, real.sin (f x)) (real.cos (f x) • f') x :=
(real.has_strict_deriv_at_sin (f x)).comp_has_strict_fderiv_at x hf

lemma has_fderiv_at.sin (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, real.sin (f x)) (real.cos (f x) • f') x :=
(real.has_deriv_at_sin (f x)).comp_has_fderiv_at x hf

lemma has_fderiv_within_at.sin (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, real.sin (f x)) (real.cos (f x) • f') s x :=
(real.has_deriv_at_sin (f x)).comp_has_fderiv_within_at x hf

lemma differentiable_within_at.sin (hf : differentiable_within_at ℝ f s x) :
  differentiable_within_at ℝ (λ x, real.sin (f x)) s x :=
hf.has_fderiv_within_at.sin.differentiable_within_at

@[simp] lemma differentiable_at.sin (hc : differentiable_at ℝ f x) :
  differentiable_at ℝ (λx, real.sin (f x)) x :=
hc.has_fderiv_at.sin.differentiable_at

lemma differentiable_on.sin (hc : differentiable_on ℝ f s) :
  differentiable_on ℝ (λx, real.sin (f x)) s :=
λx h, (hc x h).sin

@[simp] lemma differentiable.sin (hc : differentiable ℝ f) :
  differentiable ℝ (λx, real.sin (f x)) :=
λx, (hc x).sin

lemma fderiv_within_sin (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  fderiv_within ℝ (λx, real.sin (f x)) s x = real.cos (f x) • (fderiv_within ℝ f s x) :=
hf.has_fderiv_within_at.sin.fderiv_within hxs

@[simp] lemma fderiv_sin (hc : differentiable_at ℝ f x) :
  fderiv ℝ (λx, real.sin (f x)) x = real.cos (f x) • (fderiv ℝ f x) :=
hc.has_fderiv_at.sin.fderiv

lemma times_cont_diff.sin {n} (h : times_cont_diff ℝ n f) :
  times_cont_diff ℝ n (λ x, real.sin (f x)) :=
real.times_cont_diff_sin.comp h

lemma times_cont_diff_at.sin {n} (hf : times_cont_diff_at ℝ n f x) :
  times_cont_diff_at ℝ n (λ x, real.sin (f x)) x :=
real.times_cont_diff_sin.times_cont_diff_at.comp x hf

lemma times_cont_diff_on.sin {n} (hf : times_cont_diff_on ℝ n f s) :
  times_cont_diff_on ℝ n (λ x, real.sin (f x)) s :=
real.times_cont_diff_sin.comp_times_cont_diff_on  hf

lemma times_cont_diff_within_at.sin {n} (hf : times_cont_diff_within_at ℝ n f s x) :
  times_cont_diff_within_at ℝ n (λ x, real.sin (f x)) s x :=
real.times_cont_diff_sin.times_cont_diff_at.comp_times_cont_diff_within_at x hf

/-! #### `real.cosh` -/

lemma has_strict_fderiv_at.cosh (hf : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (λ x, real.cosh (f x)) (real.sinh (f x) • f') x :=
(real.has_strict_deriv_at_cosh (f x)).comp_has_strict_fderiv_at x hf

lemma has_fderiv_at.cosh (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, real.cosh (f x)) (real.sinh (f x) • f') x :=
(real.has_deriv_at_cosh (f x)).comp_has_fderiv_at x hf

lemma has_fderiv_within_at.cosh (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, real.cosh (f x)) (real.sinh (f x) • f') s x :=
(real.has_deriv_at_cosh (f x)).comp_has_fderiv_within_at x hf

lemma differentiable_within_at.cosh (hf : differentiable_within_at ℝ f s x) :
  differentiable_within_at ℝ (λ x, real.cosh (f x)) s x :=
hf.has_fderiv_within_at.cosh.differentiable_within_at

@[simp] lemma differentiable_at.cosh (hc : differentiable_at ℝ f x) :
  differentiable_at ℝ (λx, real.cosh (f x)) x :=
hc.has_fderiv_at.cosh.differentiable_at

lemma differentiable_on.cosh (hc : differentiable_on ℝ f s) :
  differentiable_on ℝ (λx, real.cosh (f x)) s :=
λx h, (hc x h).cosh

@[simp] lemma differentiable.cosh (hc : differentiable ℝ f) :
  differentiable ℝ (λx, real.cosh (f x)) :=
λx, (hc x).cosh

lemma fderiv_within_cosh (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  fderiv_within ℝ (λx, real.cosh (f x)) s x = real.sinh (f x) • (fderiv_within ℝ f s x) :=
hf.has_fderiv_within_at.cosh.fderiv_within hxs

@[simp] lemma fderiv_cosh (hc : differentiable_at ℝ f x) :
  fderiv ℝ (λx, real.cosh (f x)) x = real.sinh (f x) • (fderiv ℝ f x) :=
hc.has_fderiv_at.cosh.fderiv

lemma times_cont_diff.cosh {n} (h : times_cont_diff ℝ n f) :
  times_cont_diff ℝ n (λ x, real.cosh (f x)) :=
real.times_cont_diff_cosh.comp h

lemma times_cont_diff_at.cosh {n} (hf : times_cont_diff_at ℝ n f x) :
  times_cont_diff_at ℝ n (λ x, real.cosh (f x)) x :=
real.times_cont_diff_cosh.times_cont_diff_at.comp x hf

lemma times_cont_diff_on.cosh {n} (hf : times_cont_diff_on ℝ n f s) :
  times_cont_diff_on ℝ n (λ x, real.cosh (f x)) s :=
real.times_cont_diff_cosh.comp_times_cont_diff_on  hf

lemma times_cont_diff_within_at.cosh {n} (hf : times_cont_diff_within_at ℝ n f s x) :
  times_cont_diff_within_at ℝ n (λ x, real.cosh (f x)) s x :=
real.times_cont_diff_cosh.times_cont_diff_at.comp_times_cont_diff_within_at x hf

/-! #### `real.sinh` -/

lemma has_strict_fderiv_at.sinh (hf : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (λ x, real.sinh (f x)) (real.cosh (f x) • f') x :=
(real.has_strict_deriv_at_sinh (f x)).comp_has_strict_fderiv_at x hf

lemma has_fderiv_at.sinh (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, real.sinh (f x)) (real.cosh (f x) • f') x :=
(real.has_deriv_at_sinh (f x)).comp_has_fderiv_at x hf

lemma has_fderiv_within_at.sinh (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, real.sinh (f x)) (real.cosh (f x) • f') s x :=
(real.has_deriv_at_sinh (f x)).comp_has_fderiv_within_at x hf

lemma differentiable_within_at.sinh (hf : differentiable_within_at ℝ f s x) :
  differentiable_within_at ℝ (λ x, real.sinh (f x)) s x :=
hf.has_fderiv_within_at.sinh.differentiable_within_at

@[simp] lemma differentiable_at.sinh (hc : differentiable_at ℝ f x) :
  differentiable_at ℝ (λx, real.sinh (f x)) x :=
hc.has_fderiv_at.sinh.differentiable_at

lemma differentiable_on.sinh (hc : differentiable_on ℝ f s) :
  differentiable_on ℝ (λx, real.sinh (f x)) s :=
λx h, (hc x h).sinh

@[simp] lemma differentiable.sinh (hc : differentiable ℝ f) :
  differentiable ℝ (λx, real.sinh (f x)) :=
λx, (hc x).sinh

lemma fderiv_within_sinh (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  fderiv_within ℝ (λx, real.sinh (f x)) s x = real.cosh (f x) • (fderiv_within ℝ f s x) :=
hf.has_fderiv_within_at.sinh.fderiv_within hxs

@[simp] lemma fderiv_sinh (hc : differentiable_at ℝ f x) :
  fderiv ℝ (λx, real.sinh (f x)) x = real.cosh (f x) • (fderiv ℝ f x) :=
hc.has_fderiv_at.sinh.fderiv

lemma times_cont_diff.sinh {n} (h : times_cont_diff ℝ n f) :
  times_cont_diff ℝ n (λ x, real.sinh (f x)) :=
real.times_cont_diff_sinh.comp h

lemma times_cont_diff_at.sinh {n} (hf : times_cont_diff_at ℝ n f x) :
  times_cont_diff_at ℝ n (λ x, real.sinh (f x)) x :=
real.times_cont_diff_sinh.times_cont_diff_at.comp x hf

lemma times_cont_diff_on.sinh {n} (hf : times_cont_diff_on ℝ n f s) :
  times_cont_diff_on ℝ n (λ x, real.sinh (f x)) s :=
real.times_cont_diff_sinh.comp_times_cont_diff_on  hf

lemma times_cont_diff_within_at.sinh {n} (hf : times_cont_diff_within_at ℝ n f s x) :
  times_cont_diff_within_at ℝ n (λ x, real.sinh (f x)) s x :=
real.times_cont_diff_sinh.times_cont_diff_at.comp_times_cont_diff_within_at x hf

end

namespace real

lemma exists_cos_eq_zero : 0 ∈ cos '' Icc (1:ℝ) 2 :=
intermediate_value_Icc' (by norm_num) continuous_on_cos
  ⟨le_of_lt cos_two_neg, le_of_lt cos_one_pos⟩

/-- The number π = 3.14159265... Defined here using choice as twice a zero of cos in [1,2], from
which one can derive all its properties. For explicit bounds on π, see `data.real.pi.bounds`. -/
protected noncomputable def pi : ℝ := 2 * classical.some exists_cos_eq_zero

localized "notation `π` := real.pi" in real

@[simp] lemma cos_pi_div_two : cos (π / 2) = 0 :=
by rw [real.pi, mul_div_cancel_left _ (@two_ne_zero' ℝ _ _ _)];
  exact (classical.some_spec exists_cos_eq_zero).2

lemma one_le_pi_div_two : (1 : ℝ) ≤ π / 2 :=
by rw [real.pi, mul_div_cancel_left _ (@two_ne_zero' ℝ _ _ _)];
  exact (classical.some_spec exists_cos_eq_zero).1.1

lemma pi_div_two_le_two : π / 2 ≤ 2 :=
by rw [real.pi, mul_div_cancel_left _ (@two_ne_zero' ℝ _ _ _)];
  exact (classical.some_spec exists_cos_eq_zero).1.2

lemma two_le_pi : (2 : ℝ) ≤ π :=
(div_le_div_right (show (0 : ℝ) < 2, by norm_num)).1
  (by rw div_self (@two_ne_zero' ℝ _ _ _); exact one_le_pi_div_two)

lemma pi_le_four : π ≤ 4 :=
(div_le_div_right (show (0 : ℝ) < 2, by norm_num)).1
  (calc π / 2 ≤ 2 : pi_div_two_le_two
    ... = 4 / 2 : by norm_num)

lemma pi_pos : 0 < π :=
lt_of_lt_of_le (by norm_num) two_le_pi

lemma pi_ne_zero : π ≠ 0 :=
ne_of_gt pi_pos

lemma pi_div_two_pos : 0 < π / 2 :=
half_pos pi_pos

lemma two_pi_pos : 0 < 2 * π :=
by linarith [pi_pos]

end real

namespace nnreal
open real
open_locale real nnreal

/-- `π` considered as a nonnegative real. -/
noncomputable def pi : ℝ≥0 := ⟨π, real.pi_pos.le⟩

@[simp] lemma coe_real_pi : (pi : ℝ) = π := rfl

lemma pi_pos : 0 < pi := by exact_mod_cast real.pi_pos

lemma pi_ne_zero : pi ≠ 0 := pi_pos.ne'

end nnreal

namespace real
open_locale real

@[simp] lemma sin_pi : sin π = 0 :=
by rw [← mul_div_cancel_left π (@two_ne_zero ℝ _ _), two_mul, add_div,
    sin_add, cos_pi_div_two]; simp

@[simp] lemma cos_pi : cos π = -1 :=
by rw [← mul_div_cancel_left π (@two_ne_zero ℝ _ _), mul_div_assoc,
    cos_two_mul, cos_pi_div_two];
  simp [bit0, pow_add]

@[simp] lemma sin_two_pi : sin (2 * π) = 0 :=
by simp [two_mul, sin_add]

@[simp] lemma cos_two_pi : cos (2 * π) = 1 :=
by simp [two_mul, cos_add]

lemma sin_antiperiodic : function.antiperiodic sin π :=
by simp [sin_add]

lemma sin_periodic : function.periodic sin (2 * π) :=
sin_antiperiodic.periodic

@[simp] lemma sin_add_pi (x : ℝ) : sin (x + π) = -sin x :=
sin_antiperiodic x

@[simp] lemma sin_add_two_pi (x : ℝ) : sin (x + 2 * π) = sin x :=
sin_periodic x

@[simp] lemma sin_sub_pi (x : ℝ) : sin (x - π) = -sin x :=
sin_antiperiodic.sub_eq x

@[simp] lemma sin_sub_two_pi (x : ℝ) : sin (x - 2 * π) = sin x :=
sin_periodic.sub_eq x

@[simp] lemma sin_pi_sub (x : ℝ) : sin (π - x) = sin x :=
neg_neg (sin x) ▸ sin_neg x ▸ sin_antiperiodic.sub_eq'

@[simp] lemma sin_two_pi_sub (x : ℝ) : sin (2 * π - x) = -sin x :=
sin_neg x ▸ sin_periodic.sub_eq'

@[simp] lemma sin_nat_mul_pi (n : ℕ) : sin (n * π) = 0 :=
sin_antiperiodic.nat_mul_eq_of_eq_zero sin_zero n

@[simp] lemma sin_int_mul_pi (n : ℤ) : sin (n * π) = 0 :=
sin_antiperiodic.int_mul_eq_of_eq_zero sin_zero n

@[simp] lemma sin_add_nat_mul_two_pi (x : ℝ) (n : ℕ) : sin (x + n * (2 * π)) = sin x :=
sin_periodic.nat_mul n x

@[simp] lemma sin_add_int_mul_two_pi (x : ℝ) (n : ℤ) : sin (x + n * (2 * π)) = sin x :=
sin_periodic.int_mul n x

@[simp] lemma sin_sub_nat_mul_two_pi (x : ℝ) (n : ℕ) : sin (x - n * (2 * π)) = sin x :=
sin_periodic.sub_nat_mul_eq n

@[simp] lemma sin_sub_int_mul_two_pi (x : ℝ) (n : ℤ) : sin (x - n * (2 * π)) = sin x :=
sin_periodic.sub_int_mul_eq n

@[simp] lemma sin_nat_mul_two_pi_sub (x : ℝ) (n : ℕ) : sin (n * (2 * π) - x) = -sin x :=
sin_neg x ▸ sin_periodic.nat_mul_sub_eq n

@[simp] lemma sin_int_mul_two_pi_sub (x : ℝ) (n : ℤ) : sin (n * (2 * π) - x) = -sin x :=
sin_neg x ▸ sin_periodic.int_mul_sub_eq n

lemma cos_antiperiodic : function.antiperiodic cos π :=
by simp [cos_add]

lemma cos_periodic : function.periodic cos (2 * π) :=
cos_antiperiodic.periodic

@[simp] lemma cos_add_pi (x : ℝ) : cos (x + π) = -cos x :=
cos_antiperiodic x

@[simp] lemma cos_add_two_pi (x : ℝ) : cos (x + 2 * π) = cos x :=
cos_periodic x

@[simp] lemma cos_sub_pi (x : ℝ) : cos (x - π) = -cos x :=
cos_antiperiodic.sub_eq x

@[simp] lemma cos_sub_two_pi (x : ℝ) : cos (x - 2 * π) = cos x :=
cos_periodic.sub_eq x

@[simp] lemma cos_pi_sub (x : ℝ) : cos (π - x) = -cos x :=
cos_neg x ▸ cos_antiperiodic.sub_eq'

@[simp] lemma cos_two_pi_sub (x : ℝ) : cos (2 * π - x) = cos x :=
cos_neg x ▸ cos_periodic.sub_eq'

@[simp] lemma cos_nat_mul_two_pi (n : ℕ) : cos (n * (2 * π)) = 1 :=
(cos_periodic.nat_mul_eq n).trans cos_zero

@[simp] lemma cos_int_mul_two_pi (n : ℤ) : cos (n * (2 * π)) = 1 :=
(cos_periodic.int_mul_eq n).trans cos_zero

@[simp] lemma cos_add_nat_mul_two_pi (x : ℝ) (n : ℕ) : cos (x + n * (2 * π)) = cos x :=
cos_periodic.nat_mul n x

@[simp] lemma cos_add_int_mul_two_pi (x : ℝ) (n : ℤ) : cos (x + n * (2 * π)) = cos x :=
cos_periodic.int_mul n x

@[simp] lemma cos_sub_nat_mul_two_pi (x : ℝ) (n : ℕ) : cos (x - n * (2 * π)) = cos x :=
cos_periodic.sub_nat_mul_eq n

@[simp] lemma cos_sub_int_mul_two_pi (x : ℝ) (n : ℤ) : cos (x - n * (2 * π)) = cos x :=
cos_periodic.sub_int_mul_eq n

@[simp] lemma cos_nat_mul_two_pi_sub (x : ℝ) (n : ℕ) : cos (n * (2 * π) - x) = cos x :=
cos_neg x ▸ cos_periodic.nat_mul_sub_eq n

@[simp] lemma cos_int_mul_two_pi_sub (x : ℝ) (n : ℤ) : cos (n * (2 * π) - x) = cos x :=
cos_neg x ▸ cos_periodic.int_mul_sub_eq n

@[simp] lemma cos_nat_mul_two_pi_add_pi (n : ℕ) : cos (n * (2 * π) + π) = -1 :=
by simpa only [cos_zero] using (cos_periodic.nat_mul n).add_antiperiod_eq cos_antiperiodic

@[simp] lemma cos_int_mul_two_pi_add_pi (n : ℤ) : cos (n * (2 * π) + π) = -1 :=
by simpa only [cos_zero] using (cos_periodic.int_mul n).add_antiperiod_eq cos_antiperiodic

@[simp] lemma cos_nat_mul_two_pi_sub_pi (n : ℕ) : cos (n * (2 * π) - π) = -1 :=
by simpa only [cos_zero] using (cos_periodic.nat_mul n).sub_antiperiod_eq cos_antiperiodic

@[simp] lemma cos_int_mul_two_pi_sub_pi (n : ℤ) : cos (n * (2 * π) - π) = -1 :=
by simpa only [cos_zero] using (cos_periodic.int_mul n).sub_antiperiod_eq cos_antiperiodic

lemma sin_pos_of_pos_of_lt_pi {x : ℝ} (h0x : 0 < x) (hxp : x < π) : 0 < sin x :=
if hx2 : x ≤ 2 then sin_pos_of_pos_of_le_two h0x hx2
else
  have (2 : ℝ) + 2 = 4, from rfl,
  have π - x ≤ 2, from sub_le_iff_le_add.2
    (le_trans pi_le_four (this ▸ add_le_add_left (le_of_not_ge hx2) _)),
  sin_pi_sub x ▸ sin_pos_of_pos_of_le_two (sub_pos.2 hxp) this

lemma sin_pos_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo 0 π) : 0 < sin x :=
sin_pos_of_pos_of_lt_pi hx.1 hx.2

lemma sin_nonneg_of_mem_Icc {x : ℝ} (hx : x ∈ Icc 0 π) : 0 ≤ sin x :=
begin
  rw ← closure_Ioo pi_pos at hx,
  exact closure_lt_subset_le continuous_const continuous_sin
    (closure_mono (λ y, sin_pos_of_mem_Ioo) hx)
end

lemma sin_nonneg_of_nonneg_of_le_pi {x : ℝ} (h0x : 0 ≤ x) (hxp : x ≤ π) : 0 ≤ sin x :=
sin_nonneg_of_mem_Icc ⟨h0x, hxp⟩

lemma sin_neg_of_neg_of_neg_pi_lt {x : ℝ} (hx0 : x < 0) (hpx : -π < x) : sin x < 0 :=
neg_pos.1 $ sin_neg x ▸ sin_pos_of_pos_of_lt_pi (neg_pos.2 hx0) (neg_lt.1 hpx)

lemma sin_nonpos_of_nonnpos_of_neg_pi_le {x : ℝ} (hx0 : x ≤ 0) (hpx : -π ≤ x) : sin x ≤ 0 :=
neg_nonneg.1 $ sin_neg x ▸ sin_nonneg_of_nonneg_of_le_pi (neg_nonneg.2 hx0) (neg_le.1 hpx)

@[simp] lemma sin_pi_div_two : sin (π / 2) = 1 :=
have sin (π / 2) = 1 ∨ sin (π / 2) = -1 :=
by simpa [sq, mul_self_eq_one_iff] using sin_sq_add_cos_sq (π / 2),
this.resolve_right
  (λ h, (show ¬(0 : ℝ) < -1, by norm_num) $
    h ▸ sin_pos_of_pos_of_lt_pi pi_div_two_pos (half_lt_self pi_pos))

lemma sin_add_pi_div_two (x : ℝ) : sin (x + π / 2) = cos x :=
by simp [sin_add]

lemma sin_sub_pi_div_two (x : ℝ) : sin (x - π / 2) = -cos x :=
by simp [sub_eq_add_neg, sin_add]

lemma sin_pi_div_two_sub (x : ℝ) : sin (π / 2 - x) = cos x :=
by simp [sub_eq_add_neg, sin_add]

lemma cos_add_pi_div_two (x : ℝ) : cos (x + π / 2) = -sin x :=
by simp [cos_add]

lemma cos_sub_pi_div_two (x : ℝ) : cos (x - π / 2) = sin x :=
by simp [sub_eq_add_neg, cos_add]

lemma cos_pi_div_two_sub (x : ℝ) : cos (π / 2 - x) = sin x :=
by rw [← cos_neg, neg_sub, cos_sub_pi_div_two]

lemma cos_pos_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo (-(π / 2)) (π / 2)) : 0 < cos x :=
sin_add_pi_div_two x ▸ sin_pos_of_mem_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩

lemma cos_nonneg_of_mem_Icc {x : ℝ} (hx : x ∈ Icc (-(π / 2)) (π / 2)) : 0 ≤ cos x :=
sin_add_pi_div_two x ▸ sin_nonneg_of_mem_Icc ⟨by linarith [hx.1], by linarith [hx.2]⟩

lemma cos_nonneg_of_neg_pi_div_two_le_of_le {x : ℝ} (hl : -(π / 2) ≤ x) (hu : x ≤ π / 2) :
  0 ≤ cos x :=
cos_nonneg_of_mem_Icc ⟨hl, hu⟩

lemma cos_neg_of_pi_div_two_lt_of_lt {x : ℝ} (hx₁ : π / 2 < x) (hx₂ : x < π + π / 2) : cos x < 0 :=
neg_pos.1 $ cos_pi_sub x ▸ cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

lemma cos_nonpos_of_pi_div_two_le_of_le {x : ℝ} (hx₁ : π / 2 ≤ x) (hx₂ : x ≤ π + π / 2) :
  cos x ≤ 0 :=
neg_nonneg.1 $ cos_pi_sub x ▸ cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩

lemma sin_eq_sqrt_one_sub_cos_sq {x : ℝ} (hl : 0 ≤ x) (hu : x ≤ π) :
  sin x = sqrt (1 - cos x ^ 2) :=
by rw [← abs_sin_eq_sqrt_one_sub_cos_sq, abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi hl hu)]

lemma cos_eq_sqrt_one_sub_sin_sq {x : ℝ} (hl : -(π / 2) ≤ x) (hu : x ≤ π / 2) :
  cos x = sqrt (1 - sin x ^ 2) :=
by rw [← abs_cos_eq_sqrt_one_sub_sin_sq, abs_of_nonneg (cos_nonneg_of_mem_Icc ⟨hl, hu⟩)]

lemma sin_eq_zero_iff_of_lt_of_lt {x : ℝ} (hx₁ : -π < x) (hx₂ : x < π) :
  sin x = 0 ↔ x = 0 :=
⟨λ h, le_antisymm
    (le_of_not_gt (λ h0, lt_irrefl (0 : ℝ) $
      calc 0 < sin x : sin_pos_of_pos_of_lt_pi h0 hx₂
        ... = 0 : h))
    (le_of_not_gt (λ h0, lt_irrefl (0 : ℝ) $
      calc 0 = sin x : h.symm
        ... < 0 : sin_neg_of_neg_of_neg_pi_lt h0 hx₁)),
  λ h, by simp [h]⟩

lemma sin_eq_zero_iff {x : ℝ} : sin x = 0 ↔ ∃ n : ℤ, (n : ℝ) * π = x :=
⟨λ h, ⟨⌊x / π⌋, le_antisymm (sub_nonneg.1 (sub_floor_div_mul_nonneg _ pi_pos))
  (sub_nonpos.1 $ le_of_not_gt $ λ h₃,
    (sin_pos_of_pos_of_lt_pi h₃ (sub_floor_div_mul_lt _ pi_pos)).ne
    (by simp [sub_eq_add_neg, sin_add, h, sin_int_mul_pi]))⟩,
  λ ⟨n, hn⟩, hn ▸ sin_int_mul_pi _⟩

lemma sin_ne_zero_iff {x : ℝ} : sin x ≠ 0 ↔ ∀ n : ℤ, (n : ℝ) * π ≠ x :=
by rw [← not_exists, not_iff_not, sin_eq_zero_iff]

lemma sin_eq_zero_iff_cos_eq {x : ℝ} : sin x = 0 ↔ cos x = 1 ∨ cos x = -1 :=
by rw [← mul_self_eq_one_iff, ← sin_sq_add_cos_sq x,
    sq, sq, ← sub_eq_iff_eq_add, sub_self];
  exact ⟨λ h, by rw [h, mul_zero], eq_zero_of_mul_self_eq_zero ∘ eq.symm⟩

lemma cos_eq_one_iff (x : ℝ) : cos x = 1 ↔ ∃ n : ℤ, (n : ℝ) * (2 * π) = x :=
⟨λ h, let ⟨n, hn⟩ := sin_eq_zero_iff.1 (sin_eq_zero_iff_cos_eq.2 (or.inl h)) in
    ⟨n / 2, (int.mod_two_eq_zero_or_one n).elim
      (λ hn0, by rwa [← mul_assoc, ← @int.cast_two ℝ, ← int.cast_mul, int.div_mul_cancel
        ((int.dvd_iff_mod_eq_zero _ _).2 hn0)])
      (λ hn1, by rw [← int.mod_add_div n 2, hn1, int.cast_add, int.cast_one, add_mul,
          one_mul, add_comm, mul_comm (2 : ℤ), int.cast_mul, mul_assoc, int.cast_two] at hn;
        rw [← hn, cos_int_mul_two_pi_add_pi] at h;
        exact absurd h (by norm_num))⟩,
  λ ⟨n, hn⟩, hn ▸ cos_int_mul_two_pi _⟩

lemma cos_eq_one_iff_of_lt_of_lt {x : ℝ} (hx₁ : -(2 * π) < x) (hx₂ : x < 2 * π) :
  cos x = 1 ↔ x = 0 :=
⟨λ h,
    begin
      rcases (cos_eq_one_iff _).1 h with ⟨n, rfl⟩,
      rw [mul_lt_iff_lt_one_left two_pi_pos] at hx₂,
      rw [neg_lt, neg_mul_eq_neg_mul, mul_lt_iff_lt_one_left two_pi_pos] at hx₁,
      norm_cast at hx₁ hx₂,
      obtain rfl : n = 0 := le_antisymm (by linarith) (by linarith),
      simp
    end,
  λ h, by simp [h]⟩

lemma cos_lt_cos_of_nonneg_of_le_pi_div_two {x y : ℝ} (hx₁ : 0 ≤ x) (hy₂ : y ≤ π / 2)
  (hxy : x < y) :
  cos y < cos x :=
begin
  rw [← sub_lt_zero, cos_sub_cos],
  have : 0 < sin ((y + x) / 2),
  { refine sin_pos_of_pos_of_lt_pi _ _; linarith },
  have : 0 < sin ((y - x) / 2),
  { refine sin_pos_of_pos_of_lt_pi _ _; linarith },
  nlinarith,
end

lemma cos_lt_cos_of_nonneg_of_le_pi {x y : ℝ} (hx₁ : 0 ≤ x) (hy₂ : y ≤ π) (hxy : x < y) :
  cos y < cos x :=
match (le_total x (π / 2) : x ≤ π / 2 ∨ π / 2 ≤ x), le_total y (π / 2) with
| or.inl hx, or.inl hy := cos_lt_cos_of_nonneg_of_le_pi_div_two hx₁ hy hxy
| or.inl hx, or.inr hy := (lt_or_eq_of_le hx).elim
  (λ hx, calc cos y ≤ 0 : cos_nonpos_of_pi_div_two_le_of_le hy (by linarith [pi_pos])
    ... < cos x : cos_pos_of_mem_Ioo ⟨by linarith, hx⟩)
  (λ hx, calc cos y < 0 : cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith [pi_pos])
    ... = cos x : by rw [hx, cos_pi_div_two])
| or.inr hx, or.inl hy := by linarith
| or.inr hx, or.inr hy := neg_lt_neg_iff.1 (by rw [← cos_pi_sub, ← cos_pi_sub];
  apply cos_lt_cos_of_nonneg_of_le_pi_div_two; linarith)
end

lemma strict_anti_on_cos : strict_anti_on cos (Icc 0 π) :=
λ x hx y hy hxy, cos_lt_cos_of_nonneg_of_le_pi hx.1 hy.2 hxy

lemma cos_le_cos_of_nonneg_of_le_pi {x y : ℝ} (hx₁ : 0 ≤ x) (hy₂ : y ≤ π) (hxy : x ≤ y) :
  cos y ≤ cos x :=
(strict_anti_on_cos.le_iff_le ⟨hx₁.trans hxy, hy₂⟩ ⟨hx₁, hxy.trans hy₂⟩).2 hxy

lemma sin_lt_sin_of_lt_of_le_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) ≤ x)
  (hy₂ : y ≤ π / 2) (hxy : x < y) : sin x < sin y :=
by rw [← cos_sub_pi_div_two, ← cos_sub_pi_div_two, ← cos_neg (x - _), ← cos_neg (y - _)];
  apply cos_lt_cos_of_nonneg_of_le_pi; linarith

lemma strict_mono_on_sin : strict_mono_on sin (Icc (-(π / 2)) (π / 2)) :=
λ x hx y hy hxy, sin_lt_sin_of_lt_of_le_pi_div_two hx.1 hy.2 hxy

lemma sin_le_sin_of_le_of_le_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) ≤ x)
  (hy₂ : y ≤ π / 2) (hxy : x ≤ y) : sin x ≤ sin y :=
(strict_mono_on_sin.le_iff_le ⟨hx₁, hxy.trans hy₂⟩ ⟨hx₁.trans hxy, hy₂⟩).2 hxy

lemma inj_on_sin : inj_on sin (Icc (-(π / 2)) (π / 2)) :=
strict_mono_on_sin.inj_on

lemma inj_on_cos : inj_on cos (Icc 0 π) := strict_anti_on_cos.inj_on

lemma surj_on_sin : surj_on sin (Icc (-(π / 2)) (π / 2)) (Icc (-1) 1) :=
by simpa only [sin_neg, sin_pi_div_two]
  using intermediate_value_Icc (neg_le_self pi_div_two_pos.le) continuous_sin.continuous_on

lemma surj_on_cos : surj_on cos (Icc 0 π) (Icc (-1) 1) :=
by simpa only [cos_zero, cos_pi]
  using intermediate_value_Icc' pi_pos.le continuous_cos.continuous_on

lemma sin_mem_Icc (x : ℝ) : sin x ∈ Icc (-1 : ℝ) 1 := ⟨neg_one_le_sin x, sin_le_one x⟩

lemma cos_mem_Icc (x : ℝ) : cos x ∈ Icc (-1 : ℝ) 1 := ⟨neg_one_le_cos x, cos_le_one x⟩

lemma maps_to_sin (s : set ℝ) : maps_to sin s (Icc (-1 : ℝ) 1) := λ x _, sin_mem_Icc x

lemma maps_to_cos (s : set ℝ) : maps_to cos s (Icc (-1 : ℝ) 1) := λ x _, cos_mem_Icc x

lemma bij_on_sin : bij_on sin (Icc (-(π / 2)) (π / 2)) (Icc (-1) 1) :=
⟨maps_to_sin _, inj_on_sin, surj_on_sin⟩

lemma bij_on_cos : bij_on cos (Icc 0 π) (Icc (-1) 1) :=
⟨maps_to_cos _, inj_on_cos, surj_on_cos⟩

@[simp] lemma range_cos : range cos = (Icc (-1) 1 : set ℝ) :=
subset.antisymm (range_subset_iff.2 cos_mem_Icc) surj_on_cos.subset_range

@[simp] lemma range_sin : range sin = (Icc (-1) 1 : set ℝ) :=
subset.antisymm (range_subset_iff.2 sin_mem_Icc) surj_on_sin.subset_range

lemma range_cos_infinite : (range real.cos).infinite :=
by { rw real.range_cos, exact Icc.infinite (by norm_num) }

lemma range_sin_infinite : (range real.sin).infinite :=
by { rw real.range_sin, exact Icc.infinite (by norm_num) }

lemma sin_lt {x : ℝ} (h : 0 < x) : sin x < x :=
begin
  cases le_or_gt x 1 with h' h',
  { have hx : abs x = x := abs_of_nonneg (le_of_lt h),
    have : abs x ≤ 1, rwa [hx],
    have := sin_bound this, rw [abs_le] at this,
    have := this.2, rw [sub_le_iff_le_add', hx] at this,
    apply lt_of_le_of_lt this, rw [sub_add], apply lt_of_lt_of_le _ (le_of_eq (sub_zero x)),
    apply sub_lt_sub_left, rw [sub_pos, div_eq_mul_inv (x ^ 3)], apply mul_lt_mul',
    { rw [pow_succ x 3], refine le_trans _ (le_of_eq (one_mul _)),
      rw mul_le_mul_right, exact h', apply pow_pos h },
    norm_num, norm_num, apply pow_pos h },
  exact lt_of_le_of_lt (sin_le_one x) h'
end

/- note 1: this inequality is not tight, the tighter inequality is sin x > x - x ^ 3 / 6.
   note 2: this is also true for x > 1, but it's nontrivial for x just above 1. -/
lemma sin_gt_sub_cube {x : ℝ} (h : 0 < x) (h' : x ≤ 1) : x - x ^ 3 / 4 < sin x :=
begin
  have hx : abs x = x := abs_of_nonneg (le_of_lt h),
  have : abs x ≤ 1, rwa [hx],
  have := sin_bound this, rw [abs_le] at this,
  have := this.1, rw [le_sub_iff_add_le, hx] at this,
  refine lt_of_lt_of_le _ this,
  rw [add_comm, sub_add, sub_neg_eq_add], apply sub_lt_sub_left,
  apply add_lt_of_lt_sub_left,
  rw (show x ^ 3 / 4 - x ^ 3 / 6 = x ^ 3 * 12⁻¹,
    by simp [div_eq_mul_inv, ← mul_sub]; norm_num),
  apply mul_lt_mul',
  { rw [pow_succ x 3], refine le_trans _ (le_of_eq (one_mul _)),
    rw mul_le_mul_right, exact h', apply pow_pos h },
  norm_num, norm_num, apply pow_pos h
end

section cos_div_sq

variable (x : ℝ)

/-- the series `sqrt_two_add_series x n` is `sqrt(2 + sqrt(2 + ... ))` with `n` square roots,
  starting with `x`. We define it here because `cos (pi / 2 ^ (n+1)) = sqrt_two_add_series 0 n / 2`
-/
@[simp, pp_nodot] noncomputable def sqrt_two_add_series (x : ℝ) : ℕ → ℝ
| 0     := x
| (n+1) := sqrt (2 + sqrt_two_add_series n)

lemma sqrt_two_add_series_zero : sqrt_two_add_series x 0 = x := by simp
lemma sqrt_two_add_series_one : sqrt_two_add_series 0 1 = sqrt 2 := by simp
lemma sqrt_two_add_series_two : sqrt_two_add_series 0 2 = sqrt (2 + sqrt 2) := by simp

lemma sqrt_two_add_series_zero_nonneg : ∀(n : ℕ), 0 ≤ sqrt_two_add_series 0 n
| 0     := le_refl 0
| (n+1) := sqrt_nonneg _

lemma sqrt_two_add_series_nonneg {x : ℝ} (h : 0 ≤ x) : ∀(n : ℕ), 0 ≤ sqrt_two_add_series x n
| 0     := h
| (n+1) := sqrt_nonneg _

lemma sqrt_two_add_series_lt_two : ∀(n : ℕ), sqrt_two_add_series 0 n < 2
| 0     := by norm_num
| (n+1) :=
  begin
    refine lt_of_lt_of_le _ (sqrt_sq zero_lt_two.le).le,
    rw [sqrt_two_add_series, sqrt_lt_sqrt_iff, ← lt_sub_iff_add_lt'],
    { refine (sqrt_two_add_series_lt_two n).trans_le _, norm_num },
    { exact add_nonneg zero_le_two (sqrt_two_add_series_zero_nonneg n) }
  end

lemma sqrt_two_add_series_succ (x : ℝ) :
  ∀(n : ℕ), sqrt_two_add_series x (n+1) = sqrt_two_add_series (sqrt (2 + x)) n
| 0     := rfl
| (n+1) := by rw [sqrt_two_add_series, sqrt_two_add_series_succ, sqrt_two_add_series]

lemma sqrt_two_add_series_monotone_left {x y : ℝ} (h : x ≤ y) :
  ∀(n : ℕ), sqrt_two_add_series x n ≤ sqrt_two_add_series y n
| 0     := h
| (n+1) :=
  begin
    rw [sqrt_two_add_series, sqrt_two_add_series],
    exact sqrt_le_sqrt (add_le_add_left (sqrt_two_add_series_monotone_left _) _)
  end

@[simp] lemma cos_pi_over_two_pow : ∀(n : ℕ), cos (π / 2 ^ (n+1)) = sqrt_two_add_series 0 n / 2
| 0     := by simp
| (n+1) :=
  begin
    have : (2 : ℝ) ≠ 0 := two_ne_zero,
    symmetry, rw [div_eq_iff_mul_eq this], symmetry,
    rw [sqrt_two_add_series, sqrt_eq_iff_sq_eq, mul_pow, cos_sq, ←mul_div_assoc,
      nat.add_succ, pow_succ, mul_div_mul_left _ _ this, cos_pi_over_two_pow, add_mul],
    congr, { norm_num },
    rw [mul_comm, sq, mul_assoc, ←mul_div_assoc, mul_div_cancel_left, ←mul_div_assoc,
        mul_div_cancel_left]; try { exact this },
    apply add_nonneg, norm_num, apply sqrt_two_add_series_zero_nonneg, norm_num,
    apply le_of_lt, apply cos_pos_of_mem_Ioo ⟨_, _⟩,
    { transitivity (0 : ℝ), rw neg_lt_zero, apply pi_div_two_pos,
      apply div_pos pi_pos, apply pow_pos, norm_num },
    apply div_lt_div' (le_refl π) _ pi_pos _,
    refine lt_of_le_of_lt (le_of_eq (pow_one _).symm) _,
    apply pow_lt_pow, norm_num, apply nat.succ_lt_succ, apply nat.succ_pos, all_goals {norm_num}
  end

lemma sin_sq_pi_over_two_pow (n : ℕ) :
  sin (π / 2 ^ (n+1)) ^ 2 = 1 - (sqrt_two_add_series 0 n / 2) ^ 2 :=
by rw [sin_sq, cos_pi_over_two_pow]

lemma sin_sq_pi_over_two_pow_succ (n : ℕ) :
  sin (π / 2 ^ (n+2)) ^ 2 = 1 / 2 - sqrt_two_add_series 0 n / 4 :=
begin
  rw [sin_sq_pi_over_two_pow, sqrt_two_add_series, div_pow, sq_sqrt, add_div, ←sub_sub],
  congr, norm_num, norm_num, apply add_nonneg, norm_num, apply sqrt_two_add_series_zero_nonneg,
end

@[simp] lemma sin_pi_over_two_pow_succ (n : ℕ) :
  sin (π / 2 ^ (n+2)) = sqrt (2 - sqrt_two_add_series 0 n) / 2 :=
begin
  symmetry, rw [div_eq_iff_mul_eq], symmetry,
  rw [sqrt_eq_iff_sq_eq, mul_pow, sin_sq_pi_over_two_pow_succ, sub_mul],
  { congr, norm_num, rw [mul_comm], convert mul_div_cancel' _ _, norm_num, norm_num },
  { rw [sub_nonneg], apply le_of_lt, apply sqrt_two_add_series_lt_two },
  apply le_of_lt, apply mul_pos, apply sin_pos_of_pos_of_lt_pi,
  { apply div_pos pi_pos, apply pow_pos, norm_num },
  refine lt_of_lt_of_le _ (le_of_eq (div_one _)), rw [div_lt_div_left],
  refine lt_of_le_of_lt (le_of_eq (pow_zero 2).symm) _,
  apply pow_lt_pow, norm_num, apply nat.succ_pos, apply pi_pos,
  apply pow_pos, all_goals {norm_num}
end

@[simp] lemma cos_pi_div_four : cos (π / 4) = sqrt 2 / 2 :=
by { transitivity cos (π / 2 ^ 2), congr, norm_num, simp }

@[simp] lemma sin_pi_div_four : sin (π / 4) = sqrt 2 / 2 :=
by { transitivity sin (π / 2 ^ 2), congr, norm_num, simp }

@[simp] lemma cos_pi_div_eight : cos (π / 8) = sqrt (2 + sqrt 2) / 2 :=
by { transitivity cos (π / 2 ^ 3), congr, norm_num, simp }

@[simp] lemma sin_pi_div_eight : sin (π / 8) = sqrt (2 - sqrt 2) / 2 :=
by { transitivity sin (π / 2 ^ 3), congr, norm_num, simp }

@[simp] lemma cos_pi_div_sixteen : cos (π / 16) = sqrt (2 + sqrt (2 + sqrt 2)) / 2 :=
by { transitivity cos (π / 2 ^ 4), congr, norm_num, simp }

@[simp] lemma sin_pi_div_sixteen : sin (π / 16) = sqrt (2 - sqrt (2 + sqrt 2)) / 2 :=
by { transitivity sin (π / 2 ^ 4), congr, norm_num, simp }

@[simp] lemma cos_pi_div_thirty_two : cos (π / 32) = sqrt (2 + sqrt (2 + sqrt (2 + sqrt 2))) / 2 :=
by { transitivity cos (π / 2 ^ 5), congr, norm_num, simp }

@[simp] lemma sin_pi_div_thirty_two : sin (π / 32) = sqrt (2 - sqrt (2 + sqrt (2 + sqrt 2))) / 2 :=
by { transitivity sin (π / 2 ^ 5), congr, norm_num, simp }

-- This section is also a convenient location for other explicit values of `sin` and `cos`.

/-- The cosine of `π / 3` is `1 / 2`. -/
@[simp] lemma cos_pi_div_three : cos (π / 3) = 1 / 2 :=
begin
  have h₁ : (2 * cos (π / 3) - 1) ^ 2 * (2 * cos (π / 3) + 2) = 0,
  { have : cos (3 * (π / 3)) = cos π := by { congr' 1, ring },
    linarith [cos_pi, cos_three_mul (π / 3)] },
  cases mul_eq_zero.mp h₁ with h h,
  { linarith [pow_eq_zero h] },
  { have : cos π < cos (π / 3),
    { refine cos_lt_cos_of_nonneg_of_le_pi _ rfl.ge _;
      linarith [pi_pos] },
    linarith [cos_pi] }
end

/-- The square of the cosine of `π / 6` is `3 / 4` (this is sometimes more convenient than the
result for cosine itself). -/
lemma sq_cos_pi_div_six : cos (π / 6) ^ 2 = 3 / 4 :=
begin
  have h1 : cos (π / 6) ^ 2 = 1 / 2 + 1 / 2 / 2,
  { convert cos_sq (π / 6),
    have h2 : 2 * (π / 6) = π / 3 := by cancel_denoms,
    rw [h2, cos_pi_div_three] },
  rw ← sub_eq_zero at h1 ⊢,
  convert h1 using 1,
  ring
end

/-- The cosine of `π / 6` is `√3 / 2`. -/
@[simp] lemma cos_pi_div_six : cos (π / 6) = (sqrt 3) / 2 :=
begin
  suffices : sqrt 3 = cos (π / 6) * 2,
  { field_simp [(by norm_num : 0 ≠ 2)], exact this.symm },
  rw sqrt_eq_iff_sq_eq,
  { have h1 := (mul_right_inj' (by norm_num : (4:ℝ) ≠ 0)).mpr sq_cos_pi_div_six,
    rw ← sub_eq_zero at h1 ⊢,
    convert h1 using 1,
    ring },
  { norm_num },
  { have : 0 < cos (π / 6) := by { apply cos_pos_of_mem_Ioo; split; linarith [pi_pos] },
    linarith },
end

/-- The sine of `π / 6` is `1 / 2`. -/
@[simp] lemma sin_pi_div_six : sin (π / 6) = 1 / 2 :=
begin
  rw [← cos_pi_div_two_sub, ← cos_pi_div_three],
  congr,
  ring
end

/-- The square of the sine of `π / 3` is `3 / 4` (this is sometimes more convenient than the
result for cosine itself). -/
lemma sq_sin_pi_div_three : sin (π / 3) ^ 2 = 3 / 4 :=
begin
  rw [← cos_pi_div_two_sub, ← sq_cos_pi_div_six],
  congr,
  ring
end

/-- The sine of `π / 3` is `√3 / 2`. -/
@[simp] lemma sin_pi_div_three : sin (π / 3) = (sqrt 3) / 2 :=
begin
  rw [← cos_pi_div_two_sub, ← cos_pi_div_six],
  congr,
  ring
end

end cos_div_sq

/-- The type of angles -/
def angle : Type :=
quotient_add_group.quotient (add_subgroup.gmultiples (2 * π))

namespace angle

instance angle.add_comm_group : add_comm_group angle :=
quotient_add_group.add_comm_group _

instance : inhabited angle := ⟨0⟩

instance angle.has_coe : has_coe ℝ angle :=
⟨quotient.mk'⟩

@[simp] lemma coe_zero : ↑(0 : ℝ) = (0 : angle) := rfl
@[simp] lemma coe_add (x y : ℝ) : ↑(x + y : ℝ) = (↑x + ↑y : angle) := rfl
@[simp] lemma coe_neg (x : ℝ) : ↑(-x : ℝ) = -(↑x : angle) := rfl
@[simp] lemma coe_sub (x y : ℝ) : ↑(x - y : ℝ) = (↑x - ↑y : angle) :=
by rw [sub_eq_add_neg, sub_eq_add_neg, coe_add, coe_neg]

@[simp, norm_cast] lemma coe_nat_mul_eq_nsmul (x : ℝ) (n : ℕ) :
  ↑((n : ℝ) * x) = n • (↑x : angle) :=
by simpa using add_monoid_hom.map_nsmul ⟨coe, coe_zero, coe_add⟩ _ _
@[simp, norm_cast] lemma coe_int_mul_eq_gsmul (x : ℝ) (n : ℤ) :
  ↑((n : ℝ) * x : ℝ) = n • (↑x : angle) :=
by simpa using add_monoid_hom.map_gsmul ⟨coe, coe_zero, coe_add⟩ _ _

@[simp] lemma coe_two_pi : ↑(2 * π : ℝ) = (0 : angle) :=
quotient.sound' ⟨-1, show (-1 : ℤ) • (2 * π) = _, by rw [neg_one_gsmul, add_zero]⟩

lemma angle_eq_iff_two_pi_dvd_sub {ψ θ : ℝ} : (θ : angle) = ψ ↔ ∃ k : ℤ, θ - ψ = 2 * π * k :=
by simp only [quotient_add_group.eq, add_subgroup.gmultiples_eq_closure,
  add_subgroup.mem_closure_singleton, gsmul_eq_mul', (sub_eq_neg_add _ _).symm, eq_comm]

theorem cos_eq_iff_eq_or_eq_neg {θ ψ : ℝ} : cos θ = cos ψ ↔ (θ : angle) = ψ ∨ (θ : angle) = -ψ :=
begin
  split,
  { intro Hcos,
    rw [← sub_eq_zero, cos_sub_cos, mul_eq_zero, mul_eq_zero, neg_eq_zero,
        eq_false_intro two_ne_zero, false_or, sin_eq_zero_iff, sin_eq_zero_iff] at Hcos,
    rcases Hcos with ⟨n, hn⟩ | ⟨n, hn⟩,
    { right,
      rw [eq_div_iff_mul_eq (@two_ne_zero ℝ _ _), ← sub_eq_iff_eq_add] at hn,
      rw [← hn, coe_sub, eq_neg_iff_add_eq_zero, sub_add_cancel, mul_assoc,
          coe_int_mul_eq_gsmul, mul_comm, coe_two_pi, gsmul_zero] },
    { left,
      rw [eq_div_iff_mul_eq (@two_ne_zero ℝ _ _), eq_sub_iff_add_eq] at hn,
      rw [← hn, coe_add, mul_assoc,
          coe_int_mul_eq_gsmul, mul_comm, coe_two_pi, gsmul_zero, zero_add] },
    apply_instance, },
  { rw [angle_eq_iff_two_pi_dvd_sub, ← coe_neg, angle_eq_iff_two_pi_dvd_sub],
    rintro (⟨k, H⟩ | ⟨k, H⟩),
    rw [← sub_eq_zero, cos_sub_cos, H, mul_assoc 2 π k,
        mul_div_cancel_left _ (@two_ne_zero ℝ _ _), mul_comm π _, sin_int_mul_pi, mul_zero],
    rw [← sub_eq_zero, cos_sub_cos, ← sub_neg_eq_add, H, mul_assoc 2 π k,
        mul_div_cancel_left _ (@two_ne_zero ℝ _ _), mul_comm π _, sin_int_mul_pi, mul_zero,
        zero_mul] }
end

theorem sin_eq_iff_eq_or_add_eq_pi {θ ψ : ℝ} :
  sin θ = sin ψ ↔ (θ : angle) = ψ ∨ (θ : angle) + ψ = π :=
begin
  split,
  { intro Hsin, rw [← cos_pi_div_two_sub, ← cos_pi_div_two_sub] at Hsin,
    cases cos_eq_iff_eq_or_eq_neg.mp Hsin with h h,
    { left, rw [coe_sub, coe_sub] at h, exact sub_right_inj.1 h },
      right, rw [coe_sub, coe_sub, eq_neg_iff_add_eq_zero, add_sub,
      sub_add_eq_add_sub, ← coe_add, add_halves, sub_sub, sub_eq_zero] at h,
    exact h.symm },
  { rw [angle_eq_iff_two_pi_dvd_sub, ←eq_sub_iff_add_eq, ←coe_sub, angle_eq_iff_two_pi_dvd_sub],
    rintro (⟨k, H⟩ | ⟨k, H⟩),
    rw [← sub_eq_zero, sin_sub_sin, H, mul_assoc 2 π k,
         mul_div_cancel_left _ (@two_ne_zero ℝ _ _), mul_comm π _, sin_int_mul_pi, mul_zero,
         zero_mul],
    have H' : θ + ψ = (2 * k) * π + π := by rwa [←sub_add, sub_add_eq_add_sub, sub_eq_iff_eq_add,
      mul_assoc, mul_comm π _, ←mul_assoc] at H,
    rw [← sub_eq_zero, sin_sub_sin, H', add_div, mul_assoc 2 _ π,
        mul_div_cancel_left _ (@two_ne_zero ℝ _ _), cos_add_pi_div_two, sin_int_mul_pi, neg_zero,
        mul_zero] }
end

theorem cos_sin_inj {θ ψ : ℝ} (Hcos : cos θ = cos ψ) (Hsin : sin θ = sin ψ) : (θ : angle) = ψ :=
begin
  cases cos_eq_iff_eq_or_eq_neg.mp Hcos with hc hc, { exact hc },
  cases sin_eq_iff_eq_or_add_eq_pi.mp Hsin with hs hs, { exact hs },
  rw [eq_neg_iff_add_eq_zero, hs] at hc,
  cases quotient.exact' hc with n hn, change n • _ = _ at hn,
  rw [← neg_one_mul, add_zero, ← sub_eq_zero, gsmul_eq_mul, ← mul_assoc, ← sub_mul,
      mul_eq_zero, eq_false_intro (ne_of_gt pi_pos), or_false, sub_neg_eq_add,
      ← int.cast_zero, ← int.cast_one, ← int.cast_bit0, ← int.cast_mul, ← int.cast_add,
      int.cast_inj] at hn,
  have : (n * 2 + 1) % (2:ℤ) = 0 % (2:ℤ) := congr_arg (%(2:ℤ)) hn,
  rw [add_comm, int.add_mul_mod_self] at this,
  exact absurd this one_ne_zero
end

end angle

/-- `real.sin` as an `order_iso` between `[-(π / 2), π / 2]` and `[-1, 1]`. -/
def sin_order_iso : Icc (-(π / 2)) (π / 2) ≃o Icc (-1:ℝ) 1 :=
(strict_mono_on_sin.order_iso _ _).trans $ order_iso.set_congr _ _ bij_on_sin.image_eq

@[simp] lemma coe_sin_order_iso_apply (x : Icc (-(π / 2)) (π / 2)) :
  (sin_order_iso x : ℝ) = sin x := rfl

lemma sin_order_iso_apply (x : Icc (-(π / 2)) (π / 2)) :
  sin_order_iso x = ⟨sin x, sin_mem_Icc x⟩ := rfl

@[simp] lemma tan_pi_div_four : tan (π / 4) = 1 :=
begin
  rw [tan_eq_sin_div_cos, cos_pi_div_four, sin_pi_div_four],
  have h : (sqrt 2) / 2 > 0 := by cancel_denoms,
  exact div_self (ne_of_gt h),
end

@[simp] lemma tan_pi_div_two : tan (π / 2) = 0 := by simp [tan_eq_sin_div_cos]

lemma tan_pos_of_pos_of_lt_pi_div_two {x : ℝ} (h0x : 0 < x) (hxp : x < π / 2) : 0 < tan x :=
by rw tan_eq_sin_div_cos; exact div_pos (sin_pos_of_pos_of_lt_pi h0x (by linarith))
  (cos_pos_of_mem_Ioo ⟨by linarith, hxp⟩)

lemma tan_nonneg_of_nonneg_of_le_pi_div_two {x : ℝ} (h0x : 0 ≤ x) (hxp : x ≤ π / 2) : 0 ≤ tan x :=
match lt_or_eq_of_le h0x, lt_or_eq_of_le hxp with
| or.inl hx0, or.inl hxp := le_of_lt (tan_pos_of_pos_of_lt_pi_div_two hx0 hxp)
| or.inl hx0, or.inr hxp := by simp [hxp, tan_eq_sin_div_cos]
| or.inr hx0, _          := by simp [hx0.symm]
end

lemma tan_neg_of_neg_of_pi_div_two_lt {x : ℝ} (hx0 : x < 0) (hpx : -(π / 2) < x) : tan x < 0 :=
neg_pos.1 (tan_neg x ▸ tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith [pi_pos]))

lemma tan_nonpos_of_nonpos_of_neg_pi_div_two_le {x : ℝ} (hx0 : x ≤ 0) (hpx : -(π / 2) ≤ x) :
  tan x ≤ 0 :=
neg_nonneg.1 (tan_neg x ▸ tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith))

lemma tan_lt_tan_of_nonneg_of_lt_pi_div_two {x y : ℝ}
  (hx₁ : 0 ≤ x) (hy₂ : y < π / 2) (hxy : x < y) :
  tan x < tan y :=
begin
  rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos],
  exact div_lt_div
    (sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (le_of_lt hy₂) hxy)
    (cos_le_cos_of_nonneg_of_le_pi hx₁ (by linarith) (le_of_lt hxy))
    (sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))
    (cos_pos_of_mem_Ioo ⟨by linarith, hy₂⟩)
end

lemma tan_lt_tan_of_lt_of_lt_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) < x)
 (hy₂ : y < π / 2) (hxy : x < y) : tan x < tan y :=
match le_total x 0, le_total y 0 with
| or.inl hx0, or.inl hy0 := neg_lt_neg_iff.1 $ by rw [← tan_neg, ← tan_neg]; exact
  tan_lt_tan_of_nonneg_of_lt_pi_div_two (neg_nonneg.2 hy0)
    (neg_lt.2 hx₁) (neg_lt_neg hxy)
| or.inl hx0, or.inr hy0 := (lt_or_eq_of_le hy0).elim
  (λ hy0, calc tan x ≤ 0 : tan_nonpos_of_nonpos_of_neg_pi_div_two_le hx0 (le_of_lt hx₁)
    ... < tan y : tan_pos_of_pos_of_lt_pi_div_two hy0 hy₂)
  (λ hy0, by rw [← hy0, tan_zero]; exact
    tan_neg_of_neg_of_pi_div_two_lt (hy0.symm ▸ hxy) hx₁)
| or.inr hx0, or.inl hy0 := by linarith
| or.inr hx0, or.inr hy0 := tan_lt_tan_of_nonneg_of_lt_pi_div_two hx0 hy₂ hxy
end

lemma strict_mono_on_tan : strict_mono_on tan (Ioo (-(π / 2)) (π / 2)) :=
λ x hx y hy, tan_lt_tan_of_lt_of_lt_pi_div_two hx.1 hy.2

lemma inj_on_tan : inj_on tan (Ioo (-(π / 2)) (π / 2)) :=
strict_mono_on_tan.inj_on

lemma tan_inj_of_lt_of_lt_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) < x) (hx₂ : x < π / 2)
  (hy₁ : -(π / 2) < y) (hy₂ : y < π / 2) (hxy : tan x = tan y) : x = y :=
inj_on_tan ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩ hxy

lemma tan_periodic : function.periodic tan π :=
by simpa only [function.periodic, tan_eq_sin_div_cos] using sin_antiperiodic.div cos_antiperiodic

lemma tan_add_pi (x : ℝ) : tan (x + π) = tan x :=
tan_periodic x

lemma tan_sub_pi (x : ℝ) : tan (x - π) = tan x :=
tan_periodic.sub_eq x

lemma tan_pi_sub (x : ℝ) : tan (π - x) = -tan x :=
tan_neg x ▸ tan_periodic.sub_eq'

lemma tan_nat_mul_pi (n : ℕ) : tan (n * π) = 0 :=
tan_zero ▸ tan_periodic.nat_mul_eq n

lemma tan_int_mul_pi (n : ℤ) : tan (n * π) = 0 :=
tan_zero ▸ tan_periodic.int_mul_eq n

lemma tan_add_nat_mul_pi (x : ℝ) (n : ℕ) : tan (x + n * π) = tan x :=
tan_periodic.nat_mul n x

lemma tan_add_int_mul_pi (x : ℝ) (n : ℤ) : tan (x + n * π) = tan x :=
tan_periodic.int_mul n x

lemma tan_sub_nat_mul_pi (x : ℝ) (n : ℕ) : tan (x - n * π) = tan x :=
tan_periodic.sub_nat_mul_eq n

lemma tan_sub_int_mul_pi (x : ℝ) (n : ℤ) : tan (x - n * π) = tan x :=
tan_periodic.sub_int_mul_eq n

lemma tan_nat_mul_pi_sub (x : ℝ) (n : ℕ) : tan (n * π - x) = -tan x :=
tan_neg x ▸ tan_periodic.nat_mul_sub_eq n

lemma tan_int_mul_pi_sub (x : ℝ) (n : ℤ) : tan (n * π - x) = -tan x :=
tan_neg x ▸ tan_periodic.int_mul_sub_eq n


lemma tendsto_sin_pi_div_two : tendsto sin (𝓝[Iio (π/2)] (π/2)) (𝓝 1) :=
by { convert continuous_sin.continuous_within_at, simp }

lemma tendsto_cos_pi_div_two : tendsto cos (𝓝[Iio (π/2)] (π/2)) (𝓝[Ioi 0] 0) :=
begin
  apply tendsto_nhds_within_of_tendsto_nhds_of_eventually_within,
  { convert continuous_cos.continuous_within_at, simp },
  { filter_upwards [Ioo_mem_nhds_within_Iio (right_mem_Ioc.mpr (norm_num.lt_neg_pos
      _ _ pi_div_two_pos pi_div_two_pos))] λ x hx, cos_pos_of_mem_Ioo hx },
end

lemma tendsto_tan_pi_div_two : tendsto tan (𝓝[Iio (π/2)] (π/2)) at_top :=
begin
  convert tendsto_cos_pi_div_two.inv_tendsto_zero.at_top_mul zero_lt_one
            tendsto_sin_pi_div_two,
  simp only [pi.inv_apply, ← div_eq_inv_mul, ← tan_eq_sin_div_cos]
end

lemma tendsto_sin_neg_pi_div_two : tendsto sin (𝓝[Ioi (-(π/2))] (-(π/2))) (𝓝 (-1)) :=
by { convert continuous_sin.continuous_within_at, simp }

lemma tendsto_cos_neg_pi_div_two : tendsto cos (𝓝[Ioi (-(π/2))] (-(π/2))) (𝓝[Ioi 0] 0) :=
begin
  apply tendsto_nhds_within_of_tendsto_nhds_of_eventually_within,
  { convert continuous_cos.continuous_within_at, simp },
  { filter_upwards [Ioo_mem_nhds_within_Ioi (left_mem_Ico.mpr (norm_num.lt_neg_pos
      _ _ pi_div_two_pos pi_div_two_pos))] λ x hx, cos_pos_of_mem_Ioo hx },
end

lemma tendsto_tan_neg_pi_div_two : tendsto tan (𝓝[Ioi (-(π/2))] (-(π/2))) at_bot :=
begin
  convert tendsto_cos_neg_pi_div_two.inv_tendsto_zero.at_top_mul_neg (by norm_num)
            tendsto_sin_neg_pi_div_two,
  simp only [pi.inv_apply, ← div_eq_inv_mul, ← tan_eq_sin_div_cos]
end

end real

namespace complex

open_locale real

lemma sin_eq_zero_iff_cos_eq {z : ℂ} : sin z = 0 ↔ cos z = 1 ∨ cos z = -1 :=
by rw [← mul_self_eq_one_iff, ← sin_sq_add_cos_sq, sq, sq, ← sub_eq_iff_eq_add, sub_self];
  exact ⟨λ h, by rw [h, mul_zero], eq_zero_of_mul_self_eq_zero ∘ eq.symm⟩

@[simp] lemma cos_pi_div_two : cos (π / 2) = 0 :=
calc cos (π / 2) = real.cos (π / 2) : by rw [of_real_cos]; simp
... = 0 : by simp

@[simp] lemma sin_pi_div_two : sin (π / 2) = 1 :=
calc sin (π / 2) = real.sin (π / 2) : by rw [of_real_sin]; simp
... = 1 : by simp

@[simp] lemma sin_pi : sin π = 0 :=
by rw [← of_real_sin, real.sin_pi]; simp

@[simp] lemma cos_pi : cos π = -1 :=
by rw [← of_real_cos, real.cos_pi]; simp

@[simp] lemma sin_two_pi : sin (2 * π) = 0 :=
by simp [two_mul, sin_add]

@[simp] lemma cos_two_pi : cos (2 * π) = 1 :=
by simp [two_mul, cos_add]

lemma sin_antiperiodic : function.antiperiodic sin π :=
by simp [sin_add]

lemma sin_periodic : function.periodic sin (2 * π) :=
sin_antiperiodic.periodic

lemma sin_add_pi (x : ℂ) : sin (x + π) = -sin x :=
sin_antiperiodic x

lemma sin_add_two_pi (x : ℂ) : sin (x + 2 * π) = sin x :=
sin_periodic x

lemma sin_sub_pi (x : ℂ) : sin (x - π) = -sin x :=
sin_antiperiodic.sub_eq x

lemma sin_sub_two_pi (x : ℂ) : sin (x - 2 * π) = sin x :=
sin_periodic.sub_eq x

lemma sin_pi_sub (x : ℂ) : sin (π - x) = sin x :=
neg_neg (sin x) ▸ sin_neg x ▸ sin_antiperiodic.sub_eq'

lemma sin_two_pi_sub (x : ℂ) : sin (2 * π - x) = -sin x :=
sin_neg x ▸ sin_periodic.sub_eq'

lemma sin_nat_mul_pi (n : ℕ) : sin (n * π) = 0 :=
sin_antiperiodic.nat_mul_eq_of_eq_zero sin_zero n

lemma sin_int_mul_pi (n : ℤ) : sin (n * π) = 0 :=
sin_antiperiodic.int_mul_eq_of_eq_zero sin_zero n

lemma sin_add_nat_mul_two_pi (x : ℂ) (n : ℕ) : sin (x + n * (2 * π)) = sin x :=
sin_periodic.nat_mul n x

lemma sin_add_int_mul_two_pi (x : ℂ) (n : ℤ) : sin (x + n * (2 * π)) = sin x :=
sin_periodic.int_mul n x

lemma sin_sub_nat_mul_two_pi (x : ℂ) (n : ℕ) : sin (x - n * (2 * π)) = sin x :=
sin_periodic.sub_nat_mul_eq n

lemma sin_sub_int_mul_two_pi (x : ℂ) (n : ℤ) : sin (x - n * (2 * π)) = sin x :=
sin_periodic.sub_int_mul_eq n

lemma sin_nat_mul_two_pi_sub (x : ℂ) (n : ℕ) : sin (n * (2 * π) - x) = -sin x :=
sin_neg x ▸ sin_periodic.nat_mul_sub_eq n

lemma sin_int_mul_two_pi_sub (x : ℂ) (n : ℤ) : sin (n * (2 * π) - x) = -sin x :=
sin_neg x ▸ sin_periodic.int_mul_sub_eq n

lemma cos_antiperiodic : function.antiperiodic cos π :=
by simp [cos_add]

lemma cos_periodic : function.periodic cos (2 * π) :=
cos_antiperiodic.periodic

lemma cos_add_pi (x : ℂ) : cos (x + π) = -cos x :=
cos_antiperiodic x

lemma cos_add_two_pi (x : ℂ) : cos (x + 2 * π) = cos x :=
cos_periodic x

lemma cos_sub_pi (x : ℂ) : cos (x - π) = -cos x :=
cos_antiperiodic.sub_eq x

lemma cos_sub_two_pi (x : ℂ) : cos (x - 2 * π) = cos x :=
cos_periodic.sub_eq x

lemma cos_pi_sub (x : ℂ) : cos (π - x) = -cos x :=
cos_neg x ▸ cos_antiperiodic.sub_eq'

lemma cos_two_pi_sub (x : ℂ) : cos (2 * π - x) = cos x :=
cos_neg x ▸ cos_periodic.sub_eq'

lemma cos_nat_mul_two_pi (n : ℕ) : cos (n * (2 * π)) = 1 :=
(cos_periodic.nat_mul_eq n).trans cos_zero

lemma cos_int_mul_two_pi (n : ℤ) : cos (n * (2 * π)) = 1 :=
(cos_periodic.int_mul_eq n).trans cos_zero

lemma cos_add_nat_mul_two_pi (x : ℂ) (n : ℕ) : cos (x + n * (2 * π)) = cos x :=
cos_periodic.nat_mul n x

lemma cos_add_int_mul_two_pi (x : ℂ) (n : ℤ) : cos (x + n * (2 * π)) = cos x :=
cos_periodic.int_mul n x

lemma cos_sub_nat_mul_two_pi (x : ℂ) (n : ℕ) : cos (x - n * (2 * π)) = cos x :=
cos_periodic.sub_nat_mul_eq n

lemma cos_sub_int_mul_two_pi (x : ℂ) (n : ℤ) : cos (x - n * (2 * π)) = cos x :=
cos_periodic.sub_int_mul_eq n

lemma cos_nat_mul_two_pi_sub (x : ℂ) (n : ℕ) : cos (n * (2 * π) - x) = cos x :=
cos_neg x ▸ cos_periodic.nat_mul_sub_eq n

lemma cos_int_mul_two_pi_sub (x : ℂ) (n : ℤ) : cos (n * (2 * π) - x) = cos x :=
cos_neg x ▸ cos_periodic.int_mul_sub_eq n

lemma cos_nat_mul_two_pi_add_pi (n : ℕ) : cos (n * (2 * π) + π) = -1 :=
by simpa only [cos_zero] using (cos_periodic.nat_mul n).add_antiperiod_eq cos_antiperiodic

lemma cos_int_mul_two_pi_add_pi (n : ℤ) : cos (n * (2 * π) + π) = -1 :=
by simpa only [cos_zero] using (cos_periodic.int_mul n).add_antiperiod_eq cos_antiperiodic

lemma cos_nat_mul_two_pi_sub_pi (n : ℕ) : cos (n * (2 * π) - π) = -1 :=
by simpa only [cos_zero] using (cos_periodic.nat_mul n).sub_antiperiod_eq cos_antiperiodic

lemma cos_int_mul_two_pi_sub_pi (n : ℤ) : cos (n * (2 * π) - π) = -1 :=
by simpa only [cos_zero] using (cos_periodic.int_mul n).sub_antiperiod_eq cos_antiperiodic

lemma sin_add_pi_div_two (x : ℂ) : sin (x + π / 2) = cos x :=
by simp [sin_add]

lemma sin_sub_pi_div_two (x : ℂ) : sin (x - π / 2) = -cos x :=
by simp [sub_eq_add_neg, sin_add]

lemma sin_pi_div_two_sub (x : ℂ) : sin (π / 2 - x) = cos x :=
by simp [sub_eq_add_neg, sin_add]

lemma cos_add_pi_div_two (x : ℂ) : cos (x + π / 2) = -sin x :=
by simp [cos_add]

lemma cos_sub_pi_div_two (x : ℂ) : cos (x - π / 2) = sin x :=
by simp [sub_eq_add_neg, cos_add]

lemma cos_pi_div_two_sub (x : ℂ) : cos (π / 2 - x) = sin x :=
by rw [← cos_neg, neg_sub, cos_sub_pi_div_two]

lemma tan_periodic : function.periodic tan π :=
by simpa only [tan_eq_sin_div_cos] using sin_antiperiodic.div cos_antiperiodic

lemma tan_add_pi (x : ℂ) : tan (x + π) = tan x :=
tan_periodic x

lemma tan_sub_pi (x : ℂ) : tan (x - π) = tan x :=
tan_periodic.sub_eq x

lemma tan_pi_sub (x : ℂ) : tan (π - x) = -tan x :=
tan_neg x ▸ tan_periodic.sub_eq'

lemma tan_nat_mul_pi (n : ℕ) : tan (n * π) = 0 :=
tan_zero ▸ tan_periodic.nat_mul_eq n

lemma tan_int_mul_pi (n : ℤ) : tan (n * π) = 0 :=
tan_zero ▸ tan_periodic.int_mul_eq n

lemma tan_add_nat_mul_pi (x : ℂ) (n : ℕ) : tan (x + n * π) = tan x :=
tan_periodic.nat_mul n x

lemma tan_add_int_mul_pi (x : ℂ) (n : ℤ) : tan (x + n * π) = tan x :=
tan_periodic.int_mul n x

lemma tan_sub_nat_mul_pi (x : ℂ) (n : ℕ) : tan (x - n * π) = tan x :=
tan_periodic.sub_nat_mul_eq n

lemma tan_sub_int_mul_pi (x : ℂ) (n : ℤ) : tan (x - n * π) = tan x :=
tan_periodic.sub_int_mul_eq n

lemma tan_nat_mul_pi_sub (x : ℂ) (n : ℕ) : tan (n * π - x) = -tan x :=
tan_neg x ▸ tan_periodic.nat_mul_sub_eq n

lemma tan_int_mul_pi_sub (x : ℂ) (n : ℤ) : tan (n * π - x) = -tan x :=
tan_neg x ▸ tan_periodic.int_mul_sub_eq n

lemma exp_antiperiodic : function.antiperiodic exp (π * I) :=
by simp [exp_add, exp_mul_I]

lemma exp_periodic : function.periodic exp (2 * π * I) :=
(mul_assoc (2:ℂ) π I).symm ▸ exp_antiperiodic.periodic

lemma exp_mul_I_antiperiodic : function.antiperiodic (λ x, exp (x * I)) π :=
by simpa only [mul_inv_cancel_right' I_ne_zero] using exp_antiperiodic.mul_const I_ne_zero

lemma exp_mul_I_periodic : function.periodic (λ x, exp (x * I)) (2 * π) :=
exp_mul_I_antiperiodic.periodic

lemma exp_pi_mul_I : exp (π * I) = -1 :=
exp_zero ▸ exp_antiperiodic.eq

lemma exp_two_pi_mul_I : exp (2 * π * I) = 1 :=
exp_periodic.eq.trans exp_zero

lemma exp_nat_mul_two_pi_mul_I (n : ℕ) : exp (n * (2 * π * I)) = 1 :=
(exp_periodic.nat_mul_eq n).trans exp_zero

lemma exp_int_mul_two_pi_mul_I (n : ℤ) : exp (n * (2 * π * I)) = 1 :=
(exp_periodic.int_mul_eq n).trans exp_zero

end complex
