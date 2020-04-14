/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
import tactic.linarith data.complex.exponential analysis.specific_limits
      group_theory.quotient_group analysis.complex.basic


/-!
# Exponential

## Main definitions

This file contains the following definitions:
* π, arcsin, arccos, arctan
* argument of a complex number
* logarithm on real and complex numbers
* complex and real power function

## Main statements

The following functions are shown to be continuous:
* complex and real exponential function
* sin, cos, tan, sinh, cosh
* logarithm on real numbers
* real power function
* square root function

The following functions are shown to be differentiable, and their derivatives are computed:
  * complex and real exponential function
  * sin, cos, sinh, cosh

## Tags

exp, log, sin, cos, tan, arcsin, arccos, arctan, angle, argument, power, square root,

-/
noncomputable theory

open finset filter metric asymptotics
open_locale classical
open_locale topological_space

namespace complex

/-- The complex exponential is everywhere differentiable, with the derivative `exp x`. -/
lemma has_deriv_at_exp (x : ℂ) : has_deriv_at exp (exp x) x :=
begin
  rw has_deriv_at_iff_is_o_nhds_zero,
  have : (1 : ℕ) < 2 := by norm_num,
  refine is_O.trans_is_o ⟨∥exp x∥, _⟩ (is_o_pow_id this),
  have : metric.ball (0 : ℂ) 1 ∈ nhds (0 : ℂ) := metric.ball_mem_nhds 0 zero_lt_one,
  apply filter.mem_sets_of_superset this (λz hz, _),
  simp only [metric.mem_ball, dist_zero_right] at hz,
  simp only [exp_zero, mul_one, one_mul, add_comm, normed_field.norm_pow,
             zero_add, set.mem_set_of_eq],
  calc ∥exp (x + z) - exp x - z * exp x∥
    = ∥exp x * (exp z - 1 - z)∥ : by { congr, rw [exp_add], ring }
    ... = ∥exp x∥ * ∥exp z - 1 - z∥ : normed_field.norm_mul _ _
    ... ≤ ∥exp x∥ * ∥z∥^2 :
      mul_le_mul_of_nonneg_left (abs_exp_sub_one_sub_id_le (le_of_lt hz)) (norm_nonneg _)
end

@[simp] lemma differentiable_exp : differentiable ℂ exp :=
λx, (has_deriv_at_exp x).differentiable_at

@[simp] lemma differentiable_at_exp {x : ℂ} : differentiable_at ℂ exp x :=
differentiable_exp x

@[simp] lemma deriv_exp : deriv exp = exp :=
funext $ λ x, (has_deriv_at_exp x).deriv

@[simp] lemma iter_deriv_exp : ∀ n : ℕ, (deriv^[n] exp) = exp
| 0 := rfl
| (n+1) := by rw [nat.iterate_succ, deriv_exp, iter_deriv_exp n]

lemma continuous_exp : continuous exp :=
differentiable_exp.continuous

end complex

section
variables {f : ℂ → ℂ} {f' x : ℂ} {s : set ℂ}

lemma has_deriv_at.cexp (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, complex.exp (f x)) (complex.exp (f x) * f') x :=
(complex.has_deriv_at_exp (f x)).comp x hf

lemma has_deriv_within_at.cexp (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, complex.exp (f x)) (complex.exp (f x) * f') s x :=
(complex.has_deriv_at_exp (f x)).comp_has_deriv_within_at x hf

lemma differentiable_within_at.cexp (hf : differentiable_within_at ℂ f s x) :
  differentiable_within_at ℂ (λ x, complex.exp (f x)) s x :=
hf.has_deriv_within_at.cexp.differentiable_within_at

@[simp] lemma differentiable_at.cexp (hc : differentiable_at ℂ f x) :
  differentiable_at ℂ (λx, complex.exp (f x)) x :=
hc.has_deriv_at.cexp.differentiable_at

lemma differentiable_on.cexp (hc : differentiable_on ℂ f s) :
  differentiable_on ℂ (λx, complex.exp (f x)) s :=
λx h, (hc x h).cexp

@[simp] lemma differentiable.cexp (hc : differentiable ℂ f) :
  differentiable ℂ (λx, complex.exp (f x)) :=
λx, (hc x).cexp

lemma deriv_within_cexp (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  deriv_within (λx, complex.exp (f x)) s x = complex.exp (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.cexp.deriv_within hxs

@[simp] lemma deriv_cexp (hc : differentiable_at ℂ f x) :
  deriv (λx, complex.exp (f x)) x = complex.exp (f x) * (deriv f x) :=
hc.has_deriv_at.cexp.deriv

end

namespace complex

/-- The complex sine function is everywhere differentiable, with the derivative `cos x`. -/
lemma has_deriv_at_sin (x : ℂ) : has_deriv_at sin (cos x) x :=
begin
  simp only [cos, div_eq_mul_inv],
  convert ((((has_deriv_at_id x).neg.mul_const I).cexp.sub
    ((has_deriv_at_id x).mul_const I).cexp).mul_const I).mul_const (2:ℂ)⁻¹,
  simp only [function.comp, id],
  rw [sub_mul, mul_assoc, mul_assoc, I_mul_I, neg_one_mul, neg_neg, mul_one, one_mul, mul_assoc,
      I_mul_I, mul_neg_one, sub_neg_eq_add, add_comm]
end

@[simp] lemma differentiable_sin : differentiable ℂ sin :=
λx, (has_deriv_at_sin x).differentiable_at

@[simp] lemma differentiable_at_sin {x : ℂ} : differentiable_at ℂ sin x :=
differentiable_sin x

@[simp] lemma deriv_sin : deriv sin = cos :=
funext $ λ x, (has_deriv_at_sin x).deriv

lemma continuous_sin : continuous sin :=
differentiable_sin.continuous

/-- The complex cosine function is everywhere differentiable, with the derivative `-sin x`. -/
lemma has_deriv_at_cos (x : ℂ) : has_deriv_at cos (-sin x) x :=
begin
  simp only [sin, div_eq_mul_inv, neg_mul_eq_neg_mul],
  convert (((has_deriv_at_id x).mul_const I).cexp.add
    ((has_deriv_at_id x).neg.mul_const I).cexp).mul_const (2:ℂ)⁻¹,
  simp only [function.comp, id],
  ring
end

@[simp] lemma differentiable_cos : differentiable ℂ cos :=
λx, (has_deriv_at_cos x).differentiable_at

@[simp] lemma differentiable_at_cos {x : ℂ} : differentiable_at ℂ cos x :=
differentiable_cos x

lemma deriv_cos {x : ℂ} : deriv cos x = -sin x :=
(has_deriv_at_cos x).deriv

@[simp] lemma deriv_cos' : deriv cos = (λ x, -sin x) :=
funext $ λ x, deriv_cos

lemma continuous_cos : continuous cos :=
differentiable_cos.continuous

lemma continuous_tan : continuous (λ x : {x // cos x ≠ 0}, tan x) :=
(continuous_sin.comp continuous_subtype_val).mul
  (continuous.inv subtype.property (continuous_cos.comp continuous_subtype_val))

/-- The complex hyperbolic sine function is everywhere differentiable, with the derivative `sinh x`. -/
lemma has_deriv_at_sinh (x : ℂ) : has_deriv_at sinh (cosh x) x :=
begin
  simp only [cosh, div_eq_mul_inv],
  convert ((has_deriv_at_exp x).sub (has_deriv_at_id x).neg.cexp).mul_const (2:ℂ)⁻¹,
  rw [id, mul_neg_one, neg_neg]
end

@[simp] lemma differentiable_sinh : differentiable ℂ sinh :=
λx, (has_deriv_at_sinh x).differentiable_at

@[simp] lemma differentiable_at_sinh {x : ℂ} : differentiable_at ℂ sinh x :=
differentiable_sinh x

@[simp] lemma deriv_sinh : deriv sinh = cosh :=
funext $ λ x, (has_deriv_at_sinh x).deriv

lemma continuous_sinh : continuous sinh :=
differentiable_sinh.continuous

/-- The complex hyperbolic cosine function is everywhere differentiable, with the derivative `cosh x`. -/
lemma has_deriv_at_cosh (x : ℂ) : has_deriv_at cosh (sinh x) x :=
begin
  simp only [sinh, div_eq_mul_inv],
  convert ((has_deriv_at_exp x).add (has_deriv_at_id x).neg.cexp).mul_const (2:ℂ)⁻¹,
  rw [id, mul_neg_one, sub_eq_add_neg]
end

@[simp] lemma differentiable_cosh : differentiable ℂ cosh :=
λx, (has_deriv_at_cosh x).differentiable_at

@[simp] lemma differentiable_at_cosh {x : ℂ} : differentiable_at ℂ cos x :=
differentiable_cos x

@[simp] lemma deriv_cosh : deriv cosh = sinh :=
funext $ λ x, (has_deriv_at_cosh x).deriv

lemma continuous_cosh : continuous cosh :=
differentiable_cosh.continuous

end complex

section
/-! Register lemmas for the derivatives of the composition of `complex.cos`, `complex.sin`,
`complex.cosh` and `complex.sinh` with a differentiable function, for standalone use and use with
`simp`. -/

variables {f : ℂ → ℂ} {f' x : ℂ} {s : set ℂ}

/-! `complex.cos`-/

lemma has_deriv_at.ccos (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, complex.cos (f x)) (- complex.sin (f x) * f') x :=
(complex.has_deriv_at_cos (f x)).comp x hf

lemma has_deriv_within_at.ccos (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, complex.cos (f x)) (- complex.sin (f x) * f') s x :=
(complex.has_deriv_at_cos (f x)).comp_has_deriv_within_at x hf

lemma differentiable_within_at.ccos (hf : differentiable_within_at ℂ f s x) :
  differentiable_within_at ℂ (λ x, complex.cos (f x)) s x :=
hf.has_deriv_within_at.ccos.differentiable_within_at

@[simp] lemma differentiable_at.ccos (hc : differentiable_at ℂ f x) :
  differentiable_at ℂ (λx, complex.cos (f x)) x :=
hc.has_deriv_at.ccos.differentiable_at

lemma differentiable_on.ccos (hc : differentiable_on ℂ f s) :
  differentiable_on ℂ (λx, complex.cos (f x)) s :=
λx h, (hc x h).ccos

@[simp] lemma differentiable.ccos (hc : differentiable ℂ f) :
  differentiable ℂ (λx, complex.cos (f x)) :=
λx, (hc x).ccos

lemma deriv_within_ccos (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  deriv_within (λx, complex.cos (f x)) s x = - complex.sin (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.ccos.deriv_within hxs

@[simp] lemma deriv_ccos (hc : differentiable_at ℂ f x) :
  deriv (λx, complex.cos (f x)) x = - complex.sin (f x) * (deriv f x) :=
hc.has_deriv_at.ccos.deriv

/-! `complex.sin`-/

lemma has_deriv_at.csin (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, complex.sin (f x)) (complex.cos (f x) * f') x :=
(complex.has_deriv_at_sin (f x)).comp x hf

lemma has_deriv_within_at.csin (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, complex.sin (f x)) (complex.cos (f x) * f') s x :=
(complex.has_deriv_at_sin (f x)).comp_has_deriv_within_at x hf

lemma differentiable_within_at.csin (hf : differentiable_within_at ℂ f s x) :
  differentiable_within_at ℂ (λ x, complex.sin (f x)) s x :=
hf.has_deriv_within_at.csin.differentiable_within_at

@[simp] lemma differentiable_at.csin (hc : differentiable_at ℂ f x) :
  differentiable_at ℂ (λx, complex.sin (f x)) x :=
hc.has_deriv_at.csin.differentiable_at

lemma differentiable_on.csin (hc : differentiable_on ℂ f s) :
  differentiable_on ℂ (λx, complex.sin (f x)) s :=
λx h, (hc x h).csin

@[simp] lemma differentiable.csin (hc : differentiable ℂ f) :
  differentiable ℂ (λx, complex.sin (f x)) :=
λx, (hc x).csin

lemma deriv_within_csin (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  deriv_within (λx, complex.sin (f x)) s x = complex.cos (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.csin.deriv_within hxs

@[simp] lemma deriv_csin (hc : differentiable_at ℂ f x) :
  deriv (λx, complex.sin (f x)) x = complex.cos (f x) * (deriv f x) :=
hc.has_deriv_at.csin.deriv

/-! `complex.cosh`-/

lemma has_deriv_at.ccosh (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, complex.cosh (f x)) (complex.sinh (f x) * f') x :=
(complex.has_deriv_at_cosh (f x)).comp x hf

lemma has_deriv_within_at.ccosh (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, complex.cosh (f x)) (complex.sinh (f x) * f') s x :=
(complex.has_deriv_at_cosh (f x)).comp_has_deriv_within_at x hf

lemma differentiable_within_at.ccosh (hf : differentiable_within_at ℂ f s x) :
  differentiable_within_at ℂ (λ x, complex.cosh (f x)) s x :=
hf.has_deriv_within_at.ccosh.differentiable_within_at

@[simp] lemma differentiable_at.ccosh (hc : differentiable_at ℂ f x) :
  differentiable_at ℂ (λx, complex.cosh (f x)) x :=
hc.has_deriv_at.ccosh.differentiable_at

lemma differentiable_on.ccosh (hc : differentiable_on ℂ f s) :
  differentiable_on ℂ (λx, complex.cosh (f x)) s :=
λx h, (hc x h).ccosh

@[simp] lemma differentiable.ccosh (hc : differentiable ℂ f) :
  differentiable ℂ (λx, complex.cosh (f x)) :=
λx, (hc x).ccosh

lemma deriv_within_ccosh (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  deriv_within (λx, complex.cosh (f x)) s x = complex.sinh (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.ccosh.deriv_within hxs

@[simp] lemma deriv_ccosh (hc : differentiable_at ℂ f x) :
  deriv (λx, complex.cosh (f x)) x = complex.sinh (f x) * (deriv f x) :=
hc.has_deriv_at.ccosh.deriv

/-! `complex.sinh`-/

lemma has_deriv_at.csinh (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, complex.sinh (f x)) (complex.cosh (f x) * f') x :=
(complex.has_deriv_at_sinh (f x)).comp x hf

lemma has_deriv_within_at.csinh (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, complex.sinh (f x)) (complex.cosh (f x) * f') s x :=
(complex.has_deriv_at_sinh (f x)).comp_has_deriv_within_at x hf

lemma differentiable_within_at.csinh (hf : differentiable_within_at ℂ f s x) :
  differentiable_within_at ℂ (λ x, complex.sinh (f x)) s x :=
hf.has_deriv_within_at.csinh.differentiable_within_at

@[simp] lemma differentiable_at.csinh (hc : differentiable_at ℂ f x) :
  differentiable_at ℂ (λx, complex.sinh (f x)) x :=
hc.has_deriv_at.csinh.differentiable_at

lemma differentiable_on.csinh (hc : differentiable_on ℂ f s) :
  differentiable_on ℂ (λx, complex.sinh (f x)) s :=
λx h, (hc x h).csinh

@[simp] lemma differentiable.csinh (hc : differentiable ℂ f) :
  differentiable ℂ (λx, complex.sinh (f x)) :=
λx, (hc x).csinh

lemma deriv_within_csinh (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  deriv_within (λx, complex.sinh (f x)) s x = complex.cosh (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.csinh.deriv_within hxs

@[simp] lemma deriv_csinh (hc : differentiable_at ℂ f x) :
  deriv (λx, complex.sinh (f x)) x = complex.cosh (f x) * (deriv f x) :=
hc.has_deriv_at.csinh.deriv

end

namespace real

variables {x y z : ℝ}

lemma has_deriv_at_exp (x : ℝ) : has_deriv_at exp (exp x) x :=
has_deriv_at_real_of_complex (complex.has_deriv_at_exp x)

@[simp] lemma differentiable_exp : differentiable ℝ exp :=
λx, (has_deriv_at_exp x).differentiable_at

@[simp] lemma differentiable_at_exp : differentiable_at ℝ exp x :=
differentiable_exp x

@[simp] lemma deriv_exp : deriv exp = exp :=
funext $ λ x, (has_deriv_at_exp x).deriv

@[simp] lemma iter_deriv_exp : ∀ n : ℕ, (deriv^[n] exp) = exp
| 0 := rfl
| (n+1) := by rw [nat.iterate_succ, deriv_exp, iter_deriv_exp n]

lemma continuous_exp : continuous exp :=
differentiable_exp.continuous

lemma has_deriv_at_sin (x : ℝ) : has_deriv_at sin (cos x) x :=
has_deriv_at_real_of_complex (complex.has_deriv_at_sin x)

@[simp] lemma differentiable_sin : differentiable ℝ sin :=
λx, (has_deriv_at_sin x).differentiable_at

@[simp] lemma differentiable_at_sin : differentiable_at ℝ sin x :=
differentiable_sin x

@[simp] lemma deriv_sin : deriv sin = cos :=
funext $ λ x, (has_deriv_at_sin x).deriv

lemma continuous_sin : continuous sin :=
differentiable_sin.continuous

lemma has_deriv_at_cos (x : ℝ) : has_deriv_at cos (-sin x) x :=
(has_deriv_at_real_of_complex (complex.has_deriv_at_cos x) : _)

@[simp] lemma differentiable_cos : differentiable ℝ cos :=
λx, (has_deriv_at_cos x).differentiable_at

@[simp] lemma differentiable_at_cos : differentiable_at ℝ cos x :=
differentiable_cos x

lemma deriv_cos : deriv cos x = - sin x :=
(has_deriv_at_cos x).deriv

@[simp] lemma deriv_cos' : deriv cos = (λ x, - sin x) :=
funext $ λ _, deriv_cos

lemma continuous_cos : continuous cos :=
differentiable_cos.continuous

lemma continuous_tan : continuous (λ x : {x // cos x ≠ 0}, tan x) :=
by simp only [tan_eq_sin_div_cos]; exact
  (continuous_sin.comp continuous_subtype_val).mul
  (continuous.inv subtype.property
    (continuous_cos.comp continuous_subtype_val))

lemma has_deriv_at_sinh (x : ℝ) : has_deriv_at sinh (cosh x) x :=
has_deriv_at_real_of_complex (complex.has_deriv_at_sinh x)

@[simp] lemma differentiable_sinh : differentiable ℝ sinh :=
λx, (has_deriv_at_sinh x).differentiable_at

@[simp] lemma differentiable_at_sinh : differentiable_at ℝ sinh x :=
differentiable_sinh x

@[simp] lemma deriv_sinh : deriv sinh = cosh :=
funext $ λ x, (has_deriv_at_sinh x).deriv

lemma continuous_sinh : continuous sinh :=
differentiable_sinh.continuous

lemma has_deriv_at_cosh (x : ℝ) : has_deriv_at cosh (sinh x) x :=
has_deriv_at_real_of_complex (complex.has_deriv_at_cosh x)

@[simp] lemma differentiable_cosh : differentiable ℝ cosh :=
λx, (has_deriv_at_cosh x).differentiable_at

@[simp] lemma differentiable_at_cosh : differentiable_at ℝ cosh x :=
differentiable_cosh x

@[simp] lemma deriv_cosh : deriv cosh = sinh :=
funext $ λ x, (has_deriv_at_cosh x).deriv

lemma continuous_cosh : continuous cosh :=
differentiable_cosh.continuous

end real


section
/-! Register lemmas for the derivatives of the composition of `real.exp`, `real.cos`, `real.sin`,
`real.cosh` and `real.sinh` with a differentiable function, for standalone use and use with
`simp`. -/

variables {f : ℝ → ℝ} {f' x : ℝ} {s : set ℝ}

/-! `real.exp`-/

lemma has_deriv_at.exp (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, real.exp (f x)) (real.exp (f x) * f') x :=
(real.has_deriv_at_exp (f x)).comp x hf

lemma has_deriv_within_at.exp (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, real.exp (f x)) (real.exp (f x) * f') s x :=
(real.has_deriv_at_exp (f x)).comp_has_deriv_within_at x hf

lemma differentiable_within_at.exp (hf : differentiable_within_at ℝ f s x) :
  differentiable_within_at ℝ (λ x, real.exp (f x)) s x :=
hf.has_deriv_within_at.exp.differentiable_within_at

@[simp] lemma differentiable_at.exp (hc : differentiable_at ℝ f x) :
  differentiable_at ℝ (λx, real.exp (f x)) x :=
hc.has_deriv_at.exp.differentiable_at

lemma differentiable_on.exp (hc : differentiable_on ℝ f s) :
  differentiable_on ℝ (λx, real.exp (f x)) s :=
λx h, (hc x h).exp

@[simp] lemma differentiable.exp (hc : differentiable ℝ f) :
  differentiable ℝ (λx, real.exp (f x)) :=
λx, (hc x).exp

lemma deriv_within_exp (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λx, real.exp (f x)) s x = real.exp (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.exp.deriv_within hxs

@[simp] lemma deriv_exp (hc : differentiable_at ℝ f x) :
  deriv (λx, real.exp (f x)) x = real.exp (f x) * (deriv f x) :=
hc.has_deriv_at.exp.deriv

/-! `real.cos`-/

lemma has_deriv_at.cos (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, real.cos (f x)) (- real.sin (f x) * f') x :=
(real.has_deriv_at_cos (f x)).comp x hf

lemma has_deriv_within_at.cos (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, real.cos (f x)) (- real.sin (f x) * f') s x :=
(real.has_deriv_at_cos (f x)).comp_has_deriv_within_at x hf

lemma differentiable_within_at.cos (hf : differentiable_within_at ℝ f s x) :
  differentiable_within_at ℝ (λ x, real.cos (f x)) s x :=
hf.has_deriv_within_at.cos.differentiable_within_at

@[simp] lemma differentiable_at.cos (hc : differentiable_at ℝ f x) :
  differentiable_at ℝ (λx, real.cos (f x)) x :=
hc.has_deriv_at.cos.differentiable_at

lemma differentiable_on.cos (hc : differentiable_on ℝ f s) :
  differentiable_on ℝ (λx, real.cos (f x)) s :=
λx h, (hc x h).cos

@[simp] lemma differentiable.cos (hc : differentiable ℝ f) :
  differentiable ℝ (λx, real.cos (f x)) :=
λx, (hc x).cos

lemma deriv_within_cos (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λx, real.cos (f x)) s x = - real.sin (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.cos.deriv_within hxs

@[simp] lemma deriv_cos (hc : differentiable_at ℝ f x) :
  deriv (λx, real.cos (f x)) x = - real.sin (f x) * (deriv f x) :=
hc.has_deriv_at.cos.deriv

/-! `real.sin`-/

lemma has_deriv_at.sin (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, real.sin (f x)) (real.cos (f x) * f') x :=
(real.has_deriv_at_sin (f x)).comp x hf

lemma has_deriv_within_at.sin (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, real.sin (f x)) (real.cos (f x) * f') s x :=
(real.has_deriv_at_sin (f x)).comp_has_deriv_within_at x hf

lemma differentiable_within_at.sin (hf : differentiable_within_at ℝ f s x) :
  differentiable_within_at ℝ (λ x, real.sin (f x)) s x :=
hf.has_deriv_within_at.sin.differentiable_within_at

@[simp] lemma differentiable_at.sin (hc : differentiable_at ℝ f x) :
  differentiable_at ℝ (λx, real.sin (f x)) x :=
hc.has_deriv_at.sin.differentiable_at

lemma differentiable_on.sin (hc : differentiable_on ℝ f s) :
  differentiable_on ℝ (λx, real.sin (f x)) s :=
λx h, (hc x h).sin

@[simp] lemma differentiable.sin (hc : differentiable ℝ f) :
  differentiable ℝ (λx, real.sin (f x)) :=
λx, (hc x).sin

lemma deriv_within_sin (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λx, real.sin (f x)) s x = real.cos (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.sin.deriv_within hxs

@[simp] lemma deriv_sin (hc : differentiable_at ℝ f x) :
  deriv (λx, real.sin (f x)) x = real.cos (f x) * (deriv f x) :=
hc.has_deriv_at.sin.deriv

/-! `real.cosh`-/

lemma has_deriv_at.cosh (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, real.cosh (f x)) (real.sinh (f x) * f') x :=
(real.has_deriv_at_cosh (f x)).comp x hf

lemma has_deriv_within_at.cosh (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, real.cosh (f x)) (real.sinh (f x) * f') s x :=
(real.has_deriv_at_cosh (f x)).comp_has_deriv_within_at x hf

lemma differentiable_within_at.cosh (hf : differentiable_within_at ℝ f s x) :
  differentiable_within_at ℝ (λ x, real.cosh (f x)) s x :=
hf.has_deriv_within_at.cosh.differentiable_within_at

@[simp] lemma differentiable_at.cosh (hc : differentiable_at ℝ f x) :
  differentiable_at ℝ (λx, real.cosh (f x)) x :=
hc.has_deriv_at.cosh.differentiable_at

lemma differentiable_on.cosh (hc : differentiable_on ℝ f s) :
  differentiable_on ℝ (λx, real.cosh (f x)) s :=
λx h, (hc x h).cosh

@[simp] lemma differentiable.cosh (hc : differentiable ℝ f) :
  differentiable ℝ (λx, real.cosh (f x)) :=
λx, (hc x).cosh

lemma deriv_within_cosh (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λx, real.cosh (f x)) s x = real.sinh (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.cosh.deriv_within hxs

@[simp] lemma deriv_cosh (hc : differentiable_at ℝ f x) :
  deriv (λx, real.cosh (f x)) x = real.sinh (f x) * (deriv f x) :=
hc.has_deriv_at.cosh.deriv

/-! `real.sinh`-/

lemma has_deriv_at.sinh (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, real.sinh (f x)) (real.cosh (f x) * f') x :=
(real.has_deriv_at_sinh (f x)).comp x hf

lemma has_deriv_within_at.sinh (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, real.sinh (f x)) (real.cosh (f x) * f') s x :=
(real.has_deriv_at_sinh (f x)).comp_has_deriv_within_at x hf

lemma differentiable_within_at.sinh (hf : differentiable_within_at ℝ f s x) :
  differentiable_within_at ℝ (λ x, real.sinh (f x)) s x :=
hf.has_deriv_within_at.sinh.differentiable_within_at

@[simp] lemma differentiable_at.sinh (hc : differentiable_at ℝ f x) :
  differentiable_at ℝ (λx, real.sinh (f x)) x :=
hc.has_deriv_at.sinh.differentiable_at

lemma differentiable_on.sinh (hc : differentiable_on ℝ f s) :
  differentiable_on ℝ (λx, real.sinh (f x)) s :=
λx h, (hc x h).sinh

@[simp] lemma differentiable.sinh (hc : differentiable ℝ f) :
  differentiable ℝ (λx, real.sinh (f x)) :=
λx, (hc x).sinh

lemma deriv_within_sinh (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λx, real.sinh (f x)) s x = real.cosh (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.sinh.deriv_within hxs

@[simp] lemma deriv_sinh (hc : differentiable_at ℝ f x) :
  deriv (λx, real.sinh (f x)) x = real.cosh (f x) * (deriv f x) :=
hc.has_deriv_at.sinh.deriv

end

namespace real

variables {x y z : ℝ}

lemma exists_exp_eq_of_pos {x : ℝ} (hx : 0 < x) : ∃ y, exp y = x :=
have ∀ {z:ℝ}, 1 ≤ z → z ∈ set.range exp,
  from λ z hz, intermediate_value_univ 0 (z - 1) continuous_exp
    ⟨by simpa, by simpa using add_one_le_exp_of_nonneg (sub_nonneg.2 hz)⟩,
match le_total x 1 with
| (or.inl hx1) := let ⟨y, hy⟩ := this (one_le_inv hx hx1) in
  ⟨-y, by rw [exp_neg, hy, inv_inv']⟩
| (or.inr hx1) := this hx1
end

/-- The real logarithm function, equal to `0` for `x ≤ 0` and to the inverse of the exponential
for `x > 0`. -/
noncomputable def log (x : ℝ) : ℝ :=
if hx : 0 < x then classical.some (exists_exp_eq_of_pos hx) else 0

lemma exp_log {x : ℝ} (hx : 0 < x) : exp (log x) = x :=
by rw [log, dif_pos hx]; exact classical.some_spec (exists_exp_eq_of_pos hx)

@[simp] lemma log_exp (x : ℝ) : log (exp x) = x :=
exp_injective $ exp_log (exp_pos x)

@[simp] lemma log_zero : log 0 = 0 :=
by simp [log, lt_irrefl]

@[simp] lemma log_one : log 1 = 0 :=
exp_injective $ by rw [exp_log zero_lt_one, exp_zero]

lemma log_mul {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : log (x * y) = log x + log y :=
exp_injective $ by rw [exp_log (mul_pos hx hy), exp_add, exp_log hx, exp_log hy]

lemma log_le_log {x y : ℝ} (h : 0 < x) (h₁ : 0 < y) : real.log x ≤ real.log y ↔ x ≤ y :=
⟨λ h₂, by rwa [←real.exp_le_exp, real.exp_log h, real.exp_log h₁] at h₂, λ h₂,
(real.exp_le_exp).1 $ by rwa [real.exp_log h₁, real.exp_log h]⟩

lemma log_lt_log (hx : 0 < x) : x < y → log x < log y :=
by { intro h, rwa [← exp_lt_exp, exp_log hx, exp_log (lt_trans hx h)] }

lemma log_lt_log_iff (hx : 0 < x) (hy : 0 < y) : log x < log y ↔ x < y :=
by { rw [← exp_lt_exp, exp_log hx, exp_log hy] }

lemma log_pos_iff (x : ℝ) : 0 < log x ↔ 1 < x :=
begin
  by_cases h : 0 < x,
  { rw ← log_one, exact log_lt_log_iff (by norm_num) h },
  { rw [log, dif_neg], split, repeat {intro, linarith} }
end

lemma log_pos : 1 < x → 0 < log x := (log_pos_iff x).2

lemma log_neg_iff (h : 0 < x) : log x < 0 ↔ x < 1 :=
by { rw ← log_one, exact log_lt_log_iff h (by norm_num) }

lemma log_neg (h0 : 0 < x) (h1 : x < 1) : log x < 0 := (log_neg_iff h0).2 h1

lemma log_nonneg : 1 ≤ x → 0 ≤ log x :=
by { intro, rwa [← log_one, log_le_log], norm_num, linarith }

lemma log_nonpos : x ≤ 1 → log x ≤ 0 :=
begin
  intro, by_cases hx : 0 < x,
  { rwa [← log_one, log_le_log], exact hx, norm_num },
  { simp [log, dif_neg hx] }
end

section prove_log_is_continuous

lemma tendsto_log_one_zero : tendsto log (𝓝 1) (𝓝 0) :=
begin
  rw tendsto_nhds_nhds, assume ε ε0,
  let δ := min (exp ε - 1) (1 - exp (-ε)),
  have : 0 < δ,
    refine lt_min (sub_pos_of_lt (by rwa one_lt_exp_iff)) (sub_pos_of_lt _),
      by { rw exp_lt_one_iff, linarith },
  use [δ, this], assume x h,
  cases le_total 1 x with hx hx,
  { have h : x < exp ε,
      rw [dist_eq, abs_of_nonneg (sub_nonneg_of_le hx)] at h,
      linarith [(min_le_left _ _ : δ ≤ exp ε - 1)],
    calc abs (log x - 0) = abs (log x) : by simp
      ... = log x : abs_of_nonneg $ log_nonneg hx
      ... < ε : by { rwa [← exp_lt_exp, exp_log], linarith }},
  { have h : exp (-ε) < x,
      rw [dist_eq, abs_of_nonpos (sub_nonpos_of_le hx)] at h,
      linarith [(min_le_right _ _ : δ ≤ 1 - exp (-ε))],
    have : 0 < x := lt_trans (exp_pos _) h,
    calc abs (log x - 0) = abs (log x) : by simp
      ... = -log x : abs_of_nonpos $ log_nonpos hx
      ... < ε : by { rw [neg_lt, ← exp_lt_exp, exp_log], assumption' } }
end

lemma continuous_log' : continuous (λx : {x:ℝ // 0 < x}, log x.val) :=
continuous_iff_continuous_at.2 $ λ x,
begin
  rw continuous_at,
  let f₁ := λ h:{h:ℝ // 0 < h}, log (x.1 * h.1),
  let f₂ := λ y:{y:ℝ // 0 < y}, subtype.mk (x.1 ⁻¹ * y.1) (mul_pos (inv_pos.2 x.2) y.2),
  have H1 : tendsto f₁ (𝓝 ⟨1, zero_lt_one⟩) (𝓝 (log (x.1*1))),
    have : f₁ = λ h:{h:ℝ // 0 < h}, log x.1 + log h.1,
      ext h, rw ← log_mul x.2 h.2,
    simp only [this, log_mul x.2 zero_lt_one, log_one],
    exact tendsto_const_nhds.add (tendsto.comp tendsto_log_one_zero continuous_at_subtype_val),
  have H2 : tendsto f₂ (𝓝 x) (𝓝 ⟨x.1⁻¹ * x.1, mul_pos (inv_pos.2 x.2) x.2⟩),
    rw tendsto_subtype_rng, exact tendsto_const_nhds.mul continuous_at_subtype_val,
  suffices h : tendsto (f₁ ∘ f₂) (𝓝 x) (𝓝 (log x.1)),
  begin
    convert h, ext y,
    have : x.val * (x.val⁻¹ * y.val) = y.val,
      rw [← mul_assoc, mul_inv_cancel (ne_of_gt x.2), one_mul],
    show log (y.val) = log (x.val * (x.val⁻¹ * y.val)), rw this
  end,
  exact tendsto.comp (by rwa mul_one at H1)
    (by { simp only [inv_mul_cancel (ne_of_gt x.2)] at H2, assumption })
end

lemma continuous_at_log (hx : 0 < x) : continuous_at log x :=
continuous_within_at.continuous_at (continuous_on_iff_continuous_restrict.2 continuous_log' _ hx)
  (mem_nhds_sets (is_open_lt' _) hx)

/--
Three forms of the continuity of `real.log` is provided.
For the other two forms, see `real.continuous_log'` and `real.continuous_at_log`
-/
lemma continuous_log {α : Type*} [topological_space α] {f : α → ℝ} (h : ∀a, 0 < f a)
  (hf : continuous f) : continuous (λa, log (f a)) :=
show continuous ((log ∘ @subtype.val ℝ (λr, 0 < r)) ∘ λa, ⟨f a, h a⟩),
  from continuous_log'.comp (continuous_subtype_mk _ hf)

end prove_log_is_continuous

lemma exists_cos_eq_zero : 0 ∈ cos '' set.Icc (1:ℝ) 2 :=
intermediate_value_Icc' (by norm_num) continuous_cos.continuous_on
  ⟨le_of_lt cos_two_neg, le_of_lt cos_one_pos⟩

/-- The number π = 3.14159265... Defined here using choice as twice a zero of cos in [1,2], from
which one can derive all its properties. For explicit bounds on π, see `data.real.pi`. -/
noncomputable def pi : ℝ := 2 * classical.some exists_cos_eq_zero

localized "notation `π` := real.pi" in real

@[simp] lemma cos_pi_div_two : cos (π / 2) = 0 :=
by rw [pi, mul_div_cancel_left _ (@two_ne_zero' ℝ _ _ _)];
  exact (classical.some_spec exists_cos_eq_zero).2

lemma one_le_pi_div_two : (1 : ℝ) ≤ π / 2 :=
by rw [pi, mul_div_cancel_left _ (@two_ne_zero' ℝ _ _ _)];
  exact (classical.some_spec exists_cos_eq_zero).1.1

lemma pi_div_two_le_two : π / 2 ≤ 2 :=
by rw [pi, mul_div_cancel_left _ (@two_ne_zero' ℝ _ _ _)];
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

lemma pi_div_two_pos : 0 < π / 2 :=
half_pos pi_pos

lemma two_pi_pos : 0 < 2 * π :=
by linarith [pi_pos]

@[simp] lemma sin_pi : sin π = 0 :=
by rw [← mul_div_cancel_left pi (@two_ne_zero ℝ _), two_mul, add_div,
    sin_add, cos_pi_div_two]; simp

@[simp] lemma cos_pi : cos π = -1 :=
by rw [← mul_div_cancel_left pi (@two_ne_zero ℝ _), mul_div_assoc,
    cos_two_mul, cos_pi_div_two];
  simp [bit0, pow_add]

@[simp] lemma sin_two_pi : sin (2 * π) = 0 :=
by simp [two_mul, sin_add]

@[simp] lemma cos_two_pi : cos (2 * π) = 1 :=
by simp [two_mul, cos_add]

lemma sin_add_pi (x : ℝ) : sin (x + π) = -sin x :=
by simp [sin_add]

lemma sin_add_two_pi (x : ℝ) : sin (x + 2 * π) = sin x :=
by simp [sin_add_pi, sin_add, sin_two_pi, cos_two_pi]

lemma cos_add_two_pi (x : ℝ) : cos (x + 2 * π) = cos x :=
by simp [cos_add, cos_two_pi, sin_two_pi]

lemma sin_pi_sub (x : ℝ) : sin (π - x) = sin x :=
by simp [sub_eq_add_neg, sin_add]

lemma cos_add_pi (x : ℝ) : cos (x + π) = -cos x :=
by simp [cos_add]

lemma cos_pi_sub (x : ℝ) : cos (π - x) = -cos x :=
by simp [sub_eq_add_neg, cos_add]

lemma sin_pos_of_pos_of_lt_pi {x : ℝ} (h0x : 0 < x) (hxp : x < π) : 0 < sin x :=
if hx2 : x ≤ 2 then sin_pos_of_pos_of_le_two h0x hx2
else
  have (2 : ℝ) + 2 = 4, from rfl,
  have π - x ≤ 2, from sub_le_iff_le_add.2
    (le_trans pi_le_four (this ▸ add_le_add_left (le_of_not_ge hx2) _)),
  sin_pi_sub x ▸ sin_pos_of_pos_of_le_two (sub_pos.2 hxp) this

lemma sin_nonneg_of_nonneg_of_le_pi {x : ℝ} (h0x : 0 ≤ x) (hxp : x ≤ π) : 0 ≤ sin x :=
match lt_or_eq_of_le h0x with
| or.inl h0x := (lt_or_eq_of_le hxp).elim
  (le_of_lt ∘ sin_pos_of_pos_of_lt_pi h0x)
  (λ hpx, by simp [hpx])
| or.inr h0x := by simp [h0x.symm]
end

lemma sin_neg_of_neg_of_neg_pi_lt {x : ℝ} (hx0 : x < 0) (hpx : -π < x) : sin x < 0 :=
neg_pos.1 $ sin_neg x ▸ sin_pos_of_pos_of_lt_pi (neg_pos.2 hx0) (neg_lt.1 hpx)

lemma sin_nonpos_of_nonnpos_of_neg_pi_le {x : ℝ} (hx0 : x ≤ 0) (hpx : -π ≤ x) : sin x ≤ 0 :=
neg_nonneg.1 $ sin_neg x ▸ sin_nonneg_of_nonneg_of_le_pi (neg_nonneg.2 hx0) (neg_le.1 hpx)

@[simp] lemma sin_pi_div_two : sin (π / 2) = 1 :=
have sin (π / 2) = 1 ∨ sin (π / 2) = -1 :=
by simpa [pow_two, mul_self_eq_one_iff] using sin_sq_add_cos_sq (π / 2),
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

lemma cos_pos_of_neg_pi_div_two_lt_of_lt_pi_div_two
  {x : ℝ} (hx₁ : -(π / 2) < x) (hx₂ : x < π / 2) : 0 < cos x :=
sin_add_pi_div_two x ▸ sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)

lemma cos_nonneg_of_neg_pi_div_two_le_of_le_pi_div_two
  {x : ℝ} (hx₁ : -(π / 2) ≤ x) (hx₂ : x ≤ π / 2) : 0 ≤ cos x :=
match lt_or_eq_of_le hx₁, lt_or_eq_of_le hx₂ with
| or.inl hx₁, or.inl hx₂ := le_of_lt (cos_pos_of_neg_pi_div_two_lt_of_lt_pi_div_two hx₁ hx₂)
| or.inl hx₁, or.inr hx₂ := by simp [hx₂]
| or.inr hx₁, _          := by simp [hx₁.symm]
end

lemma cos_neg_of_pi_div_two_lt_of_lt {x : ℝ} (hx₁ : π / 2 < x) (hx₂ : x < π + π / 2) : cos x < 0 :=
neg_pos.1 $ cos_pi_sub x ▸
  cos_pos_of_neg_pi_div_two_lt_of_lt_pi_div_two (by linarith) (by linarith)

lemma cos_nonpos_of_pi_div_two_le_of_le {x : ℝ} (hx₁ : π / 2 ≤ x) (hx₂ : x ≤ π + π / 2) : cos x ≤ 0 :=
neg_nonneg.1 $ cos_pi_sub x ▸
  cos_nonneg_of_neg_pi_div_two_le_of_le_pi_div_two (by linarith) (by linarith)

lemma sin_nat_mul_pi (n : ℕ) : sin (n * π) = 0 :=
by induction n; simp [add_mul, sin_add, *]

lemma sin_int_mul_pi (n : ℤ) : sin (n * π) = 0 :=
by cases n; simp [add_mul, sin_add, *, sin_nat_mul_pi]

lemma cos_nat_mul_two_pi (n : ℕ) : cos (n * (2 * π)) = 1 :=
by induction n; simp [*, mul_add, cos_add, add_mul, cos_two_pi, sin_two_pi]

lemma cos_int_mul_two_pi (n : ℤ) : cos (n * (2 * π)) = 1 :=
by cases n; simp only [cos_nat_mul_two_pi, int.of_nat_eq_coe,
  int.neg_succ_of_nat_coe, int.cast_coe_nat, int.cast_neg,
  (neg_mul_eq_neg_mul _ _).symm, cos_neg]

lemma cos_int_mul_two_pi_add_pi (n : ℤ) : cos (n * (2 * π) + π) = -1 :=
by simp [cos_add, sin_add, cos_int_mul_two_pi]

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
  (sub_nonpos.1 $ le_of_not_gt $ λ h₃, ne_of_lt (sin_pos_of_pos_of_lt_pi h₃ (sub_floor_div_mul_lt _ pi_pos))
    (by simp [sub_eq_add_neg, sin_add, h, sin_int_mul_pi]))⟩,
  λ ⟨n, hn⟩, hn ▸ sin_int_mul_pi _⟩

lemma sin_eq_zero_iff_cos_eq {x : ℝ} : sin x = 0 ↔ cos x = 1 ∨ cos x = -1 :=
by rw [← mul_self_eq_one_iff (cos x), ← sin_sq_add_cos_sq x,
    pow_two, pow_two, ← sub_eq_iff_eq_add, sub_self];
  exact ⟨λ h, by rw [h, mul_zero], eq_zero_of_mul_self_eq_zero ∘ eq.symm⟩

theorem sin_sub_sin (θ ψ : ℝ) : sin θ - sin ψ = 2 * sin((θ - ψ)/2) * cos((θ + ψ)/2) :=
begin
  have s1 := sin_add ((θ + ψ) / 2) ((θ - ψ) / 2),
  have s2 := sin_sub ((θ + ψ) / 2) ((θ - ψ) / 2),
  rw [div_add_div_same, add_sub, add_right_comm, add_sub_cancel, add_self_div_two] at s1,
  rw [div_sub_div_same, ←sub_add, add_sub_cancel', add_self_div_two] at s2,
  rw [s1, s2, ←sub_add, add_sub_cancel', ← two_mul, ← mul_assoc, mul_right_comm]
end

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

theorem cos_eq_zero_iff {θ : ℝ} : cos θ = 0 ↔ ∃ k : ℤ, θ = (2 * k + 1) * pi / 2 :=
begin
  rw [←real.sin_pi_div_two_sub, sin_eq_zero_iff],
  split,
  { rintro ⟨n, hn⟩, existsi -n,
    rw [int.cast_neg, add_mul, add_div, mul_assoc, mul_div_cancel_left _ (@two_ne_zero ℝ _),
        one_mul, ←neg_mul_eq_neg_mul, hn, neg_sub, sub_add_cancel] },
  { rintro ⟨n, hn⟩, existsi -n,
    rw [hn, add_mul, one_mul, add_div, mul_assoc, mul_div_cancel_left _ (@two_ne_zero ℝ _),
        sub_add_eq_sub_sub_swap, sub_self, zero_sub, neg_mul_eq_neg_mul, int.cast_neg] }
end

lemma cos_eq_one_iff_of_lt_of_lt {x : ℝ} (hx₁ : -(2 * π) < x) (hx₂ : x < 2 * π) : cos x = 1 ↔ x = 0 :=
⟨λ h, let ⟨n, hn⟩ := (cos_eq_one_iff x).1 h in
    begin
      clear _let_match,
      subst hn,
      rw [mul_lt_iff_lt_one_left two_pi_pos, ← int.cast_one, int.cast_lt, ← int.le_sub_one_iff, sub_self] at hx₂,
      rw [neg_lt, neg_mul_eq_neg_mul, mul_lt_iff_lt_one_left two_pi_pos, neg_lt,
        ← int.cast_one, ← int.cast_neg, int.cast_lt, ← int.add_one_le_iff, neg_add_self] at hx₁,
      exact mul_eq_zero.2 (or.inl (int.cast_eq_zero.2 (le_antisymm hx₂ hx₁))),
    end,
  λ h, by simp [h]⟩

theorem cos_sub_cos (θ ψ : ℝ) : cos θ - cos ψ = -2 * sin((θ + ψ)/2) * sin((θ - ψ)/2) :=
by rw [← sin_pi_div_two_sub, ← sin_pi_div_two_sub, sin_sub_sin, sub_sub_sub_cancel_left,
    add_sub, sub_add_eq_add_sub, add_halves, sub_sub, sub_div π, cos_pi_div_two_sub,
    ← neg_sub, neg_div, sin_neg, ← neg_mul_eq_mul_neg, neg_mul_eq_neg_mul, mul_right_comm]

lemma cos_lt_cos_of_nonneg_of_le_pi_div_two {x y : ℝ} (hx₁ : 0 ≤ x) (hx₂ : x ≤ π / 2)
  (hy₁ : 0 ≤ y) (hy₂ : y ≤ π / 2) (hxy : x < y) : cos y < cos x :=
calc cos y = cos x * cos (y - x) - sin x * sin (y - x) :
  by rw [← cos_add, add_sub_cancel'_right]
... < (cos x * 1) - sin x * sin (y - x) :
  sub_lt_sub_right ((mul_lt_mul_left
    (cos_pos_of_neg_pi_div_two_lt_of_lt_pi_div_two (lt_of_lt_of_le (neg_neg_of_pos pi_div_two_pos) hx₁)
      (lt_of_lt_of_le hxy hy₂))).2
        (lt_of_le_of_ne (cos_le_one _) (mt (cos_eq_one_iff_of_lt_of_lt
          (show -(2 * π) < y - x, by linarith) (show y - x < 2 * π, by linarith)).1
            (sub_ne_zero.2 (ne_of_lt hxy).symm)))) _
... ≤ _ : by rw mul_one;
  exact sub_le_self _ (mul_nonneg (sin_nonneg_of_nonneg_of_le_pi hx₁ (by linarith))
    (sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)))

lemma cos_lt_cos_of_nonneg_of_le_pi {x y : ℝ} (hx₁ : 0 ≤ x) (hx₂ : x ≤ π)
  (hy₁ : 0 ≤ y) (hy₂ : y ≤ π) (hxy : x < y) : cos y < cos x :=
match (le_total x (π / 2) : x ≤ π / 2 ∨ π / 2 ≤ x), le_total y (π / 2) with
| or.inl hx, or.inl hy := cos_lt_cos_of_nonneg_of_le_pi_div_two hx₁ hx hy₁ hy hxy
| or.inl hx, or.inr hy := (lt_or_eq_of_le hx).elim
  (λ hx, calc cos y ≤ 0 : cos_nonpos_of_pi_div_two_le_of_le hy (by linarith [pi_pos])
    ... < cos x : cos_pos_of_neg_pi_div_two_lt_of_lt_pi_div_two (by linarith) hx)
  (λ hx, calc cos y < 0 : cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith [pi_pos])
    ... = cos x : by rw [hx, cos_pi_div_two])
| or.inr hx, or.inl hy := by linarith
| or.inr hx, or.inr hy := neg_lt_neg_iff.1 (by rw [← cos_pi_sub, ← cos_pi_sub];
  apply cos_lt_cos_of_nonneg_of_le_pi_div_two; linarith)
end

lemma cos_le_cos_of_nonneg_of_le_pi {x y : ℝ} (hx₁ : 0 ≤ x) (hx₂ : x ≤ π)
  (hy₁ : 0 ≤ y) (hy₂ : y ≤ π) (hxy : x ≤ y) : cos y ≤ cos x :=
(lt_or_eq_of_le hxy).elim
  (le_of_lt ∘ cos_lt_cos_of_nonneg_of_le_pi hx₁ hx₂ hy₁ hy₂)
  (λ h, h ▸ le_refl _)

lemma sin_lt_sin_of_le_of_le_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) ≤ x) (hx₂ : x ≤ π / 2) (hy₁ : -(π / 2) ≤ y)
  (hy₂ : y ≤ π / 2) (hxy : x < y) : sin x < sin y :=
by rw [← cos_sub_pi_div_two, ← cos_sub_pi_div_two, ← cos_neg (x - _), ← cos_neg (y - _)];
  apply cos_lt_cos_of_nonneg_of_le_pi; linarith

lemma sin_le_sin_of_le_of_le_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) ≤ x) (hx₂ : x ≤ π / 2) (hy₁ : -(π / 2) ≤ y)
  (hy₂ : y ≤ π / 2) (hxy : x ≤ y) : sin x ≤ sin y :=
(lt_or_eq_of_le hxy).elim
  (le_of_lt ∘ sin_lt_sin_of_le_of_le_pi_div_two hx₁ hx₂ hy₁ hy₂)
  (λ h, h ▸ le_refl _)

lemma sin_inj_of_le_of_le_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) ≤ x) (hx₂ : x ≤ π / 2) (hy₁ : -(π / 2) ≤ y)
  (hy₂ : y ≤ π / 2) (hxy : sin x = sin y) : x = y :=
match lt_trichotomy x y with
| or.inl h          := absurd (sin_lt_sin_of_le_of_le_pi_div_two hx₁ hx₂ hy₁ hy₂ h) (by rw hxy; exact lt_irrefl _)
| or.inr (or.inl h) := h
| or.inr (or.inr h) := absurd (sin_lt_sin_of_le_of_le_pi_div_two hy₁ hy₂ hx₁ hx₂ h) (by rw hxy; exact lt_irrefl _)
end

lemma cos_inj_of_nonneg_of_le_pi {x y : ℝ} (hx₁ : 0 ≤ x) (hx₂ : x ≤ π) (hy₁ : 0 ≤ y) (hy₂ : y ≤ π)
  (hxy : cos x = cos y) : x = y :=
begin
  rw [← sin_pi_div_two_sub, ← sin_pi_div_two_sub] at hxy,
  refine (sub_left_inj).1 (sin_inj_of_le_of_le_pi_div_two _ _ _ _ hxy);
  linarith
end

lemma exists_sin_eq : set.Icc (-1:ℝ) 1 ⊆  sin '' set.Icc (-(π / 2)) (π / 2) :=
by convert intermediate_value_Icc
  (le_trans (neg_nonpos.2 (le_of_lt pi_div_two_pos)) (le_of_lt pi_div_two_pos))
  continuous_sin.continuous_on; simp only [sin_neg, sin_pi_div_two]

lemma sin_lt {x : ℝ} (h : 0 < x) : sin x < x :=
begin
  cases le_or_gt x 1 with h' h',
  { have hx : abs x = x := abs_of_nonneg (le_of_lt h),
    have : abs x ≤ 1, rwa [hx],
    have := sin_bound this, rw [abs_le] at this,
    have := this.2, rw [sub_le_iff_le_add', hx] at this,
    apply lt_of_le_of_lt this, rw [sub_add], apply lt_of_lt_of_le _ (le_of_eq (sub_zero x)),
    apply sub_lt_sub_left, rw sub_pos, apply mul_lt_mul',
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
  rw (show x ^ 3 / 4 - x ^ 3 / 6 = x ^ 3 / 12,
    by simp [div_eq_mul_inv, (mul_sub _ _ _).symm, -sub_eq_add_neg]; congr; norm_num),
  apply mul_lt_mul',
  { rw [pow_succ x 3], refine le_trans _ (le_of_eq (one_mul _)),
    rw mul_le_mul_right, exact h', apply pow_pos h },
  norm_num, norm_num, apply pow_pos h
end

/-- The type of angles -/
def angle : Type :=
quotient_add_group.quotient (gmultiples (2 * π))

namespace angle

instance angle.add_comm_group : add_comm_group angle :=
quotient_add_group.add_comm_group _

instance : inhabited angle := ⟨0⟩

instance angle.has_coe : has_coe ℝ angle :=
⟨quotient.mk'⟩

instance angle.is_add_group_hom : @is_add_group_hom ℝ angle _ _ (coe : ℝ → angle) :=
@quotient_add_group.is_add_group_hom _ _ _ (normal_add_subgroup_of_add_comm_group _)

@[simp] lemma coe_zero : ↑(0 : ℝ) = (0 : angle) := rfl
@[simp] lemma coe_add (x y : ℝ) : ↑(x + y : ℝ) = (↑x + ↑y : angle) := rfl
@[simp] lemma coe_neg (x : ℝ) : ↑(-x : ℝ) = -(↑x : angle) := rfl
@[simp] lemma coe_sub (x y : ℝ) : ↑(x - y : ℝ) = (↑x - ↑y : angle) := rfl
@[simp] lemma coe_smul (x : ℝ) (n : ℕ) :
  ↑(add_monoid.smul n x : ℝ) = add_monoid.smul n (↑x : angle) :=
add_monoid_hom.map_smul ⟨coe, coe_zero, coe_add⟩ _ _
@[simp] lemma coe_gsmul (x : ℝ) (n : ℤ) : ↑(gsmul n x : ℝ) = gsmul n (↑x : angle) :=
add_monoid_hom.map_gsmul ⟨coe, coe_zero, coe_add⟩ _ _

@[simp] lemma coe_two_pi : ↑(2 * π : ℝ) = (0 : angle) :=
quotient.sound' ⟨-1, by dsimp only; rw [neg_one_gsmul, add_zero]⟩

lemma angle_eq_iff_two_pi_dvd_sub {ψ θ : ℝ} : (θ : angle) = ψ ↔ ∃ k : ℤ, θ - ψ = 2 * π * k :=
by simp only [quotient_add_group.eq, gmultiples, set.mem_range, gsmul_eq_mul', (sub_eq_neg_add _ _).symm, eq_comm]

theorem cos_eq_iff_eq_or_eq_neg {θ ψ : ℝ} : cos θ = cos ψ ↔ (θ : angle) = ψ ∨ (θ : angle) = -ψ :=
begin
  split,
  { intro Hcos,
    rw [←sub_eq_zero, cos_sub_cos, mul_eq_zero, mul_eq_zero, neg_eq_zero, eq_false_intro two_ne_zero,
        false_or, sin_eq_zero_iff, sin_eq_zero_iff] at Hcos,
    rcases Hcos with ⟨n, hn⟩ | ⟨n, hn⟩,
    { right,
      rw [eq_div_iff_mul_eq _ _ (@two_ne_zero ℝ _), ← sub_eq_iff_eq_add] at hn,
      rw [← hn, coe_sub, eq_neg_iff_add_eq_zero, sub_add_cancel, mul_assoc,
          ← gsmul_eq_mul, coe_gsmul, mul_comm, coe_two_pi, gsmul_zero] },
    { left,
      rw [eq_div_iff_mul_eq _ _ (@two_ne_zero ℝ _), eq_sub_iff_add_eq] at hn,
      rw [← hn, coe_add, mul_assoc,
          ← gsmul_eq_mul, coe_gsmul, mul_comm, coe_two_pi, gsmul_zero, zero_add] } },
  { rw [angle_eq_iff_two_pi_dvd_sub, ← coe_neg, angle_eq_iff_two_pi_dvd_sub],
    rintro (⟨k, H⟩ | ⟨k, H⟩),
    rw [← sub_eq_zero_iff_eq, cos_sub_cos, H, mul_assoc 2 π k, mul_div_cancel_left _ (@two_ne_zero ℝ _),
      mul_comm π _, sin_int_mul_pi, mul_zero],
    rw [←sub_eq_zero_iff_eq, cos_sub_cos, ← sub_neg_eq_add, H, mul_assoc 2 π k,
      mul_div_cancel_left _ (@two_ne_zero ℝ _), mul_comm π _, sin_int_mul_pi, mul_zero, zero_mul] }
end

theorem sin_eq_iff_eq_or_add_eq_pi {θ ψ : ℝ} : sin θ = sin ψ ↔ (θ : angle) = ψ ∨ (θ : angle) + ψ = π :=
begin
  split,
  { intro Hsin, rw [← cos_pi_div_two_sub, ← cos_pi_div_two_sub] at Hsin,
    cases cos_eq_iff_eq_or_eq_neg.mp Hsin with h h,
    { left, rw coe_sub at h, exact sub_left_inj.1 h },
      right, rw [coe_sub, coe_sub, eq_neg_iff_add_eq_zero, add_sub,
      sub_add_eq_add_sub, ← coe_add, add_halves, sub_sub, sub_eq_zero] at h,
    exact h.symm },
  { rw [angle_eq_iff_two_pi_dvd_sub, ←eq_sub_iff_add_eq, ←coe_sub, angle_eq_iff_two_pi_dvd_sub],
    rintro (⟨k, H⟩ | ⟨k, H⟩),
    rw [← sub_eq_zero_iff_eq, sin_sub_sin, H, mul_assoc 2 π k, mul_div_cancel_left _ (@two_ne_zero ℝ _),
      mul_comm π _, sin_int_mul_pi, mul_zero, zero_mul],
    have H' : θ + ψ = (2 * k) * π + π := by rwa [←sub_add, sub_add_eq_add_sub, sub_eq_iff_eq_add,
      mul_assoc, mul_comm π _, ←mul_assoc] at H,
    rw [← sub_eq_zero_iff_eq, sin_sub_sin, H', add_div, mul_assoc 2 _ π, mul_div_cancel_left _ (@two_ne_zero ℝ _),
      cos_add_pi_div_two, sin_int_mul_pi, neg_zero, mul_zero] }
end

theorem cos_sin_inj {θ ψ : ℝ} (Hcos : cos θ = cos ψ) (Hsin : sin θ = sin ψ) : (θ : angle) = ψ :=
begin
  cases cos_eq_iff_eq_or_eq_neg.mp Hcos with hc hc, { exact hc },
  cases sin_eq_iff_eq_or_add_eq_pi.mp Hsin with hs hs, { exact hs },
  rw [eq_neg_iff_add_eq_zero, hs] at hc,
  cases quotient.exact' hc with n hn, dsimp only at hn,
  rw [← neg_one_mul, add_zero, ← sub_eq_zero_iff_eq, gsmul_eq_mul, ← mul_assoc, ← sub_mul,
      mul_eq_zero, eq_false_intro (ne_of_gt pi_pos), or_false, sub_neg_eq_add,
      ← int.cast_zero, ← int.cast_one, ← int.cast_bit0, ← int.cast_mul, ← int.cast_add, int.cast_inj] at hn,
  have : (n * 2 + 1) % (2:ℤ) = 0 % (2:ℤ) := congr_arg (%(2:ℤ)) hn,
  rw [add_comm, int.add_mul_mod_self] at this,
  exact absurd this one_ne_zero
end

end angle

/-- Inverse of the `sin` function, returns values in the range `-π / 2 ≤ arcsin x` and `arcsin x ≤ π / 2`.
  If the argument is not between `-1` and `1` it defaults to `0` -/
noncomputable def arcsin (x : ℝ) : ℝ :=
if hx : -1 ≤ x ∧ x ≤ 1 then classical.some (exists_sin_eq hx) else 0

lemma arcsin_le_pi_div_two (x : ℝ) : arcsin x ≤ π / 2 :=
if hx : -1 ≤ x ∧ x ≤ 1
then by rw [arcsin, dif_pos hx]; exact (classical.some_spec (exists_sin_eq hx)).1.2
else by rw [arcsin, dif_neg hx]; exact le_of_lt pi_div_two_pos

lemma neg_pi_div_two_le_arcsin (x : ℝ) : -(π / 2) ≤ arcsin x :=
if hx : -1 ≤ x ∧ x ≤ 1
then by rw [arcsin, dif_pos hx]; exact (classical.some_spec (exists_sin_eq hx)).1.1
else by rw [arcsin, dif_neg hx]; exact neg_nonpos.2 (le_of_lt pi_div_two_pos)

lemma sin_arcsin {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) : sin (arcsin x) = x :=
by rw [arcsin, dif_pos (and.intro hx₁ hx₂)];
  exact (classical.some_spec (exists_sin_eq ⟨hx₁, hx₂⟩)).2

lemma arcsin_sin {x : ℝ} (hx₁ : -(π / 2) ≤ x) (hx₂ : x ≤ π / 2) : arcsin (sin x) = x :=
sin_inj_of_le_of_le_pi_div_two (neg_pi_div_two_le_arcsin _) (arcsin_le_pi_div_two _) hx₁ hx₂
  (by rw sin_arcsin (neg_one_le_sin _) (sin_le_one _))

lemma arcsin_inj {x y : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) (hy₁ : -1 ≤ y) (hy₂ : y ≤ 1)
  (hxy : arcsin x = arcsin y) : x = y :=
by rw [← sin_arcsin hx₁ hx₂, ← sin_arcsin hy₁ hy₂, hxy]

@[simp] lemma arcsin_zero : arcsin 0 = 0 :=
sin_inj_of_le_of_le_pi_div_two
  (neg_pi_div_two_le_arcsin _)
  (arcsin_le_pi_div_two _)
  (neg_nonpos.2 (le_of_lt pi_div_two_pos))
  (le_of_lt pi_div_two_pos)
  (by rw [sin_arcsin, sin_zero]; norm_num)

@[simp] lemma arcsin_one : arcsin 1 = π / 2 :=
sin_inj_of_le_of_le_pi_div_two
  (neg_pi_div_two_le_arcsin _)
  (arcsin_le_pi_div_two _)
  (by linarith [pi_pos])
  (le_refl _)
  (by rw [sin_arcsin, sin_pi_div_two]; norm_num)

@[simp] lemma arcsin_neg (x : ℝ) : arcsin (-x) = -arcsin x :=
if h : -1 ≤ x ∧ x ≤ 1 then
  have -1 ≤ -x ∧ -x ≤ 1, by rwa [neg_le_neg_iff, neg_le, and.comm],
  sin_inj_of_le_of_le_pi_div_two
    (neg_pi_div_two_le_arcsin _)
    (arcsin_le_pi_div_two _)
    (neg_le_neg (arcsin_le_pi_div_two _))
    (neg_le.1 (neg_pi_div_two_le_arcsin _))
    (by rw [sin_arcsin this.1 this.2, sin_neg, sin_arcsin h.1 h.2])
else
  have ¬(-1 ≤ -x ∧ -x ≤ 1) := by rwa [neg_le_neg_iff, neg_le, and.comm],
  by rw [arcsin, arcsin, dif_neg h, dif_neg this, neg_zero]

@[simp] lemma arcsin_neg_one : arcsin (-1) = -(π / 2) := by simp

lemma arcsin_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ arcsin x :=
if hx₁ : x ≤ 1 then
not_lt.1 (λ h, not_lt.2 hx begin
  have := sin_lt_sin_of_le_of_le_pi_div_two
    (neg_pi_div_two_le_arcsin _) (arcsin_le_pi_div_two _)
    (neg_nonpos.2 (le_of_lt pi_div_two_pos)) (le_of_lt pi_div_two_pos) h,
  rw [real.sin_arcsin, sin_zero] at this; linarith
end)
else by rw [arcsin, dif_neg]; simp [hx₁]

lemma arcsin_eq_zero_iff {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) : arcsin x = 0 ↔ x = 0 :=
⟨λ h, have sin (arcsin x) = 0, by simp [h],
  by rwa [sin_arcsin hx₁ hx₂] at this,
λ h, by simp [h]⟩

lemma arcsin_pos {x : ℝ} (hx₁ : 0 < x) (hx₂ : x ≤ 1) : 0 < arcsin x :=
lt_of_le_of_ne (arcsin_nonneg (le_of_lt hx₁))
  (ne.symm (mt (arcsin_eq_zero_iff (by linarith) hx₂).1 (ne_of_lt hx₁).symm))

lemma arcsin_nonpos {x : ℝ} (hx : x ≤ 0) : arcsin x ≤ 0 :=
neg_nonneg.1 (arcsin_neg x ▸ arcsin_nonneg (neg_nonneg.2 hx))

/-- Inverse of the `cos` function, returns values in the range `0 ≤ arccos x` and `arccos x ≤ π`.
  If the argument is not between `-1` and `1` it defaults to `π / 2` -/
noncomputable def arccos (x : ℝ) : ℝ :=
π / 2 - arcsin x

lemma arccos_eq_pi_div_two_sub_arcsin (x : ℝ) : arccos x = π / 2 - arcsin x := rfl

lemma arcsin_eq_pi_div_two_sub_arccos (x : ℝ) : arcsin x = π / 2 - arccos x :=
by simp [sub_eq_add_neg, arccos]

lemma arccos_le_pi (x : ℝ) : arccos x ≤ π :=
by unfold arccos; linarith [neg_pi_div_two_le_arcsin x]

lemma arccos_nonneg (x : ℝ) : 0 ≤ arccos x :=
by unfold arccos; linarith [arcsin_le_pi_div_two x]

lemma cos_arccos {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) : cos (arccos x) = x :=
by rw [arccos, cos_pi_div_two_sub, sin_arcsin hx₁ hx₂]

lemma arccos_cos {x : ℝ} (hx₁ : 0 ≤ x) (hx₂ : x ≤ π) : arccos (cos x) = x :=
by rw [arccos, ← sin_pi_div_two_sub, arcsin_sin]; simp [sub_eq_add_neg]; linarith

lemma arccos_inj {x y : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) (hy₁ : -1 ≤ y) (hy₂ : y ≤ 1)
  (hxy : arccos x = arccos y) : x = y :=
arcsin_inj hx₁ hx₂ hy₁ hy₂ $ by simp [arccos, *] at *

@[simp] lemma arccos_zero : arccos 0 = π / 2 := by simp [arccos]

@[simp] lemma arccos_one : arccos 1 = 0 := by simp [arccos]

@[simp] lemma arccos_neg_one : arccos (-1) = π := by simp [arccos, add_halves]

lemma arccos_neg (x : ℝ) : arccos (-x) = π - arccos x :=
by rw [← add_halves π, arccos, arcsin_neg, arccos, add_sub_assoc, sub_sub_self]; simp

lemma cos_arcsin_nonneg (x : ℝ) : 0 ≤ cos (arcsin x) :=
cos_nonneg_of_neg_pi_div_two_le_of_le_pi_div_two
    (neg_pi_div_two_le_arcsin _) (arcsin_le_pi_div_two _)

lemma cos_arcsin {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) : cos (arcsin x) = sqrt (1 - x ^ 2) :=
have sin (arcsin x) ^ 2 + cos (arcsin x) ^ 2 = 1 := sin_sq_add_cos_sq (arcsin x),
begin
  rw [← eq_sub_iff_add_eq', ← sqrt_inj (pow_two_nonneg _) (sub_nonneg.2 (sin_sq_le_one (arcsin x))),
    pow_two, sqrt_mul_self (cos_arcsin_nonneg _)] at this,
  rw [this, sin_arcsin hx₁ hx₂],
end

lemma sin_arccos {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) : sin (arccos x) = sqrt (1 - x ^ 2) :=
by rw [arccos_eq_pi_div_two_sub_arcsin, sin_pi_div_two_sub, cos_arcsin hx₁ hx₂]

lemma abs_div_sqrt_one_add_lt (x : ℝ) : abs (x / sqrt (1 + x ^ 2)) < 1 :=
have h₁ : 0 < 1 + x ^ 2, from add_pos_of_pos_of_nonneg zero_lt_one (pow_two_nonneg _),
have h₂ : 0 < sqrt (1 + x ^ 2), from sqrt_pos.2 h₁,
by rw [abs_div, div_lt_iff (abs_pos_of_pos h₂), one_mul,
    mul_self_lt_mul_self_iff (abs_nonneg x) (abs_nonneg _),
    ← abs_mul, ← abs_mul, mul_self_sqrt (add_nonneg zero_le_one (pow_two_nonneg _)),
    abs_of_nonneg (mul_self_nonneg x), abs_of_nonneg (le_of_lt h₁), pow_two, add_comm];
  exact lt_add_one _

lemma div_sqrt_one_add_lt_one (x : ℝ) : x / sqrt (1 + x ^ 2) < 1 :=
(abs_lt.1 (abs_div_sqrt_one_add_lt _)).2

lemma neg_one_lt_div_sqrt_one_add (x : ℝ) : -1 < x / sqrt (1 + x ^ 2) :=
(abs_lt.1 (abs_div_sqrt_one_add_lt _)).1

lemma tan_pos_of_pos_of_lt_pi_div_two {x : ℝ} (h0x : 0 < x) (hxp : x < π / 2) : 0 < tan x :=
by rw tan_eq_sin_div_cos; exact div_pos (sin_pos_of_pos_of_lt_pi h0x (by linarith))
  (cos_pos_of_neg_pi_div_two_lt_of_lt_pi_div_two (by linarith) hxp)

lemma tan_nonneg_of_nonneg_of_le_pi_div_two {x : ℝ} (h0x : 0 ≤ x) (hxp : x ≤ π / 2) : 0 ≤ tan x :=
match lt_or_eq_of_le h0x, lt_or_eq_of_le hxp with
| or.inl hx0, or.inl hxp := le_of_lt (tan_pos_of_pos_of_lt_pi_div_two hx0 hxp)
| or.inl hx0, or.inr hxp := by simp [hxp, tan_eq_sin_div_cos]
| or.inr hx0, _          := by simp [hx0.symm]
end

lemma tan_neg_of_neg_of_pi_div_two_lt {x : ℝ} (hx0 : x < 0) (hpx : -(π / 2) < x) : tan x < 0 :=
neg_pos.1 (tan_neg x ▸ tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith [pi_pos]))

lemma tan_nonpos_of_nonpos_of_neg_pi_div_two_le {x : ℝ} (hx0 : x ≤ 0) (hpx : -(π / 2) ≤ x) : tan x ≤ 0 :=
neg_nonneg.1 (tan_neg x ▸ tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith [pi_pos]))

lemma tan_lt_tan_of_nonneg_of_lt_pi_div_two {x y : ℝ} (hx₁ : 0 ≤ x) (hx₂ : x < π / 2) (hy₁ : 0 ≤ y)
  (hy₂ : y < π / 2) (hxy : x < y) : tan x < tan y :=
begin
  rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos],
  exact div_lt_div
    (sin_lt_sin_of_le_of_le_pi_div_two (by linarith) (le_of_lt hx₂)
      (by linarith) (le_of_lt hy₂) hxy)
    (cos_le_cos_of_nonneg_of_le_pi hx₁ (by linarith) hy₁ (by linarith) (le_of_lt hxy))
    (sin_nonneg_of_nonneg_of_le_pi hy₁ (by linarith))
    (cos_pos_of_neg_pi_div_two_lt_of_lt_pi_div_two (by linarith) hy₂)
end

lemma tan_lt_tan_of_lt_of_lt_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) < x) (hx₂ : x < π / 2)
  (hy₁ : -(π / 2) < y) (hy₂ : y < π / 2) (hxy : x < y) : tan x < tan y :=
match le_total x 0, le_total y 0 with
| or.inl hx0, or.inl hy0 := neg_lt_neg_iff.1 $ by rw [← tan_neg, ← tan_neg]; exact
  tan_lt_tan_of_nonneg_of_lt_pi_div_two (neg_nonneg.2 hy0) (neg_lt.2 hy₁)
    (neg_nonneg.2 hx0) (neg_lt.2 hx₁) (neg_lt_neg hxy)
| or.inl hx0, or.inr hy0 := (lt_or_eq_of_le hy0).elim
  (λ hy0, calc tan x ≤ 0 : tan_nonpos_of_nonpos_of_neg_pi_div_two_le hx0 (le_of_lt hx₁)
    ... < tan y : tan_pos_of_pos_of_lt_pi_div_two hy0 hy₂)
  (λ hy0, by rw [← hy0, tan_zero]; exact
    tan_neg_of_neg_of_pi_div_two_lt (hy0.symm ▸ hxy) hx₁)
| or.inr hx0, or.inl hy0 := by linarith
| or.inr hx0, or.inr hy0 := tan_lt_tan_of_nonneg_of_lt_pi_div_two hx0 hx₂ hy0 hy₂ hxy
end

lemma tan_inj_of_lt_of_lt_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) < x) (hx₂ : x < π / 2)
  (hy₁ : -(π / 2) < y) (hy₂ : y < π / 2) (hxy : tan x = tan y) : x = y :=
match lt_trichotomy x y with
| or.inl h          := absurd (tan_lt_tan_of_lt_of_lt_pi_div_two hx₁ hx₂ hy₁ hy₂ h) (by rw hxy; exact lt_irrefl _)
| or.inr (or.inl h) := h
| or.inr (or.inr h) := absurd (tan_lt_tan_of_lt_of_lt_pi_div_two hy₁ hy₂ hx₁ hx₂ h) (by rw hxy; exact lt_irrefl _)
end

/-- Inverse of the `tan` function, returns values in the range `-π / 2 < arctan x` and `arctan x < π / 2` -/
noncomputable def arctan (x : ℝ) : ℝ :=
arcsin (x / sqrt (1 + x ^ 2))

lemma sin_arctan (x : ℝ) : sin (arctan x) = x / sqrt (1 + x ^ 2) :=
sin_arcsin (le_of_lt (neg_one_lt_div_sqrt_one_add _)) (le_of_lt (div_sqrt_one_add_lt_one _))

lemma cos_arctan (x : ℝ) : cos (arctan x) = 1 / sqrt (1 + x ^ 2) :=
have h₁ : (0 : ℝ) < 1 + x ^ 2,
  from add_pos_of_pos_of_nonneg zero_lt_one (pow_two_nonneg _),
have h₂ : (x / sqrt (1 + x ^ 2)) ^ 2 < 1,
  by rw [pow_two, ← abs_mul_self, _root_.abs_mul];
    exact mul_lt_one_of_nonneg_of_lt_one_left (abs_nonneg _)
      (abs_div_sqrt_one_add_lt _) (le_of_lt (abs_div_sqrt_one_add_lt _)),
by rw [arctan, cos_arcsin (le_of_lt (neg_one_lt_div_sqrt_one_add _)) (le_of_lt (div_sqrt_one_add_lt_one _)),
    one_div_eq_inv, ← sqrt_inv, sqrt_inj (sub_nonneg.2 (le_of_lt h₂)) (inv_nonneg.2 (le_of_lt h₁)),
    div_pow, pow_two (sqrt _), mul_self_sqrt (le_of_lt h₁),
    ← domain.mul_left_inj (ne.symm (ne_of_lt h₁)), mul_sub,
    mul_div_cancel' _ (ne.symm (ne_of_lt h₁)), mul_inv_cancel (ne.symm (ne_of_lt h₁))];
  simp

lemma tan_arctan (x : ℝ) : tan (arctan x) = x :=
by rw [tan_eq_sin_div_cos, sin_arctan, cos_arctan, div_div_div_div_eq, mul_one,
    mul_div_assoc,
    div_self (mt sqrt_eq_zero'.1 (not_le_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (pow_two_nonneg x)))),
    mul_one]

lemma arctan_lt_pi_div_two (x : ℝ) : arctan x < π / 2 :=
lt_of_le_of_ne (arcsin_le_pi_div_two _)
  (λ h, ne_of_lt (div_sqrt_one_add_lt_one x) $
    by rw [← sin_arcsin (le_of_lt (neg_one_lt_div_sqrt_one_add _))
        (le_of_lt (div_sqrt_one_add_lt_one _)), ← arctan, h, sin_pi_div_two])

lemma neg_pi_div_two_lt_arctan (x : ℝ) : -(π / 2) < arctan x :=
lt_of_le_of_ne (neg_pi_div_two_le_arcsin _)
  (λ h, ne_of_lt (neg_one_lt_div_sqrt_one_add x) $
    by rw [← sin_arcsin (le_of_lt (neg_one_lt_div_sqrt_one_add _))
        (le_of_lt (div_sqrt_one_add_lt_one _)), ← arctan, ← h, sin_neg, sin_pi_div_two])

lemma tan_surjective : function.surjective tan :=
function.surjective_of_has_right_inverse ⟨_, tan_arctan⟩

lemma arctan_tan {x : ℝ} (hx₁ : -(π / 2) < x) (hx₂ : x < π / 2) : arctan (tan x) = x :=
tan_inj_of_lt_of_lt_pi_div_two (neg_pi_div_two_lt_arctan _)
  (arctan_lt_pi_div_two _) hx₁ hx₂ (by rw tan_arctan)

@[simp] lemma arctan_zero : arctan 0 = 0 :=
by simp [arctan]

@[simp] lemma arctan_neg (x : ℝ) : arctan (-x) = - arctan x :=
by simp [arctan, neg_div]

end real

namespace complex

open_locale real

/-- `arg` returns values in the range (-π, π], such that for `x ≠ 0`,
  `sin (arg x) = x.im / x.abs` and `cos (arg x) = x.re / x.abs`,
  `arg 0` defaults to `0` -/
noncomputable def arg (x : ℂ) : ℝ :=
if 0 ≤ x.re
then real.arcsin (x.im / x.abs)
else if 0 ≤ x.im
then real.arcsin ((-x).im / x.abs) + π
else real.arcsin ((-x).im / x.abs) - π

lemma arg_le_pi (x : ℂ) : arg x ≤ π :=
if hx₁ : 0 ≤ x.re
then by rw [arg, if_pos hx₁];
  exact le_trans (real.arcsin_le_pi_div_two _) (le_of_lt (half_lt_self real.pi_pos))
else
  have hx : x ≠ 0, from λ h, by simpa [h, lt_irrefl] using hx₁,
  if hx₂ : 0 ≤ x.im
  then by rw [arg, if_neg hx₁, if_pos hx₂];
    exact le_sub_iff_add_le.1 (by rw sub_self;
      exact real.arcsin_nonpos (by rw [neg_im, neg_div, neg_nonpos]; exact div_nonneg hx₂ (abs_pos.2 hx)))
  else by rw [arg, if_neg hx₁, if_neg hx₂];
      exact sub_le_iff_le_add.2 (le_trans (real.arcsin_le_pi_div_two _)
        (by linarith [real.pi_pos]))

lemma neg_pi_lt_arg (x : ℂ) : -π < arg x :=
if hx₁ : 0 ≤ x.re
then by rw [arg, if_pos hx₁];
  exact lt_of_lt_of_le (neg_lt_neg (half_lt_self real.pi_pos)) (real.neg_pi_div_two_le_arcsin _)
else
  have hx : x ≠ 0, from λ h, by simpa [h, lt_irrefl] using hx₁,
  if hx₂ : 0 ≤ x.im
  then by rw [arg, if_neg hx₁, if_pos hx₂];
    exact sub_lt_iff_lt_add.1
      (lt_of_lt_of_le (by linarith [real.pi_pos]) (real.neg_pi_div_two_le_arcsin _))
  else by rw [arg, if_neg hx₁, if_neg hx₂];
    exact lt_sub_iff_add_lt.2 (by rw neg_add_self;
      exact real.arcsin_pos (by rw [neg_im]; exact div_pos (neg_pos.2 (lt_of_not_ge hx₂))
        (abs_pos.2 hx)) (by rw [← abs_neg x]; exact (abs_le.1 (abs_im_div_abs_le_one _)).2))

lemma arg_eq_arg_neg_add_pi_of_im_nonneg_of_re_neg {x : ℂ} (hxr : x.re < 0) (hxi : 0 ≤ x.im) :
  arg x = arg (-x) + π :=
have 0 ≤ (-x).re, from le_of_lt $ by simpa [neg_pos],
by rw [arg, arg, if_neg (not_le.2 hxr), if_pos this, if_pos hxi, abs_neg]

lemma arg_eq_arg_neg_sub_pi_of_im_neg_of_re_neg {x : ℂ} (hxr : x.re < 0) (hxi : x.im < 0) :
  arg x = arg (-x) - π :=
have 0 ≤ (-x).re, from le_of_lt $ by simpa [neg_pos],
by rw [arg, arg, if_neg (not_le.2 hxr), if_neg (not_le.2 hxi), if_pos this, abs_neg]

@[simp] lemma arg_zero : arg 0 = 0 :=
by simp [arg, le_refl]

@[simp] lemma arg_one : arg 1 = 0 :=
by simp [arg, zero_le_one]

@[simp] lemma arg_neg_one : arg (-1) = π :=
by simp [arg, le_refl, not_le.2 (@zero_lt_one ℝ _)]

@[simp] lemma arg_I : arg I = π / 2 :=
by simp [arg, le_refl]

@[simp] lemma arg_neg_I : arg (-I) = -(π / 2) :=
by simp [arg, le_refl]

lemma sin_arg (x : ℂ) : real.sin (arg x) = x.im / x.abs :=
by unfold arg; split_ifs;
  simp [sub_eq_add_neg, arg, real.sin_arcsin (abs_le.1 (abs_im_div_abs_le_one x)).1
    (abs_le.1 (abs_im_div_abs_le_one x)).2, real.sin_add, neg_div, real.arcsin_neg,
    real.sin_neg]

private lemma cos_arg_of_re_nonneg {x : ℂ} (hx : x ≠ 0) (hxr : 0 ≤ x.re) : real.cos (arg x) = x.re / x.abs :=
have 0 ≤ 1 - (x.im / abs x) ^ 2,
  from sub_nonneg.2 $ by rw [pow_two, ← _root_.abs_mul_self, _root_.abs_mul, ← pow_two];
  exact pow_le_one _ (_root_.abs_nonneg _) (abs_im_div_abs_le_one _),
by rw [eq_div_iff_mul_eq _ _ (mt abs_eq_zero.1 hx), ← real.mul_self_sqrt (abs_nonneg x),
    arg, if_pos hxr, real.cos_arcsin (abs_le.1 (abs_im_div_abs_le_one x)).1
    (abs_le.1 (abs_im_div_abs_le_one x)).2, ← real.sqrt_mul (abs_nonneg _), ← real.sqrt_mul this,
    sub_mul, div_pow, ← pow_two, div_mul_cancel _ (pow_ne_zero 2 (mt abs_eq_zero.1 hx)),
    one_mul, pow_two, mul_self_abs, norm_sq, pow_two, add_sub_cancel, real.sqrt_mul_self hxr]

lemma cos_arg {x : ℂ} (hx : x ≠ 0) : real.cos (arg x) = x.re / x.abs :=
if hxr : 0 ≤ x.re then cos_arg_of_re_nonneg hx hxr
else
  have 0 ≤ (-x).re, from le_of_lt $ by simpa [neg_pos] using hxr,
  if hxi : 0 ≤ x.im
  then have 0 ≤ (-x).re, from le_of_lt $ by simpa [neg_pos] using hxr,
    by rw [arg_eq_arg_neg_add_pi_of_im_nonneg_of_re_neg (not_le.1 hxr) hxi, real.cos_add_pi,
        cos_arg_of_re_nonneg (neg_ne_zero.2 hx) this];
      simp [neg_div]
  else by rw [arg_eq_arg_neg_sub_pi_of_im_neg_of_re_neg (not_le.1 hxr) (not_le.1 hxi)];
    simp [sub_eq_add_neg, real.cos_add, neg_div, cos_arg_of_re_nonneg (neg_ne_zero.2 hx) this]

lemma tan_arg {x : ℂ} : real.tan (arg x) = x.im / x.re :=
begin
  by_cases h : x = 0,
  { simp only [h, euclidean_domain.zero_div,
    complex.zero_im, complex.arg_zero, real.tan_zero, complex.zero_re]},
  rw [real.tan_eq_sin_div_cos, sin_arg, cos_arg h,
      div_div_div_cancel_right' _ (mt abs_eq_zero.1 h)]
end

lemma arg_cos_add_sin_mul_I {x : ℝ} (hx₁ : -π < x) (hx₂ : x ≤ π) :
  arg (cos x + sin x * I) = x :=
if hx₃ : -(π / 2) ≤ x ∧ x ≤ π / 2
then
  have hx₄ : 0 ≤ (cos x + sin x * I).re,
    by simp; exact real.cos_nonneg_of_neg_pi_div_two_le_of_le_pi_div_two hx₃.1 hx₃.2,
  by rw [arg, if_pos hx₄];
    simp [abs_cos_add_sin_mul_I, sin_of_real_re, real.arcsin_sin hx₃.1 hx₃.2]
else if hx₄ : x < -(π / 2)
then
  have hx₅ : ¬0 ≤ (cos x + sin x * I).re :=
    suffices ¬ 0 ≤ real.cos x, by simpa,
    not_le.2 $ by rw ← real.cos_neg;
      apply real.cos_neg_of_pi_div_two_lt_of_lt; linarith,
  have hx₆ : ¬0 ≤ (cos ↑x + sin ↑x * I).im :=
    suffices real.sin x < 0, by simpa,
    by apply real.sin_neg_of_neg_of_neg_pi_lt; linarith,
  suffices -π + -real.arcsin (real.sin x) = x,
    by rw [arg, if_neg hx₅, if_neg hx₆];
    simpa [sub_eq_add_neg, add_comm, abs_cos_add_sin_mul_I, sin_of_real_re],
  by rw [← real.arcsin_neg, ← real.sin_add_pi, real.arcsin_sin]; try {simp [add_left_comm]}; linarith
else
  have hx₅ : π / 2 < x, by cases not_and_distrib.1 hx₃; linarith,
  have hx₆ : ¬0 ≤ (cos x + sin x * I).re :=
    suffices ¬0 ≤ real.cos x, by simpa,
    not_le.2 $ by apply real.cos_neg_of_pi_div_two_lt_of_lt; linarith,
  have hx₇ : 0 ≤ (cos x + sin x * I).im :=
    suffices 0 ≤ real.sin x, by simpa,
    by apply real.sin_nonneg_of_nonneg_of_le_pi; linarith,
  suffices π - real.arcsin (real.sin x) = x,
    by rw [arg, if_neg hx₆, if_pos hx₇];
      simpa [sub_eq_add_neg, add_comm, abs_cos_add_sin_mul_I, sin_of_real_re],
  by rw [← real.sin_pi_sub, real.arcsin_sin]; simp [sub_eq_add_neg]; linarith

lemma arg_eq_arg_iff {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
  arg x = arg y ↔ (abs y / abs x : ℂ) * x = y :=
have hax : abs x ≠ 0, from (mt abs_eq_zero.1 hx),
have hay : abs y ≠ 0, from (mt abs_eq_zero.1 hy),
⟨λ h,
  begin
    have hcos := congr_arg real.cos h,
    rw [cos_arg hx, cos_arg hy, div_eq_div_iff hax hay] at hcos,
    have hsin := congr_arg real.sin h,
    rw [sin_arg, sin_arg, div_eq_div_iff hax hay] at hsin,
    apply complex.ext,
    { rw [mul_re, ← of_real_div, of_real_re, of_real_im, zero_mul, sub_zero, mul_comm,
        ← mul_div_assoc, hcos, mul_div_cancel _ hax] },
    { rw [mul_im, ← of_real_div, of_real_re, of_real_im, zero_mul, add_zero,
        mul_comm, ← mul_div_assoc, hsin, mul_div_cancel _ hax] }
  end,
λ h,
  have hre : abs (y / x) * x.re = y.re,
    by rw ← of_real_div at h;
      simpa [-of_real_div] using congr_arg re h,
  have hre' : abs (x / y) * y.re = x.re,
    by rw [← hre, abs_div, abs_div, ← mul_assoc, div_mul_div,
      mul_comm (abs _), div_self (mul_ne_zero hay hax), one_mul],
  have him : abs (y / x) * x.im = y.im,
    by rw ← of_real_div at h;
      simpa [-of_real_div] using congr_arg im h,
  have him' : abs (x / y) * y.im = x.im,
    by rw [← him, abs_div, abs_div, ← mul_assoc, div_mul_div,
      mul_comm (abs _), div_self (mul_ne_zero hay hax), one_mul],
  have hxya : x.im / abs x = y.im / abs y,
    by rw [← him, abs_div, mul_comm, ← mul_div_comm, mul_div_cancel_left _ hay],
  have hnxya : (-x).im / abs x = (-y).im / abs y,
    by rw [neg_im, neg_im, neg_div, neg_div, hxya],
  if hxr : 0 ≤ x.re
  then
    have hyr : 0 ≤ y.re, from hre ▸ mul_nonneg (abs_nonneg _) hxr,
    by simp [arg, *] at *
  else
    have hyr : ¬ 0 ≤ y.re, from λ hyr, hxr $ hre' ▸ mul_nonneg (abs_nonneg _) hyr,
    if hxi : 0 ≤ x.im
    then
      have hyi : 0 ≤ y.im, from him ▸ mul_nonneg (abs_nonneg _) hxi,
      by simp [arg, *] at *
    else
      have hyi : ¬ 0 ≤ y.im, from λ hyi, hxi $ him' ▸ mul_nonneg (abs_nonneg _) hyi,
      by simp [arg, *] at *⟩

lemma arg_real_mul (x : ℂ) {r : ℝ} (hr : 0 < r) : arg (r * x) = arg x :=
if hx : x = 0 then by simp [hx]
else (arg_eq_arg_iff (mul_ne_zero (of_real_ne_zero.2 (ne_of_lt hr).symm) hx) hx).2 $
  by rw [abs_mul, abs_of_nonneg (le_of_lt hr), ← mul_assoc,
    of_real_mul, mul_comm (r : ℂ), ← div_div_eq_div_mul,
    div_mul_cancel _ (of_real_ne_zero.2 (ne_of_lt hr).symm),
    div_self (of_real_ne_zero.2 (mt abs_eq_zero.1 hx)), one_mul]

lemma ext_abs_arg {x y : ℂ} (h₁ : x.abs = y.abs) (h₂ : x.arg = y.arg) : x = y :=
if hy : y = 0 then by simp * at *
else have hx : x ≠ 0, from λ hx, by simp [*, eq_comm] at *,
  by rwa [arg_eq_arg_iff hx hy, h₁, div_self (of_real_ne_zero.2 (mt abs_eq_zero.1 hy)), one_mul] at h₂

lemma arg_of_real_of_nonneg {x : ℝ} (hx : 0 ≤ x) : arg x = 0 :=
by simp [arg, hx]

lemma arg_of_real_of_neg {x : ℝ} (hx : x < 0) : arg x = π :=
by rw [arg_eq_arg_neg_add_pi_of_im_nonneg_of_re_neg, ← of_real_neg, arg_of_real_of_nonneg];
  simp [*, le_iff_eq_or_lt, lt_neg]

/-- Inverse of the `exp` function. Returns values such that `(log x).im > - π` and `(log x).im ≤ π`.
  `log 0 = 0`-/
noncomputable def log (x : ℂ) : ℂ := x.abs.log + arg x * I

lemma log_re (x : ℂ) : x.log.re = x.abs.log := by simp [log]

lemma log_im (x : ℂ) : x.log.im = x.arg := by simp [log]

lemma exp_log {x : ℂ} (hx : x ≠ 0) : exp (log x) = x :=
by rw [log, exp_add_mul_I, ← of_real_sin, sin_arg, ← of_real_cos, cos_arg hx,
  ← of_real_exp, real.exp_log (abs_pos.2 hx), mul_add, of_real_div, of_real_div,
  mul_div_cancel' _ (of_real_ne_zero.2 (mt abs_eq_zero.1 hx)), ← mul_assoc,
  mul_div_cancel' _ (of_real_ne_zero.2 (mt abs_eq_zero.1 hx)), re_add_im]

lemma exp_inj_of_neg_pi_lt_of_le_pi {x y : ℂ} (hx₁ : -π < x.im) (hx₂ : x.im ≤ π)
  (hy₁ : - π < y.im) (hy₂ : y.im ≤ π) (hxy : exp x = exp y) : x = y :=
by rw [exp_eq_exp_re_mul_sin_add_cos, exp_eq_exp_re_mul_sin_add_cos y] at hxy;
  exact complex.ext
    (real.exp_injective $
      by simpa [abs_mul, abs_cos_add_sin_mul_I] using congr_arg complex.abs hxy)
    (by simpa [(of_real_exp _).symm, - of_real_exp, arg_real_mul _ (real.exp_pos _),
      arg_cos_add_sin_mul_I hx₁ hx₂, arg_cos_add_sin_mul_I hy₁ hy₂] using congr_arg arg hxy)

lemma log_exp {x : ℂ} (hx₁ : -π < x.im) (hx₂: x.im ≤ π) : log (exp x) = x :=
exp_inj_of_neg_pi_lt_of_le_pi
  (by rw log_im; exact neg_pi_lt_arg _)
  (by rw log_im; exact arg_le_pi _)
  hx₁ hx₂ (by rw [exp_log (exp_ne_zero _)])

lemma of_real_log {x : ℝ} (hx : 0 ≤ x) : (x.log : ℂ) = log x :=
complex.ext
  (by rw [log_re, of_real_re, abs_of_nonneg hx])
  (by rw [of_real_im, log_im, arg_of_real_of_nonneg hx])

@[simp] lemma log_zero : log 0 = 0 := by simp [log]

@[simp] lemma log_one : log 1 = 0 := by simp [log]

lemma log_neg_one : log (-1) = π * I := by simp [log]

lemma log_I : log I = π / 2 * I := by simp [log]

lemma log_neg_I : log (-I) = -(π / 2) * I := by simp [log]

lemma exp_eq_one_iff {x : ℂ} : exp x = 1 ↔ ∃ n : ℤ, x = n * ((2 * π) * I) :=
have real.exp (x.re) * real.cos (x.im) = 1 → real.cos x.im ≠ -1,
  from λ h₁ h₂, begin
    rw [h₂, mul_neg_eq_neg_mul_symm, mul_one, neg_eq_iff_neg_eq] at h₁,
    have := real.exp_pos x.re,
    rw ← h₁ at this,
    exact absurd this (by norm_num)
  end,
calc exp x = 1 ↔ (exp x).re = 1 ∧ (exp x).im = 0 : by simp [complex.ext_iff]
  ... ↔ real.cos x.im = 1 ∧ real.sin x.im = 0 ∧ x.re = 0 :
    begin
      rw exp_eq_exp_re_mul_sin_add_cos,
      simp [complex.ext_iff, cos_of_real_re, sin_of_real_re, exp_of_real_re,
        real.exp_ne_zero],
      split; finish [real.sin_eq_zero_iff_cos_eq]
    end
  ... ↔ (∃ n : ℤ, ↑n * (2 * π) = x.im) ∧ (∃ n : ℤ, ↑n * π = x.im) ∧ x.re = 0 :
    by rw [real.sin_eq_zero_iff, real.cos_eq_one_iff]
  ... ↔ ∃ n : ℤ, x = n * ((2 * π) * I) :
    ⟨λ ⟨⟨n, hn⟩, ⟨m, hm⟩, h⟩, ⟨n, by simp [complex.ext_iff, hn.symm, h]⟩,
      λ ⟨n, hn⟩, ⟨⟨n, by simp [hn]⟩, ⟨2 * n, by simp [hn, mul_comm, mul_assoc, mul_left_comm]⟩,
        by simp [hn]⟩⟩

lemma exp_eq_exp_iff_exp_sub_eq_one {x y : ℂ} : exp x = exp y ↔ exp (x - y) = 1 :=
by rw [exp_sub, div_eq_one_iff_eq _ (exp_ne_zero _)]

lemma exp_eq_exp_iff_exists_int {x y : ℂ} : exp x = exp y ↔ ∃ n : ℤ, x = y + n * ((2 * π) * I) :=
by simp only [exp_eq_exp_iff_exp_sub_eq_one, exp_eq_one_iff, sub_eq_iff_eq_add']

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

lemma sin_add_pi (x : ℝ) : sin (x + π) = -sin x :=
by simp [sin_add]

lemma sin_add_two_pi (x : ℝ) : sin (x + 2 * π) = sin x :=
by simp [sin_add_pi, sin_add, sin_two_pi, cos_two_pi]

lemma cos_add_two_pi (x : ℝ) : cos (x + 2 * π) = cos x :=
by simp [cos_add, cos_two_pi, sin_two_pi]

lemma sin_pi_sub (x : ℝ) : sin (π - x) = sin x :=
by simp [sub_eq_add_neg, sin_add]

lemma cos_add_pi (x : ℝ) : cos (x + π) = -cos x :=
by simp [cos_add]

lemma cos_pi_sub (x : ℝ) : cos (π - x) = -cos x :=
by simp [sub_eq_add_neg, cos_add]

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

lemma sin_nat_mul_pi (n : ℕ) : sin (n * π) = 0 :=
by induction n; simp [add_mul, sin_add, *]

lemma sin_int_mul_pi (n : ℤ) : sin (n * π) = 0 :=
by cases n; simp [add_mul, sin_add, *, sin_nat_mul_pi]

lemma cos_nat_mul_two_pi (n : ℕ) : cos (n * (2 * π)) = 1 :=
by induction n; simp [*, mul_add, cos_add, add_mul, cos_two_pi, sin_two_pi]

lemma cos_int_mul_two_pi (n : ℤ) : cos (n * (2 * π)) = 1 :=
by cases n; simp only [cos_nat_mul_two_pi, int.of_nat_eq_coe,
  int.neg_succ_of_nat_coe, int.cast_coe_nat, int.cast_neg,
  (neg_mul_eq_neg_mul _ _).symm, cos_neg]

lemma cos_int_mul_two_pi_add_pi (n : ℤ) : cos (n * (2 * π) + π) = -1 :=
by simp [cos_add, sin_add, cos_int_mul_two_pi]

section pow

/-- The complex power function `x^y`, given by `x^y = exp(y log x)` (where `log` is the principal
determination of the logarithm), unless `x = 0` where one sets `0^0 = 1` and `0^y = 0` for
`y ≠ 0`. -/
noncomputable def cpow (x y : ℂ) : ℂ :=
if x = 0
  then if y = 0
    then 1
    else 0
  else exp (log x * y)

noncomputable instance : has_pow ℂ ℂ := ⟨cpow⟩

@[simp] lemma cpow_eq_pow (x y : ℂ) : cpow x y = x ^ y := rfl

lemma cpow_def (x y : ℂ) : x ^ y =
  if x = 0
    then if y = 0
      then 1
      else 0
    else exp (log x * y) := rfl

@[simp] lemma cpow_zero (x : ℂ) : x ^ (0 : ℂ) = 1 := by simp [cpow_def]

@[simp] lemma cpow_eq_zero_iff (x y : ℂ) : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 :=
by { simp only [cpow_def], split_ifs; simp [*, exp_ne_zero] }

@[simp] lemma zero_cpow {x : ℂ} (h : x ≠ 0) : (0 : ℂ) ^ x = 0 :=
by simp [cpow_def, *]

@[simp] lemma cpow_one (x : ℂ) : x ^ (1 : ℂ) = x :=
if hx : x = 0 then by simp [hx, cpow_def]
else by rw [cpow_def, if_neg (@one_ne_zero ℂ _), if_neg hx, mul_one, exp_log hx]

@[simp] lemma one_cpow (x : ℂ) : (1 : ℂ) ^ x = 1 :=
by rw cpow_def; split_ifs; simp [one_ne_zero, *] at *

lemma cpow_add {x : ℂ} (y z : ℂ) (hx : x ≠ 0) : x ^ (y + z) = x ^ y * x ^ z :=
by simp [cpow_def]; split_ifs; simp [*, exp_add, mul_add] at *

lemma cpow_mul {x y : ℂ} (z : ℂ) (h₁ : -π < (log x * y).im) (h₂ : (log x * y).im ≤ π) :
  x ^ (y * z) = (x ^ y) ^ z :=
begin
  simp [cpow_def],
  split_ifs;
  simp [*, exp_ne_zero, log_exp h₁ h₂, mul_assoc] at *
end

lemma cpow_neg (x y : ℂ) : x ^ -y = (x ^ y)⁻¹ :=
by simp [cpow_def]; split_ifs; simp [exp_neg]

@[simp] lemma cpow_nat_cast (x : ℂ) : ∀ (n : ℕ), x ^ (n : ℂ) = x ^ n
| 0       := by simp
| (n + 1) := if hx : x = 0 then by simp only [hx, pow_succ,
    complex.zero_cpow (nat.cast_ne_zero.2 (nat.succ_ne_zero _)), zero_mul]
  else by simp [cpow_def, hx, mul_comm, mul_add, exp_add, pow_succ, (cpow_nat_cast n).symm,
    exp_log hx]

@[simp] lemma cpow_int_cast (x : ℂ) : ∀ (n : ℤ), x ^ (n : ℂ) = x ^ n
| (n : ℕ) := by simp; refl
| -[1+ n] := by rw fpow_neg_succ_of_nat;
  simp only [int.neg_succ_of_nat_coe, int.cast_neg, complex.cpow_neg, inv_eq_one_div,
    int.cast_coe_nat, cpow_nat_cast]

lemma cpow_nat_inv_pow (x : ℂ) {n : ℕ} (hn : 0 < n) : (x ^ (n⁻¹ : ℂ)) ^ n = x :=
have (log x * (↑n)⁻¹).im = (log x).im / n,
  by rw [div_eq_mul_inv, ← of_real_nat_cast, ← of_real_inv, mul_im,
                of_real_re, of_real_im]; simp,
have h : -π < (log x * (↑n)⁻¹).im ∧ (log x * (↑n)⁻¹).im ≤ π,
  from (le_total (log x).im 0).elim
    (λ h, ⟨calc -π < (log x).im : by simp [log, neg_pi_lt_arg]
            ... ≤ ((log x).im * 1) / n : le_div_of_mul_le (nat.cast_pos.2 hn)
              (mul_le_mul_of_nonpos_left (by rw ← nat.cast_one; exact nat.cast_le.2 hn) h)
            ... = (log x * (↑n)⁻¹).im : by simp [this],
          this.symm ▸ le_trans (div_nonpos_of_nonpos_of_pos h (nat.cast_pos.2 hn))
            (le_of_lt real.pi_pos)⟩)
    (λ h, ⟨this.symm ▸ lt_of_lt_of_le (neg_neg_of_pos real.pi_pos)
            (div_nonneg h (nat.cast_pos.2 hn)),
          calc (log x * (↑n)⁻¹).im = (1 * (log x).im) / n : by simp [this]
            ... ≤ (log x).im : (div_le_of_le_mul (nat.cast_pos.2 hn)
              (mul_le_mul_of_nonneg_right (by rw ← nat.cast_one; exact nat.cast_le.2 hn) h))
            ... ≤ _ : by simp [log, arg_le_pi]⟩),
by rw [← cpow_nat_cast, ← cpow_mul _ h.1 h.2,
    inv_mul_cancel (show (n : ℂ) ≠ 0, from nat.cast_ne_zero.2 (nat.pos_iff_ne_zero.1 hn)),
    cpow_one]

end pow

end complex

namespace real

/-- The real power function `x^y`, defined as the real part of the complex power function.
For `x > 0`, it is equal to `exp(y log x)`. For `x = 0`, one sets `0^0=1` and `0^y=0` for `y ≠ 0`.
For `x < 0`, the definition is somewhat arbitary as it depends on the choice of a complex
determination of the logarithm. With our conventions, it is equal to `exp (y log (-x)) cos (πy)`. -/
noncomputable def rpow (x y : ℝ) := ((x : ℂ) ^ (y : ℂ)).re

noncomputable instance : has_pow ℝ ℝ := ⟨rpow⟩

@[simp] lemma rpow_eq_pow (x y : ℝ) : rpow x y = x ^ y := rfl

lemma rpow_def (x y : ℝ) : x ^ y = ((x : ℂ) ^ (y : ℂ)).re := rfl

lemma rpow_def_of_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : x ^ y =
  if x = 0
    then if y = 0
      then 1
      else 0
    else exp (log x * y) :=
by simp only [rpow_def, complex.cpow_def];
  split_ifs;
  simp [*, (complex.of_real_log hx).symm, -complex.of_real_mul,
    (complex.of_real_mul _ _).symm, complex.exp_of_real_re] at *

lemma rpow_def_of_pos {x : ℝ} (hx : 0 < x) (y : ℝ) : x ^ y = exp (log x * y) :=
by rw [rpow_def_of_nonneg (le_of_lt hx), if_neg (ne_of_gt hx)]

lemma rpow_eq_zero_iff_of_nonneg {x y : ℝ} (hx : 0 ≤ x) : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 :=
by { simp only [rpow_def_of_nonneg hx], split_ifs; simp [*, exp_ne_zero] }

open_locale real

lemma rpow_def_of_neg {x : ℝ} (hx : x < 0) (y : ℝ) : x ^ y = exp (log (-x) * y) * cos (y * π) :=
begin
  rw [rpow_def, complex.cpow_def, if_neg],
  have : complex.log x * y = ↑(log(-x) * y) + ↑(y * π) * complex.I,
    simp only [complex.log, abs_of_neg hx, complex.arg_of_real_of_neg hx,
      complex.abs_of_real, complex.of_real_mul], ring,
  { rw [this, complex.exp_add_mul_I, ← complex.of_real_exp, ← complex.of_real_cos,
      ← complex.of_real_sin, mul_add, ← complex.of_real_mul, ← mul_assoc, ← complex.of_real_mul,
      complex.add_re, complex.of_real_re, complex.mul_re, complex.I_re, complex.of_real_im], ring },
  { rw complex.of_real_eq_zero, exact ne_of_lt hx }
end

lemma rpow_def_of_nonpos {x : ℝ} (hx : x ≤ 0) (y : ℝ) : x ^ y =
  if x = 0
    then if y = 0
      then 1
      else 0
    else exp (log (-x) * y) * cos (y * π) :=
by split_ifs; simp [rpow_def, *]; exact rpow_def_of_neg (lt_of_le_of_ne hx h) _

lemma rpow_pos_of_pos {x : ℝ} (hx : 0 < x) (y : ℝ) : 0 < x ^ y :=
by rw rpow_def_of_pos hx; apply exp_pos

lemma abs_rpow_le_abs_rpow (x y : ℝ) : abs (x ^ y) ≤ abs (x) ^ y :=
abs_le_of_le_of_neg_le
begin
  cases lt_trichotomy 0 x, { rw abs_of_pos h },
  cases h, { simp [h.symm] },
  rw [rpow_def_of_neg h, rpow_def_of_pos (abs_pos_of_neg h), abs_of_neg h],
  calc exp (log (-x) * y) * cos (y * π) ≤ exp (log (-x) * y) * 1 :
    mul_le_mul_of_nonneg_left (cos_le_one _) (le_of_lt $ exp_pos _)
  ... = _ : mul_one _
end
begin
  cases lt_trichotomy 0 x, { rw abs_of_pos h, have : 0 < x^y := rpow_pos_of_pos h _, linarith },
  cases h, { simp only [h.symm, abs_zero, rpow_def_of_nonneg], split_ifs, repeat {norm_num}},
  rw [rpow_def_of_neg h, rpow_def_of_pos (abs_pos_of_neg h), abs_of_neg h],
  calc -(exp (log (-x) * y) * cos (y * π)) = exp (log (-x) * y) * (-cos (y * π)) : by ring
    ... ≤ exp (log (-x) * y) * 1 :
      mul_le_mul_of_nonneg_left (neg_le.2 $ neg_one_le_cos _) (le_of_lt $ exp_pos _)
    ... = exp (log (-x) * y) : mul_one _
end

end real

namespace complex

lemma of_real_cpow {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : ((x ^ y : ℝ) : ℂ) = (x : ℂ) ^ (y : ℂ) :=
by simp [real.rpow_def_of_nonneg hx, complex.cpow_def]; split_ifs; simp [complex.of_real_log hx]

@[simp] lemma abs_cpow_real (x : ℂ) (y : ℝ) : abs (x ^ (y : ℂ)) = x.abs ^ y :=
begin
  rw [real.rpow_def_of_nonneg (abs_nonneg _), complex.cpow_def],
  split_ifs;
  simp [*, abs_of_nonneg (le_of_lt (real.exp_pos _)), complex.log, complex.exp_add,
    add_mul, mul_right_comm _ I, exp_mul_I, abs_cos_add_sin_mul_I,
    (complex.of_real_mul _ _).symm, -complex.of_real_mul] at *
end

@[simp] lemma abs_cpow_inv_nat (x : ℂ) (n : ℕ) : abs (x ^ (n⁻¹ : ℂ)) = x.abs ^ (n⁻¹ : ℝ) :=
by rw ← abs_cpow_real; simp [-abs_cpow_real]

end complex

namespace real

open_locale real

variables {x y z : ℝ}

@[simp] lemma rpow_zero (x : ℝ) : x ^ (0 : ℝ) = 1 := by simp [rpow_def]

@[simp] lemma zero_rpow {x : ℝ} (h : x ≠ 0) : (0 : ℝ) ^ x = 0 :=
by simp [rpow_def, *]

@[simp] lemma rpow_one (x : ℝ) : x ^ (1 : ℝ) = x := by simp [rpow_def]

@[simp] lemma one_rpow (x : ℝ) : (1 : ℝ) ^ x = 1 := by simp [rpow_def]

lemma rpow_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : 0 ≤ x ^ y :=
by rw [rpow_def_of_nonneg hx];
  split_ifs; simp only [zero_le_one, le_refl, le_of_lt (exp_pos _)]

lemma rpow_add {x : ℝ} (y z : ℝ) (hx : 0 < x) : x ^ (y + z) = x ^ y * x ^ z :=
by simp only [rpow_def_of_pos hx, mul_add, exp_add]

lemma rpow_mul {x : ℝ} (hx : 0 ≤ x) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z :=
by rw [← complex.of_real_inj, complex.of_real_cpow (rpow_nonneg_of_nonneg hx _),
    complex.of_real_cpow hx, complex.of_real_mul, complex.cpow_mul, complex.of_real_cpow hx];
  simp only [(complex.of_real_mul _ _).symm, (complex.of_real_log hx).symm,
    complex.of_real_im, neg_lt_zero, pi_pos, le_of_lt pi_pos]

lemma rpow_neg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : x ^ -y = (x ^ y)⁻¹ :=
by simp only [rpow_def_of_nonneg hx]; split_ifs; simp [*, exp_neg] at *

@[simp] lemma rpow_nat_cast (x : ℝ) (n : ℕ) : x ^ (n : ℝ) = x ^ n :=
by simp only [rpow_def, (complex.of_real_pow _ _).symm, complex.cpow_nat_cast,
  complex.of_real_nat_cast, complex.of_real_re]

@[simp] lemma rpow_int_cast (x : ℝ) (n : ℤ) : x ^ (n : ℝ) = x ^ n :=
by simp only [rpow_def, (complex.of_real_fpow _ _).symm, complex.cpow_int_cast,
  complex.of_real_int_cast, complex.of_real_re]

lemma mul_rpow {x y z : ℝ} (h : 0 ≤ x) (h₁ : 0 ≤ y) : (x*y)^z = x^z * y^z :=
begin
  iterate 3 { rw real.rpow_def_of_nonneg }, split_ifs; simp * at *,
  { have hx : 0 < x, cases lt_or_eq_of_le h with h₂ h₂, exact h₂, exfalso, apply h_2, exact eq.symm h₂,
    have hy : 0 < y, cases lt_or_eq_of_le h₁ with h₂ h₂, exact h₂, exfalso, apply h_3, exact eq.symm h₂,
    rw [log_mul hx hy, add_mul, exp_add]},
  { exact h₁},
  { exact h},
  { exact mul_nonneg h h₁},
end

lemma one_le_rpow {x z : ℝ} (h : 1 ≤ x) (h₁ : 0 ≤ z) : 1 ≤ x^z :=
begin
  rw real.rpow_def_of_nonneg, split_ifs with h₂ h₃,
  { refl},
  { simp [*, not_le_of_gt zero_lt_one] at *},
  { have hx : 0 < x, exact lt_of_lt_of_le zero_lt_one h,
    rw [←log_le_log zero_lt_one hx, log_one] at h,
    have pos : 0 ≤ log x * z, exact mul_nonneg h h₁,
      rwa [←exp_le_exp, exp_zero] at pos},
  { exact le_trans zero_le_one h},
end

lemma rpow_le_rpow {x y z: ℝ} (h : 0 ≤ x) (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x^z ≤ y^z :=
begin
  rw le_iff_eq_or_lt at h h₂, cases h₂,
  { rw [←h₂, rpow_zero, rpow_zero]},
  { cases h,
    { rw [←h, zero_rpow], rw real.rpow_def_of_nonneg, split_ifs,
      { exact zero_le_one},
      { refl},
      { exact le_of_lt (exp_pos (log y * z))},
      { rwa ←h at h₁},
      { exact ne.symm (ne_of_lt h₂)}},
    { have one_le : 1 ≤ y / x, rw one_le_div_iff_le h, exact h₁,
      have one_le_pow : 1 ≤ (y / x)^z, exact one_le_rpow one_le (le_of_lt h₂),
      rw [←mul_div_cancel y (ne.symm (ne_of_lt h)), mul_comm, mul_div_assoc],
      rw [mul_rpow (le_of_lt h) (le_trans zero_le_one one_le), mul_comm],
      exact (le_mul_of_ge_one_left (rpow_nonneg_of_nonneg (le_of_lt h) z) one_le_pow) } }
end

lemma rpow_lt_rpow (hx : 0 ≤ x) (hxy : x < y) (hz : 0 < z) : x^z < y^z :=
begin
  rw le_iff_eq_or_lt at hx, cases hx,
  { rw [← hx, zero_rpow (ne_of_gt hz)], exact rpow_pos_of_pos (by rwa ← hx at hxy) _ },
  rw [rpow_def_of_pos hx, rpow_def_of_pos (lt_trans hx hxy), exp_lt_exp],
  exact mul_lt_mul_of_pos_right (log_lt_log hx hxy) hz
end

lemma rpow_lt_rpow_of_exponent_lt (hx : 1 < x) (hyz : y < z) : x^y < x^z :=
begin
  repeat {rw [rpow_def_of_pos (lt_trans zero_lt_one hx)]},
  rw exp_lt_exp, exact mul_lt_mul_of_pos_left hyz (log_pos hx),
end

lemma rpow_le_rpow_of_exponent_le (hx : 1 ≤ x) (hyz : y ≤ z) : x^y ≤ x^z :=
begin
  repeat {rw [rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hx)]},
  rw exp_le_exp, exact mul_le_mul_of_nonneg_left hyz (log_nonneg hx),
end

lemma rpow_lt_rpow_of_exponent_gt (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) :
  x^y < x^z :=
begin
  repeat {rw [rpow_def_of_pos hx0]},
  rw exp_lt_exp, exact mul_lt_mul_of_neg_left hyz (log_neg hx0 hx1),
end

lemma rpow_le_rpow_of_exponent_ge (hx0 : 0 < x) (hx1 : x ≤ 1) (hyz : z ≤ y) :
  x^y ≤ x^z :=
begin
  repeat {rw [rpow_def_of_pos hx0]},
  rw exp_le_exp, exact mul_le_mul_of_nonpos_left hyz (log_nonpos hx1),
end

lemma rpow_le_one {x e : ℝ} (he : 0 ≤ e) (hx : 0 ≤ x) (hx2 : x ≤ 1) : x^e ≤ 1 :=
by rw ←one_rpow e; apply rpow_le_rpow; assumption

lemma one_lt_rpow (hx : 1 < x) (hz : 0 < z) : 1 < x^z :=
by { rw ← one_rpow z, exact rpow_lt_rpow zero_le_one hx hz }

lemma rpow_lt_one (hx : 0 < x) (hx1 : x < 1) (hz : 0 < z) : x^z < 1 :=
by { rw ← one_rpow z, exact rpow_lt_rpow (le_of_lt hx) hx1 hz }

lemma pow_nat_rpow_nat_inv {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : 0 < n) :
  (x ^ n) ^ (n⁻¹ : ℝ) = x :=
have hn0 : (n : ℝ) ≠ 0, by simpa [nat.pos_iff_ne_zero] using hn,
by rw [← rpow_nat_cast, ← rpow_mul hx, mul_inv_cancel hn0, rpow_one]

lemma rpow_nat_inv_pow_nat {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : 0 < n) :
  (x ^ (n⁻¹ : ℝ)) ^ n = x :=
have hn0 : (n : ℝ) ≠ 0, by simpa [nat.pos_iff_ne_zero] using hn,
by rw [← rpow_nat_cast, ← rpow_mul hx, inv_mul_cancel hn0, rpow_one]

section prove_rpow_is_continuous

lemma continuous_rpow_aux1 : continuous (λp : {p:ℝ×ℝ // 0 < p.1}, p.val.1 ^ p.val.2) :=
suffices h : continuous (λ p : {p:ℝ×ℝ // 0 < p.1 }, exp (log p.val.1 * p.val.2)),
  by { convert h, ext p, rw rpow_def_of_pos p.2 },
continuous_exp.comp $
  (show continuous ((λp:{p:ℝ//0 < p}, log (p.val)) ∘ (λp:{p:ℝ×ℝ//0<p.fst}, ⟨p.val.1, p.2⟩)), from
    continuous_log'.comp $ continuous_subtype_mk _ $ continuous_fst.comp continuous_subtype_val).mul
  (continuous_snd.comp $ continuous_subtype_val.comp continuous_id)

lemma continuous_rpow_aux2 : continuous (λ p : {p:ℝ×ℝ // p.1 < 0}, p.val.1 ^ p.val.2) :=
suffices h : continuous (λp:{p:ℝ×ℝ // p.1 < 0}, exp (log (-p.val.1) * p.val.2) * cos (p.val.2 * π)),
  by { convert h, ext p, rw [rpow_def_of_neg p.2] },
  (continuous_exp.comp $
    (show continuous $ (λp:{p:ℝ//0<p},
            log (p.val))∘(λp:{p:ℝ×ℝ//p.1<0}, ⟨-p.val.1, neg_pos_of_neg p.2⟩),
     from continuous_log'.comp $ continuous_subtype_mk _ $ continuous_neg.comp $
            continuous_fst.comp continuous_subtype_val).mul
    (continuous_snd.comp $ continuous_subtype_val.comp continuous_id)).mul
  (continuous_cos.comp $
    (continuous_snd.comp $ continuous_subtype_val.comp continuous_id).mul continuous_const)

lemma continuous_at_rpow_of_ne_zero (hx : x ≠ 0) (y : ℝ) :
  continuous_at (λp:ℝ×ℝ, p.1^p.2) (x, y) :=
begin
  cases lt_trichotomy 0 x,
  exact continuous_within_at.continuous_at
    (continuous_on_iff_continuous_restrict.2 continuous_rpow_aux1 _ h)
    (mem_nhds_sets (by { convert is_open_prod (is_open_lt' (0:ℝ)) is_open_univ, ext, finish }) h),
  cases h,
  { exact absurd h.symm hx },
  exact continuous_within_at.continuous_at
    (continuous_on_iff_continuous_restrict.2 continuous_rpow_aux2 _ h)
    (mem_nhds_sets (by { convert is_open_prod (is_open_gt' (0:ℝ)) is_open_univ, ext, finish }) h)
end

lemma continuous_rpow_aux3 : continuous (λ p : {p:ℝ×ℝ // 0 < p.2}, p.val.1 ^ p.val.2) :=
continuous_iff_continuous_at.2 $ λ ⟨(x₀, y₀), hy₀⟩,
begin
  by_cases hx₀ : x₀ = 0,
  { simp only [continuous_at, hx₀, zero_rpow (ne_of_gt hy₀), tendsto_nhds_nhds], assume ε ε0,
    rcases exists_pos_rat_lt (half_pos hy₀) with ⟨q, q_pos, q_lt⟩,
    let q := (q:ℝ), replace q_pos : 0 < q := rat.cast_pos.2 q_pos,
    let δ := min (min q (ε ^ (1 / q))) (1/2),
    have δ0 : 0 < δ := lt_min (lt_min q_pos (rpow_pos_of_pos ε0 _)) (by norm_num),
    have : δ ≤ q := le_trans (min_le_left _ _) (min_le_left _ _),
    have : δ ≤ ε ^ (1 / q) := le_trans (min_le_left _ _) (min_le_right _ _),
    have : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num),
    use δ, use δ0, rintros ⟨⟨x, y⟩, hy⟩,
    simp only [subtype.dist_eq, real.dist_eq, prod.dist_eq, sub_zero, subtype.coe_mk],
    assume h, rw max_lt_iff at h, cases h with xδ yy₀,
    have qy : q < y, calc q < y₀ / 2 : q_lt
      ... = y₀ - y₀ / 2 : (sub_half _).symm
      ... ≤ y₀ - δ : by linarith
      ... < y : sub_lt_of_abs_sub_lt_left yy₀,
    calc abs(x^y) ≤ abs(x)^y : abs_rpow_le_abs_rpow _ _
      ... < δ ^ y : rpow_lt_rpow (abs_nonneg _) xδ hy
      ... < δ ^ q : by { refine rpow_lt_rpow_of_exponent_gt _ _ _, repeat {linarith} }
      ... ≤ (ε ^ (1 / q)) ^ q : by { refine rpow_le_rpow _ _ _, repeat {linarith} }
      ... = ε : by { rw [← rpow_mul, div_mul_cancel, rpow_one], exact ne_of_gt q_pos, linarith }},
  { exact (continuous_within_at_iff_continuous_at_restrict (λp:ℝ×ℝ, p.1^p.2) _).1
      (continuous_at_rpow_of_ne_zero hx₀ _).continuous_within_at }
end

lemma continuous_at_rpow_of_pos (hy : 0 < y) (x : ℝ) :
  continuous_at (λp:ℝ×ℝ, p.1^p.2) (x, y) :=
continuous_within_at.continuous_at
  (continuous_on_iff_continuous_restrict.2 continuous_rpow_aux3 _ hy)
  (mem_nhds_sets (by { convert is_open_prod is_open_univ (is_open_lt' (0:ℝ)), ext, finish }) hy)

lemma continuous_at_rpow {x y : ℝ} (h : x ≠ 0 ∨ 0 < y) :
  continuous_at (λp:ℝ×ℝ, p.1^p.2) (x, y) :=
by { cases h, exact continuous_at_rpow_of_ne_zero h _, exact continuous_at_rpow_of_pos h x }

variables {α : Type*} [topological_space α] {f g : α → ℝ}

/--
`real.rpow` is continuous at all points except for the lower half of the y-axis.
In other words, the function `λp:ℝ×ℝ, p.1^p.2` is continuous at `(x, y)` if `x ≠ 0` or `y > 0`.

Multiple forms of the claim is provided in the current section.
-/
lemma continuous_rpow (h : ∀a, f a ≠ 0 ∨ 0 < g a) (hf : continuous f) (hg : continuous g):
  continuous (λa:α, (f a) ^ (g a)) :=
continuous_iff_continuous_at.2 $ λ a,
begin
  show continuous_at ((λp:ℝ×ℝ, p.1^p.2) ∘ (λa, (f a, g a))) a,
  refine continuous_at.comp _ (continuous_iff_continuous_at.1 (hf.prod_mk hg) _),
  { replace h := h a, cases h,
    { exact continuous_at_rpow_of_ne_zero h _ },
    { exact continuous_at_rpow_of_pos h _ }},
end

lemma continuous_rpow_of_ne_zero (h : ∀a, f a ≠ 0) (hf : continuous f) (hg : continuous g):
  continuous (λa:α, (f a) ^ (g a)) := continuous_rpow (λa, or.inl $ h a) hf hg

lemma continuous_rpow_of_pos (h : ∀a, 0 < g a) (hf : continuous f) (hg : continuous g):
  continuous (λa:α, (f a) ^ (g a)) := continuous_rpow (λa, or.inr $ h a) hf hg

end prove_rpow_is_continuous

section sqrt

lemma sqrt_eq_rpow : sqrt = λx:ℝ, x ^ (1/(2:ℝ)) :=
begin
  funext, by_cases h : 0 ≤ x,
  { rw [← mul_self_inj_of_nonneg, mul_self_sqrt h, ← pow_two, ← rpow_nat_cast, ← rpow_mul h],
    norm_num, exact sqrt_nonneg _, exact rpow_nonneg_of_nonneg h _ },
  { replace h : x < 0 := lt_of_not_ge h,
    have : 1 / (2:ℝ) * π = π / (2:ℝ), ring,
    rw [sqrt_eq_zero_of_nonpos (le_of_lt h), rpow_def_of_neg h, this, cos_pi_div_two, mul_zero] }
end

lemma continuous_sqrt : continuous sqrt :=
by rw sqrt_eq_rpow; exact continuous_rpow_of_pos (λa, by norm_num) continuous_id continuous_const

end sqrt

section exp

/-- The real exponential function tends to +infinity at +infinity -/
lemma tendsto_exp_at_top : tendsto exp at_top at_top :=
begin
  have A : tendsto (λx:ℝ, x + 1) at_top at_top :=
    tendsto_at_top_add_const_right at_top 1 tendsto_id,
  have B : ∀ᶠ x in at_top, x + 1 ≤ exp x,
  { have : ∀ᶠ (x : ℝ) in at_top, 0 ≤ x := mem_at_top 0,
    filter_upwards [this],
    exact λx hx, add_one_le_exp_of_nonneg hx },
  exact tendsto_at_top_mono' at_top B A
end

/-- The real exponential function tends to 0 at -infinity or, equivalently, `exp(-x)` tends to `0`
at +infinity -/
lemma tendsto_exp_neg_at_top_nhds_0 : tendsto (λx, exp (-x)) at_top (𝓝 0) :=
(tendsto_inv_at_top_zero.comp (tendsto_exp_at_top)).congr (λx, (exp_neg x).symm)

/-- The function `exp(x)/x^n` tends to +infinity at +infinity, for any natural number `n` -/
lemma tendsto_exp_div_pow_at_top (n : ℕ) : tendsto (λx, exp x / x^n) at_top at_top :=
begin
  have n_pos : (0 : ℝ) < n + 1 := nat.cast_add_one_pos n,
  have n_ne_zero : (n : ℝ) + 1 ≠ 0 := ne_of_gt n_pos,
  have A : ∀x:ℝ, 0 < x → exp (x / (n+1)) / (n+1)^n ≤ exp x / x^n,
  { assume x hx,
    let y := x / (n+1),
    have y_pos : 0 < y := div_pos hx n_pos,
    have : exp (x / (n+1)) ≤ (n+1)^n * (exp x / x^n), from calc
      exp y = exp y * 1 : by simp
      ... ≤ exp y * (exp y / y)^n : begin
          apply mul_le_mul_of_nonneg_left (one_le_pow_of_one_le _ n) (le_of_lt (exp_pos _)),
          apply one_le_div_of_le _ y_pos,
          apply le_trans _ (add_one_le_exp_of_nonneg (le_of_lt y_pos)),
          exact le_add_of_le_of_nonneg (le_refl _) (zero_le_one)
        end
      ... = exp y * exp (n * y) / y^n :
        by rw [div_pow, exp_nat_mul, mul_div_assoc]
      ... = exp ((n + 1) * y) / y^n :
        by rw [← exp_add, add_mul, one_mul, add_comm]
      ... = exp x / (x / (n+1))^n :
        by { dsimp [y], rw mul_div_cancel' _ n_ne_zero }
      ... = (n+1)^n * (exp x / x^n) :
        by rw [← mul_div_assoc, div_pow, div_div_eq_mul_div, mul_comm],
    rwa div_le_iff' (pow_pos n_pos n) },
  have B : ∀ᶠ x in at_top, exp (x / (n+1)) / (n+1)^n ≤ exp x / x^n :=
    mem_at_top_sets.2 ⟨1, λx hx, A _ (lt_of_lt_of_le zero_lt_one hx)⟩,
  have C : tendsto (λx, exp (x / (n+1)) / (n+1)^n) at_top at_top :=
    tendsto_at_top_div (pow_pos n_pos n)
      (tendsto_exp_at_top.comp (tendsto_at_top_div (nat.cast_add_one_pos n) tendsto_id)),
  exact tendsto_at_top_mono' at_top B C
end

/-- The function `x^n * exp(-x)` tends to `0` at +infinity, for any natural number `n`. -/
lemma tendsto_pow_mul_exp_neg_at_top_nhds_0 (n : ℕ) : tendsto (λx, x^n * exp (-x)) at_top (𝓝 0) :=
(tendsto_inv_at_top_zero.comp (tendsto_exp_div_pow_at_top n)).congr $ λx,
  by rw [function.comp_app, inv_eq_one_div, div_div_eq_mul_div, one_mul, div_eq_mul_inv, exp_neg]

end exp

end real

lemma has_deriv_at.rexp {f : ℝ → ℝ} {f' x : ℝ} (hf : has_deriv_at f f' x) :
  has_deriv_at (real.exp ∘ f) (real.exp (f x) * f') x :=
(real.has_deriv_at_exp (f x)).comp x hf

lemma has_deriv_within_at.rexp {f : ℝ → ℝ} {f' x : ℝ} {s : set ℝ}
  (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (real.exp ∘ f) (real.exp (f x) * f') s x :=
(real.has_deriv_at_exp (f x)).comp_has_deriv_within_at x hf

namespace nnreal

/-- The nonnegative real power function `x^y`, defined for `x : nnreal` and `y : ℝ ` as the
restriction of the real power function. For `x > 0`, it is equal to `exp (y log x)`. For `x = 0`,
one sets `0 ^ 0 = 1` and `0 ^ y = 0` for `y ≠ 0`. -/
noncomputable def rpow (x : nnreal) (y : ℝ) : nnreal :=
⟨(x : ℝ) ^ y, real.rpow_nonneg_of_nonneg x.2 y⟩

noncomputable instance : has_pow nnreal ℝ := ⟨rpow⟩

@[simp] lemma rpow_eq_pow (x : nnreal) (y : ℝ) : rpow x y = x ^ y := rfl

@[simp, move_cast] lemma coe_rpow (x : nnreal) (y : ℝ) : ((x ^ y : nnreal) : ℝ) = (x : ℝ) ^ y := rfl

@[simp] lemma rpow_zero (x : nnreal) : x ^ (0 : ℝ) = 1 :=
by { rw ← nnreal.coe_eq, exact real.rpow_zero _ }

@[simp] lemma rpow_eq_zero_iff {x : nnreal} {y : ℝ} : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 :=
begin
  rw [← nnreal.coe_eq, coe_rpow, ← nnreal.coe_eq_zero],
  exact real.rpow_eq_zero_iff_of_nonneg x.2
end

@[simp] lemma zero_rpow {x : ℝ} (h : x ≠ 0) : (0 : nnreal) ^ x = 0 :=
by { rw ← nnreal.coe_eq, exact real.zero_rpow h }

@[simp] lemma rpow_one (x : nnreal) : x ^ (1 : ℝ) = x :=
by { rw ← nnreal.coe_eq, exact real.rpow_one _ }

@[simp] lemma one_rpow (x : ℝ) : (1 : nnreal) ^ x = 1 :=
by { rw ← nnreal.coe_eq, exact real.one_rpow _ }

lemma rpow_add {x : nnreal} (y z : ℝ) (hx : 0 < x) : x ^ (y + z) = x ^ y * x ^ z :=
by { rw ← nnreal.coe_eq, exact real.rpow_add _ _ hx }

lemma rpow_mul (x : nnreal) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z :=
by { rw ← nnreal.coe_eq, exact real.rpow_mul x.2 y z }

lemma rpow_neg (x : nnreal) (y : ℝ) : x ^ -y = (x ^ y)⁻¹ :=
by { rw ← nnreal.coe_eq, exact real.rpow_neg x.2 _ }

@[simp] lemma rpow_nat_cast (x : nnreal) (n : ℕ) : x ^ (n : ℝ) = x ^ n :=
by { rw [← nnreal.coe_eq, coe_pow], exact real.rpow_nat_cast (x : ℝ) n }

lemma mul_rpow {x y : nnreal} {z : ℝ}  : (x*y)^z = x^z * y^z :=
by { rw ← nnreal.coe_eq, exact real.mul_rpow x.2 y.2 }

lemma one_le_rpow {x : nnreal} {z : ℝ} (h : 1 ≤ x) (h₁ : 0 ≤ z) : 1 ≤ x^z :=
real.one_le_rpow h h₁

lemma rpow_le_rpow {x y : nnreal} {z: ℝ} (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x^z ≤ y^z :=
real.rpow_le_rpow x.2 h₁ h₂

lemma rpow_lt_rpow {x y : nnreal} {z: ℝ} (h₁ : x < y) (h₂ : 0 < z) : x^z < y^z :=
real.rpow_lt_rpow x.2 h₁ h₂

lemma rpow_lt_rpow_of_exponent_lt {x : nnreal} {y z : ℝ} (hx : 1 < x) (hyz : y < z) : x^y < x^z :=
real.rpow_lt_rpow_of_exponent_lt hx hyz

lemma rpow_le_rpow_of_exponent_le {x : nnreal} {y z : ℝ} (hx : 1 ≤ x) (hyz : y ≤ z) : x^y ≤ x^z :=
real.rpow_le_rpow_of_exponent_le hx hyz

lemma rpow_lt_rpow_of_exponent_gt {x : nnreal} {y z : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) :
  x^y < x^z :=
real.rpow_lt_rpow_of_exponent_gt hx0 hx1 hyz

lemma rpow_le_rpow_of_exponent_ge {x : nnreal} {y z : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hyz : z ≤ y) :
  x^y ≤ x^z :=
real.rpow_le_rpow_of_exponent_ge hx0 hx1 hyz

lemma rpow_le_one {x : nnreal} {e : ℝ} (he : 0 ≤ e) (hx2 : x ≤ 1) : x^e ≤ 1 :=
real.rpow_le_one he x.2 hx2

lemma one_lt_rpow {x : nnreal} {z : ℝ} (hx : 1 < x) (hz : 0 < z) : 1 < x^z :=
real.one_lt_rpow hx hz

lemma rpow_lt_one {x : nnreal} {z : ℝ} (hx : 0 < x) (hx1 : x < 1) (hz : 0 < z) : x^z < 1 :=
real.rpow_lt_one hx hx1 hz

lemma pow_nat_rpow_nat_inv (x : nnreal) {n : ℕ} (hn : 0 < n) :
  (x ^ n) ^ (n⁻¹ : ℝ) = x :=
by { rw [← nnreal.coe_eq, coe_rpow, coe_pow], exact real.pow_nat_rpow_nat_inv x.2 hn }

lemma rpow_nat_inv_pow_nat (x : nnreal) {n : ℕ} (hn : 0 < n) :
  (x ^ (n⁻¹ : ℝ)) ^ n = x :=
by { rw [← nnreal.coe_eq, coe_pow, coe_rpow], exact real.rpow_nat_inv_pow_nat x.2 hn }

lemma continuous_at_rpow {x : nnreal} {y : ℝ} (h : x ≠ 0 ∨ 0 < y) :
  continuous_at (λp:nnreal×ℝ, p.1^p.2) (x, y) :=
begin
  have : (λp:nnreal×ℝ, p.1^p.2) = nnreal.of_real ∘ (λp:ℝ×ℝ, p.1^p.2) ∘ (λp:nnreal × ℝ, (p.1.1, p.2)),
  { ext p,
    rw [← nnreal.coe_eq, coe_rpow, coe_of_real _ (real.rpow_nonneg_of_nonneg p.1.2 _)],
    refl },
  rw this,
  refine continuous_of_real.continuous_at.comp (continuous_at.comp _ _),
  { apply real.continuous_at_rpow,
    simp at h,
    rw ← (nnreal.coe_eq_zero x) at h,
    exact h },
  { exact ((continuous_subtype_val.comp continuous_fst).prod_mk continuous_snd).continuous_at }
end

end nnreal

lemma filter.tendsto.nnrpow {α : Type*} {f : filter α} {u : α → nnreal} {v : α → ℝ} {x : nnreal} {y : ℝ}
  (hx : tendsto u f (𝓝 x)) (hy : tendsto v f (𝓝 y)) (h : x ≠ 0 ∨ 0 < y) :
  tendsto (λ a, (u a) ^ (v a)) f (𝓝 (x ^ y)) :=
tendsto.comp (nnreal.continuous_at_rpow h) (tendsto.prod_mk_nhds hx hy)
