/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
import analysis.calculus.inverse
import analysis.complex.real_deriv
import analysis.special_functions.exp

/-!
# Complex and real exponential

In this file we prove that `complex.exp` and `real.exp` are infinitely smooth functions.

## Tags

exp, derivative
-/

noncomputable theory

open filter asymptotics set function
open_locale classical topological_space

namespace complex

/-- The complex exponential is everywhere differentiable, with the derivative `exp x`. -/
lemma has_deriv_at_exp (x : ℂ) : has_deriv_at exp (exp x) x :=
begin
  rw has_deriv_at_iff_is_o_nhds_zero,
  have : (1 : ℕ) < 2 := by norm_num,
  refine (is_O.of_bound (∥exp x∥) _).trans_is_o (is_o_pow_id this),
  filter_upwards [metric.ball_mem_nhds (0 : ℂ) zero_lt_one],
  simp only [metric.mem_ball, dist_zero_right, normed_field.norm_pow],
  exact λ z hz, exp_bound_sq x z hz.le,
end

lemma differentiable_exp : differentiable ℂ exp :=
λx, (has_deriv_at_exp x).differentiable_at

lemma differentiable_at_exp {x : ℂ} : differentiable_at ℂ exp x :=
differentiable_exp x

@[simp] lemma deriv_exp : deriv exp = exp :=
funext $ λ x, (has_deriv_at_exp x).deriv

@[simp] lemma iter_deriv_exp : ∀ n : ℕ, (deriv^[n] exp) = exp
| 0 := rfl
| (n+1) := by rw [iterate_succ_apply, deriv_exp, iter_deriv_exp n]

lemma times_cont_diff_exp : ∀ {n}, times_cont_diff ℂ n exp :=
begin
  refine times_cont_diff_all_iff_nat.2 (λ n, _),
  induction n with n ihn,
  { exact times_cont_diff_zero.2 continuous_exp },
  { rw times_cont_diff_succ_iff_deriv,
    use differentiable_exp,
    rwa deriv_exp }
end

lemma has_strict_deriv_at_exp (x : ℂ) : has_strict_deriv_at exp (exp x) x :=
times_cont_diff_exp.times_cont_diff_at.has_strict_deriv_at' (has_deriv_at_exp x) le_rfl

lemma has_strict_fderiv_at_exp_real (x : ℂ) :
  has_strict_fderiv_at exp (exp x • (1 : ℂ →L[ℝ] ℂ)) x :=
(has_strict_deriv_at_exp x).complex_to_real_fderiv

lemma is_open_map_exp : is_open_map exp :=
open_map_of_strict_deriv has_strict_deriv_at_exp exp_ne_zero

end complex

section
variables {f : ℂ → ℂ} {f' x : ℂ} {s : set ℂ}

lemma has_strict_deriv_at.cexp (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ x, complex.exp (f x)) (complex.exp (f x) * f') x :=
(complex.has_strict_deriv_at_exp (f x)).comp x hf

lemma has_deriv_at.cexp (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, complex.exp (f x)) (complex.exp (f x) * f') x :=
(complex.has_deriv_at_exp (f x)).comp x hf

lemma has_deriv_within_at.cexp (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, complex.exp (f x)) (complex.exp (f x) * f') s x :=
(complex.has_deriv_at_exp (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_cexp (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  deriv_within (λx, complex.exp (f x)) s x = complex.exp (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.cexp.deriv_within hxs

@[simp] lemma deriv_cexp (hc : differentiable_at ℂ f x) :
  deriv (λx, complex.exp (f x)) x = complex.exp (f x) * (deriv f x) :=
hc.has_deriv_at.cexp.deriv

end

section
variables {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} {s : set ℝ}

open complex

lemma has_strict_deriv_at.cexp_real (h : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ x, exp (f x)) (exp (f x) * f') x :=
(has_strict_fderiv_at_exp_real (f x)).comp_has_strict_deriv_at x h

lemma has_deriv_at.cexp_real (h : has_deriv_at f f' x) :
  has_deriv_at (λ x, exp (f x)) (exp (f x) * f') x :=
(has_strict_fderiv_at_exp_real (f x)).has_fderiv_at.comp_has_deriv_at x h

lemma has_deriv_within_at.cexp_real (h : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, exp (f x)) (exp (f x) * f') s x :=
(has_strict_fderiv_at_exp_real (f x)).has_fderiv_at.comp_has_deriv_within_at x h

end

section

variables {E : Type*} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {f' : E →L[ℂ] ℂ}
  {x : E} {s : set E}

lemma has_strict_fderiv_at.cexp (hf : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (λ x, complex.exp (f x)) (complex.exp (f x) • f') x :=
(complex.has_strict_deriv_at_exp (f x)).comp_has_strict_fderiv_at x hf

lemma has_fderiv_within_at.cexp (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, complex.exp (f x)) (complex.exp (f x) • f') s x :=
(complex.has_deriv_at_exp (f x)).comp_has_fderiv_within_at x hf

lemma has_fderiv_at.cexp (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, complex.exp (f x)) (complex.exp (f x) • f') x :=
has_fderiv_within_at_univ.1 $ hf.has_fderiv_within_at.cexp

lemma differentiable_within_at.cexp (hf : differentiable_within_at ℂ f s x) :
  differentiable_within_at ℂ (λ x, complex.exp (f x)) s x :=
hf.has_fderiv_within_at.cexp.differentiable_within_at

@[simp] lemma differentiable_at.cexp (hc : differentiable_at ℂ f x) :
  differentiable_at ℂ (λx, complex.exp (f x)) x :=
hc.has_fderiv_at.cexp.differentiable_at

lemma differentiable_on.cexp (hc : differentiable_on ℂ f s) :
  differentiable_on ℂ (λx, complex.exp (f x)) s :=
λx h, (hc x h).cexp

@[simp] lemma differentiable.cexp (hc : differentiable ℂ f) :
  differentiable ℂ (λx, complex.exp (f x)) :=
λx, (hc x).cexp

lemma times_cont_diff.cexp {n} (h : times_cont_diff ℂ n f) :
  times_cont_diff ℂ n (λ x, complex.exp (f x)) :=
complex.times_cont_diff_exp.comp h

lemma times_cont_diff_at.cexp {n} (hf : times_cont_diff_at ℂ n f x) :
  times_cont_diff_at ℂ n (λ x, complex.exp (f x)) x :=
complex.times_cont_diff_exp.times_cont_diff_at.comp x hf

lemma times_cont_diff_on.cexp {n} (hf : times_cont_diff_on ℂ n f s) :
  times_cont_diff_on ℂ n (λ x, complex.exp (f x)) s :=
complex.times_cont_diff_exp.comp_times_cont_diff_on  hf

lemma times_cont_diff_within_at.cexp {n} (hf : times_cont_diff_within_at ℂ n f s x) :
  times_cont_diff_within_at ℂ n (λ x, complex.exp (f x)) s x :=
complex.times_cont_diff_exp.times_cont_diff_at.comp_times_cont_diff_within_at x hf

end

namespace real

variables {x y z : ℝ}

lemma has_strict_deriv_at_exp (x : ℝ) : has_strict_deriv_at exp (exp x) x :=
(complex.has_strict_deriv_at_exp x).real_of_complex

lemma has_deriv_at_exp (x : ℝ) : has_deriv_at exp (exp x) x :=
(complex.has_deriv_at_exp x).real_of_complex

lemma times_cont_diff_exp {n} : times_cont_diff ℝ n exp :=
complex.times_cont_diff_exp.real_of_complex

lemma differentiable_exp : differentiable ℝ exp :=
λx, (has_deriv_at_exp x).differentiable_at

lemma differentiable_at_exp : differentiable_at ℝ exp x :=
differentiable_exp x

@[simp] lemma deriv_exp : deriv exp = exp :=
funext $ λ x, (has_deriv_at_exp x).deriv

@[simp] lemma iter_deriv_exp : ∀ n : ℕ, (deriv^[n] exp) = exp
| 0 := rfl
| (n+1) := by rw [iterate_succ_apply, deriv_exp, iter_deriv_exp n]

end real


section
/-! Register lemmas for the derivatives of the composition of `real.exp` with a differentiable
function, for standalone use and use with `simp`. -/

variables {f : ℝ → ℝ} {f' x : ℝ} {s : set ℝ}

lemma has_strict_deriv_at.exp (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ x, real.exp (f x)) (real.exp (f x) * f') x :=
(real.has_strict_deriv_at_exp (f x)).comp x hf

lemma has_deriv_at.exp (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, real.exp (f x)) (real.exp (f x) * f') x :=
(real.has_deriv_at_exp (f x)).comp x hf

lemma has_deriv_within_at.exp (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, real.exp (f x)) (real.exp (f x) * f') s x :=
(real.has_deriv_at_exp (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_exp (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λx, real.exp (f x)) s x = real.exp (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.exp.deriv_within hxs

@[simp] lemma deriv_exp (hc : differentiable_at ℝ f x) :
  deriv (λx, real.exp (f x)) x = real.exp (f x) * (deriv f x) :=
hc.has_deriv_at.exp.deriv

end

section
/-! Register lemmas for the derivatives of the composition of `real.exp` with a differentiable
function, for standalone use and use with `simp`. -/

variables {E : Type*} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {f' : E →L[ℝ] ℝ}
  {x : E} {s : set E}

lemma times_cont_diff.exp {n} (hf : times_cont_diff ℝ n f) :
  times_cont_diff ℝ n (λ x, real.exp (f x)) :=
real.times_cont_diff_exp.comp hf

lemma times_cont_diff_at.exp {n} (hf : times_cont_diff_at ℝ n f x) :
  times_cont_diff_at ℝ n (λ x, real.exp (f x)) x :=
real.times_cont_diff_exp.times_cont_diff_at.comp x hf

lemma times_cont_diff_on.exp {n} (hf : times_cont_diff_on ℝ n f s) :
  times_cont_diff_on ℝ n (λ x, real.exp (f x)) s :=
real.times_cont_diff_exp.comp_times_cont_diff_on  hf

lemma times_cont_diff_within_at.exp {n} (hf : times_cont_diff_within_at ℝ n f s x) :
  times_cont_diff_within_at ℝ n (λ x, real.exp (f x)) s x :=
real.times_cont_diff_exp.times_cont_diff_at.comp_times_cont_diff_within_at x hf

lemma has_fderiv_within_at.exp (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, real.exp (f x)) (real.exp (f x) • f') s x :=
(real.has_deriv_at_exp (f x)).comp_has_fderiv_within_at x hf

lemma has_fderiv_at.exp (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, real.exp (f x)) (real.exp (f x) • f') x :=
(real.has_deriv_at_exp (f x)).comp_has_fderiv_at x hf

lemma has_strict_fderiv_at.exp (hf : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (λ x, real.exp (f x)) (real.exp (f x) • f') x :=
(real.has_strict_deriv_at_exp (f x)).comp_has_strict_fderiv_at x hf

lemma differentiable_within_at.exp (hf : differentiable_within_at ℝ f s x) :
  differentiable_within_at ℝ (λ x, real.exp (f x)) s x :=
hf.has_fderiv_within_at.exp.differentiable_within_at

@[simp] lemma differentiable_at.exp (hc : differentiable_at ℝ f x) :
  differentiable_at ℝ (λx, real.exp (f x)) x :=
hc.has_fderiv_at.exp.differentiable_at

lemma differentiable_on.exp (hc : differentiable_on ℝ f s) :
  differentiable_on ℝ (λx, real.exp (f x)) s :=
λ x h, (hc x h).exp

@[simp] lemma differentiable.exp (hc : differentiable ℝ f) :
  differentiable ℝ (λx, real.exp (f x)) :=
λ x, (hc x).exp

lemma fderiv_within_exp (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  fderiv_within ℝ (λx, real.exp (f x)) s x = real.exp (f x) • (fderiv_within ℝ f s x) :=
hf.has_fderiv_within_at.exp.fderiv_within hxs

@[simp] lemma fderiv_exp (hc : differentiable_at ℝ f x) :
  fderiv ℝ (λx, real.exp (f x)) x = real.exp (f x) • (fderiv ℝ f x) :=
hc.has_fderiv_at.exp.fderiv

end
