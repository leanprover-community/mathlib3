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
variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜] [normed_algebra 𝕜 ℂ]

/-- The complex exponential is everywhere differentiable, with the derivative `exp x`. -/
lemma has_deriv_at_exp (x : ℂ) : has_deriv_at exp (exp x) x :=
begin
  rw has_deriv_at_iff_is_o_nhds_zero,
  have : (1 : ℕ) < 2 := by norm_num,
  refine (is_O.of_bound (∥exp x∥) _).trans_is_o (is_o_pow_id this),
  filter_upwards [metric.ball_mem_nhds (0 : ℂ) zero_lt_one],
  simp only [metric.mem_ball, dist_zero_right, norm_pow],
  exact λ z hz, exp_bound_sq x z hz.le,
end

lemma differentiable_exp : differentiable 𝕜 exp :=
λ x, (has_deriv_at_exp x).differentiable_at.restrict_scalars 𝕜

lemma differentiable_at_exp {x : ℂ} : differentiable_at 𝕜 exp x :=
differentiable_exp x

@[simp] lemma deriv_exp : deriv exp = exp :=
funext $ λ x, (has_deriv_at_exp x).deriv

@[simp] lemma iter_deriv_exp : ∀ n : ℕ, (deriv^[n] exp) = exp
| 0 := rfl
| (n+1) := by rw [iterate_succ_apply, deriv_exp, iter_deriv_exp n]

lemma cont_diff_exp : ∀ {n}, cont_diff 𝕜 n exp :=
begin
  refine cont_diff_all_iff_nat.2 (λ n, _),
  have : cont_diff ℂ ↑n exp,
  { induction n with n ihn,
    { exact cont_diff_zero.2 continuous_exp },
    { rw cont_diff_succ_iff_deriv,
      use differentiable_exp,
      rwa deriv_exp }, },
  exact this.restrict_scalars 𝕜
end

lemma has_strict_deriv_at_exp (x : ℂ) : has_strict_deriv_at exp (exp x) x :=
cont_diff_exp.cont_diff_at.has_strict_deriv_at' (has_deriv_at_exp x) le_rfl

lemma has_strict_fderiv_at_exp_real (x : ℂ) :
  has_strict_fderiv_at exp (exp x • (1 : ℂ →L[ℝ] ℂ)) x :=
(has_strict_deriv_at_exp x).complex_to_real_fderiv

lemma is_open_map_exp : is_open_map exp :=
open_map_of_strict_deriv has_strict_deriv_at_exp exp_ne_zero

end complex

section
variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜] [normed_algebra 𝕜 ℂ]
  {f : 𝕜 → ℂ} {f' : ℂ} {x : 𝕜} {s : set 𝕜}

lemma has_strict_deriv_at.cexp (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ x, complex.exp (f x)) (complex.exp (f x) * f') x :=
(complex.has_strict_deriv_at_exp (f x)).comp x hf

lemma has_deriv_at.cexp (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, complex.exp (f x)) (complex.exp (f x) * f') x :=
(complex.has_deriv_at_exp (f x)).comp x hf

lemma has_deriv_within_at.cexp (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, complex.exp (f x)) (complex.exp (f x) * f') s x :=
(complex.has_deriv_at_exp (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_cexp (hf : differentiable_within_at 𝕜 f s x)
  (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (λ x, complex.exp (f x)) s x = complex.exp (f x) * deriv_within f s x :=
hf.has_deriv_within_at.cexp.deriv_within hxs

@[simp] lemma deriv_cexp (hc : differentiable_at 𝕜 f x) :
  deriv (λ x, complex.exp (f x)) x = complex.exp (f x) * deriv f x :=
hc.has_deriv_at.cexp.deriv

end

section
variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜] [normed_algebra 𝕜 ℂ]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] {f : E → ℂ} {f' : E →L[𝕜] ℂ}
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

lemma differentiable_within_at.cexp (hf : differentiable_within_at 𝕜 f s x) :
  differentiable_within_at 𝕜 (λ x, complex.exp (f x)) s x :=
hf.has_fderiv_within_at.cexp.differentiable_within_at

@[simp] lemma differentiable_at.cexp (hc : differentiable_at 𝕜 f x) :
  differentiable_at 𝕜 (λ x, complex.exp (f x)) x :=
hc.has_fderiv_at.cexp.differentiable_at

lemma differentiable_on.cexp (hc : differentiable_on 𝕜 f s) :
  differentiable_on 𝕜 (λ x, complex.exp (f x)) s :=
λ x h, (hc x h).cexp

@[simp] lemma differentiable.cexp (hc : differentiable 𝕜 f) :
  differentiable 𝕜 (λ x, complex.exp (f x)) :=
λ x, (hc x).cexp

lemma cont_diff.cexp {n} (h : cont_diff 𝕜 n f) :
  cont_diff 𝕜 n (λ x, complex.exp (f x)) :=
complex.cont_diff_exp.comp h

lemma cont_diff_at.cexp {n} (hf : cont_diff_at 𝕜 n f x) :
  cont_diff_at 𝕜 n (λ x, complex.exp (f x)) x :=
complex.cont_diff_exp.cont_diff_at.comp x hf

lemma cont_diff_on.cexp {n} (hf : cont_diff_on 𝕜 n f s) :
  cont_diff_on 𝕜 n (λ x, complex.exp (f x)) s :=
complex.cont_diff_exp.comp_cont_diff_on hf

lemma cont_diff_within_at.cexp {n} (hf : cont_diff_within_at 𝕜 n f s x) :
  cont_diff_within_at 𝕜 n (λ x, complex.exp (f x)) s x :=
complex.cont_diff_exp.cont_diff_at.comp_cont_diff_within_at x hf

end

namespace real

variables {x y z : ℝ}

lemma has_strict_deriv_at_exp (x : ℝ) : has_strict_deriv_at exp (exp x) x :=
(complex.has_strict_deriv_at_exp x).real_of_complex

lemma has_deriv_at_exp (x : ℝ) : has_deriv_at exp (exp x) x :=
(complex.has_deriv_at_exp x).real_of_complex

lemma cont_diff_exp {n} : cont_diff ℝ n exp :=
complex.cont_diff_exp.real_of_complex

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

lemma cont_diff.exp {n} (hf : cont_diff ℝ n f) :
  cont_diff ℝ n (λ x, real.exp (f x)) :=
real.cont_diff_exp.comp hf

lemma cont_diff_at.exp {n} (hf : cont_diff_at ℝ n f x) :
  cont_diff_at ℝ n (λ x, real.exp (f x)) x :=
real.cont_diff_exp.cont_diff_at.comp x hf

lemma cont_diff_on.exp {n} (hf : cont_diff_on ℝ n f s) :
  cont_diff_on ℝ n (λ x, real.exp (f x)) s :=
real.cont_diff_exp.comp_cont_diff_on  hf

lemma cont_diff_within_at.exp {n} (hf : cont_diff_within_at ℝ n f s x) :
  cont_diff_within_at ℝ n (λ x, real.exp (f x)) s x :=
real.cont_diff_exp.cont_diff_at.comp_cont_diff_within_at x hf

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
