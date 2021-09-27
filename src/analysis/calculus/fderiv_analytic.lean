/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.calculus.deriv
import analysis.analytic.basic

/-!
# Frechet derivatives of analytic functions.

A function expressible as a power series at a point has a Frechet derivative there.
Also the special case in terms of `deriv` when the domain is 1-dimensional.
-/

open filter asymptotics
open_locale ennreal

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E]
variables {F : Type*} [normed_group F] [normed_space 𝕜 F]

section fderiv

variables {p : formal_multilinear_series 𝕜 E F} {r : ℝ≥0∞}
variables {f : E → F} {x : E} {s : set E}

lemma has_fpower_series_at.has_strict_fderiv_at (h : has_fpower_series_at f p x) :
  has_strict_fderiv_at f (continuous_multilinear_curry_fin1 𝕜 E F (p 1)) x :=
begin
  refine h.is_O_image_sub_norm_mul_norm_sub.trans_is_o (is_o.of_norm_right _),
  refine is_o_iff_exists_eq_mul.2 ⟨λ y, ∥y - (x, x)∥, _, eventually_eq.rfl⟩,
  refine (continuous_id.sub continuous_const).norm.tendsto' _ _ _,
  rw [_root_.id, sub_self, norm_zero]
end

lemma has_fpower_series_at.has_fderiv_at (h : has_fpower_series_at f p x) :
  has_fderiv_at f (continuous_multilinear_curry_fin1 𝕜 E F (p 1)) x :=
h.has_strict_fderiv_at.has_fderiv_at

lemma has_fpower_series_at.differentiable_at (h : has_fpower_series_at f p x) :
  differentiable_at 𝕜 f x :=
h.has_fderiv_at.differentiable_at

lemma analytic_at.differentiable_at : analytic_at 𝕜 f x → differentiable_at 𝕜 f x
| ⟨p, hp⟩ := hp.differentiable_at

lemma analytic_at.differentiable_within_at (h : analytic_at 𝕜 f x) :
  differentiable_within_at 𝕜 f s x :=
h.differentiable_at.differentiable_within_at

lemma has_fpower_series_at.fderiv (h : has_fpower_series_at f p x) :
  fderiv 𝕜 f x = continuous_multilinear_curry_fin1 𝕜 E F (p 1) :=
h.has_fderiv_at.fderiv

lemma has_fpower_series_on_ball.differentiable_on [complete_space F]
  (h : has_fpower_series_on_ball f p x r) :
  differentiable_on 𝕜 f (emetric.ball x r) :=
λ y hy, (h.analytic_at_of_mem hy).differentiable_within_at

end fderiv

section deriv

variables {p : formal_multilinear_series 𝕜 𝕜 F} {r : ℝ≥0∞}
variables {f : 𝕜 → F} {x : 𝕜}

protected lemma has_fpower_series_at.has_strict_deriv_at (h : has_fpower_series_at f p x) :
  has_strict_deriv_at f (p 1 (λ _, 1)) x :=
h.has_strict_fderiv_at.has_strict_deriv_at

protected lemma has_fpower_series_at.has_deriv_at (h : has_fpower_series_at f p x) :
  has_deriv_at f (p 1 (λ _, 1)) x :=
h.has_strict_deriv_at.has_deriv_at

protected lemma has_fpower_series_at.deriv (h : has_fpower_series_at f p x) :
  deriv f x = p 1 (λ _, 1) :=
h.has_deriv_at.deriv

end deriv
