/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.calculus.deriv
import analysis.calculus.fderiv_analytic

/-!
# One dimensional derivatives for analytic functions.

If a function `f : 𝕜 → F` where `𝕜` is a normed field and `F` is a normed space
has a power series at `x`, it has a derivative there.
-/

universes u v w
noncomputable theory
open_locale ennreal
open filter asymptotics

variables {𝕜 : Type u} [nondiscrete_normed_field 𝕜]
variables {F : Type v} [normed_group F] [normed_space 𝕜 F]
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
