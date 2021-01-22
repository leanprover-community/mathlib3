/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import analysis.analytic.basic

/-!
# Linear functions are analytic

In this file we prove that a `continuous_linear_map` defines an analytic function with
the formal power series `f x = f a + f (x - a)`.
-/

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{F : Type*} [normed_group F] [normed_space 𝕜 F]

open_locale topological_space classical big_operators nnreal ennreal
open set filter asymptotics

noncomputable theory

namespace continuous_linear_map

/-- Formal power series of a continuous linear map `f : E →L[𝕜] F` at `x : E`:
`f y = f x + f (y - x)`. -/
@[simp] def fpower_series (f : E →L[𝕜] F) (x : E) : formal_multilinear_series 𝕜 E F
| 0 := continuous_multilinear_map.curry0 𝕜 _ (f x)
| 1 := (continuous_multilinear_curry_fin1 𝕜 _ _).symm f
| _ := 0

@[simp] lemma fpower_series_apply_add_two (f : E →L[𝕜] F) (x : E) (n : ℕ) :
  f.fpower_series x (n + 2) = 0 := rfl

@[simp] lemma fpower_series_radius (f : E →L[𝕜] F) (x : E) : (f.fpower_series x).radius = ∞ :=
(f.fpower_series x).radius_eq_top_of_forall_image_add_eq_zero 2 $ λ n, rfl

protected theorem has_fpower_series_on_ball (f : E →L[𝕜] F) (x : E) :
  has_fpower_series_on_ball f (f.fpower_series x) x ∞ :=
{ r_le := by simp,
  r_pos := ennreal.coe_lt_top,
  has_sum := λ y _, (has_sum_nat_add_iff' 2).1 $
    by simp [finset.sum_range_succ, ← sub_sub, has_sum_zero] }

protected theorem has_fpower_series_at (f : E →L[𝕜] F) (x : E) :
  has_fpower_series_at f (f.fpower_series x) x :=
⟨∞, f.has_fpower_series_on_ball x⟩

protected theorem analytic_at (f : E →L[𝕜] F) (x : E) : analytic_at 𝕜 f x :=
(f.has_fpower_series_at x).analytic_at

end continuous_linear_map
