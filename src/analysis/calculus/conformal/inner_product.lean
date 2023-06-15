/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
import analysis.calculus.conformal.normed_space
import analysis.inner_product_space.conformal_linear_map

/-!
# Conformal maps between inner product spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A function between inner product spaces is which has a derivative at `x`
is conformal at `x` iff the derivative preserves inner products up to a scalar multiple.
-/

noncomputable theory

variables {E F : Type*}
variables [normed_add_comm_group E] [normed_add_comm_group F]
variables [inner_product_space ℝ E] [inner_product_space ℝ F]

open_locale real_inner_product_space

/-- A real differentiable map `f` is conformal at point `x` if and only if its
    differential `fderiv ℝ f x` at that point scales every inner product by a positive scalar. -/
lemma conformal_at_iff' {f : E → F} {x : E} :
  conformal_at f x ↔
  ∃ (c : ℝ), 0 < c ∧ ∀ (u v : E), ⟪fderiv ℝ f x u, fderiv ℝ f x v⟫ = c * ⟪u, v⟫ :=
by rw [conformal_at_iff_is_conformal_map_fderiv, is_conformal_map_iff]

/-- A real differentiable map `f` is conformal at point `x` if and only if its
    differential `f'` at that point scales every inner product by a positive scalar. -/
lemma conformal_at_iff {f : E → F} {x : E} {f' : E →L[ℝ] F} (h : has_fderiv_at f f' x) :
  conformal_at f x ↔ ∃ (c : ℝ), 0 < c ∧ ∀ (u v : E), ⟪f' u, f' v⟫ = c * ⟪u, v⟫ :=
by simp only [conformal_at_iff', h.fderiv]

/-- The conformal factor of a conformal map at some point `x`. Some authors refer to this function
    as the characteristic function of the conformal map. -/
def conformal_factor_at {f : E → F} {x : E} (h : conformal_at f x) : ℝ :=
classical.some (conformal_at_iff'.mp h)

lemma conformal_factor_at_pos {f : E → F} {x : E} (h : conformal_at f x) :
  0 < conformal_factor_at h :=
(classical.some_spec $ conformal_at_iff'.mp h).1

lemma conformal_factor_at_inner_eq_mul_inner' {f : E → F} {x : E}
  (h : conformal_at f x) (u v : E) :
  ⟪(fderiv ℝ f x) u, (fderiv ℝ f x) v⟫ = (conformal_factor_at h : ℝ) * ⟪u, v⟫ :=
(classical.some_spec $ conformal_at_iff'.mp h).2 u v

lemma conformal_factor_at_inner_eq_mul_inner {f : E → F} {x : E} {f' : E →L[ℝ] F}
  (h : has_fderiv_at f f' x) (H : conformal_at f x) (u v : E) :
  ⟪f' u, f' v⟫ = (conformal_factor_at H : ℝ) * ⟪u, v⟫ :=
(H.differentiable_at.has_fderiv_at.unique h) ▸ conformal_factor_at_inner_eq_mul_inner' H u v
