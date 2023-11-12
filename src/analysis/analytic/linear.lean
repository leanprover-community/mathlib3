/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import analysis.analytic.basic

/-!
# Linear functions are analytic

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that a `continuous_linear_map` defines an analytic function with
the formal power series `f x = f a + f (x - a)`.
-/

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
{G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]

open_locale topology classical big_operators nnreal ennreal
open set filter asymptotics

noncomputable theory

namespace continuous_linear_map

/-- Formal power series of a continuous linear map `f : E →L[𝕜] F` at `x : E`:
`f y = f x + f (y - x)`. -/
@[simp] def fpower_series (f : E →L[𝕜] F) (x : E) : formal_multilinear_series 𝕜 E F
| 0 := continuous_multilinear_map.curry0 𝕜 _ (f x)
| 1 := (continuous_multilinear_curry_fin1 𝕜 E F).symm f
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

/-- Reinterpret a bilinear map `f : E →L[𝕜] F →L[𝕜] G` as a multilinear map
`(E × F) [×2]→L[𝕜] G`. This multilinear map is the second term in the formal
multilinear series expansion of `uncurry f`. It is given by
`f.uncurry_bilinear ![(x, y), (x', y')] = f x y'`. -/
def uncurry_bilinear (f : E →L[𝕜] F →L[𝕜] G) : (E × F) [×2]→L[𝕜] G :=
@continuous_linear_map.uncurry_left 𝕜 1 (λ _, E × F) G _ _ _ _ _ $
  (↑(continuous_multilinear_curry_fin1 𝕜 (E × F) G).symm : (E × F →L[𝕜] G) →L[𝕜] _).comp $
    f.bilinear_comp (fst _ _ _) (snd _ _ _)

@[simp] lemma uncurry_bilinear_apply (f : E →L[𝕜] F →L[𝕜] G) (m : fin 2 → E × F) :
  f.uncurry_bilinear m = f (m 0).1 (m 1).2 :=
rfl

/-- Formal multilinear series expansion of a bilinear function `f : E →L[𝕜] F →L[𝕜] G`. -/
@[simp] def fpower_series_bilinear (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
  formal_multilinear_series 𝕜 (E × F) G
| 0 := continuous_multilinear_map.curry0 𝕜 _ (f x.1 x.2)
| 1 := (continuous_multilinear_curry_fin1 𝕜 (E × F) G).symm (f.deriv₂ x)
| 2 := f.uncurry_bilinear
| _ := 0

@[simp] lemma fpower_series_bilinear_radius (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
  (f.fpower_series_bilinear x).radius = ∞ :=
(f.fpower_series_bilinear x).radius_eq_top_of_forall_image_add_eq_zero 3 $ λ n, rfl

protected theorem has_fpower_series_on_ball_bilinear (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
  has_fpower_series_on_ball (λ x : E × F, f x.1 x.2) (f.fpower_series_bilinear x) x ∞ :=
{ r_le := by simp,
  r_pos := ennreal.coe_lt_top,
  has_sum := λ y _, (has_sum_nat_add_iff' 3).1 $
    begin
      simp only [finset.sum_range_succ, finset.sum_range_one, prod.fst_add, prod.snd_add,
        f.map_add_add],
      dsimp, simp only [add_comm, sub_self, has_sum_zero]
    end }

protected theorem has_fpower_series_at_bilinear (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
  has_fpower_series_at (λ x : E × F, f x.1 x.2) (f.fpower_series_bilinear x) x :=
⟨∞, f.has_fpower_series_on_ball_bilinear x⟩

protected theorem analytic_at_bilinear (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
  analytic_at 𝕜 (λ x : E × F, f x.1 x.2) x :=
(f.has_fpower_series_at_bilinear x).analytic_at

end continuous_linear_map
