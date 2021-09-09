/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import analysis.calculus.times_cont_diff

/-!
# Smoothness of `real.sqrt`

In this file we prove that `real.sqrt` is infinitely smooth at all points `x ≠ 0` and provide some
dot-notation lemmas.

## Tags

sqrt, differentiable
-/

open set
open_locale topological_space

namespace real

/-- Local homeomorph between `(0, +∞)` and `(0, +∞)` with `to_fun = λ x, x ^ 2` and
`inv_fun = sqrt`. -/
noncomputable def sq_local_homeomorph : local_homeomorph ℝ ℝ :=
{ to_fun := λ x, x ^ 2,
  inv_fun := sqrt,
  source := Ioi 0,
  target := Ioi 0,
  map_source' := λ x hx, mem_Ioi.2 (pow_pos hx _),
  map_target' := λ x hx, mem_Ioi.2 (sqrt_pos.2 hx),
  left_inv' := λ x hx, sqrt_sq (le_of_lt hx),
  right_inv' := λ x hx, sq_sqrt (le_of_lt hx),
  open_source := is_open_Ioi,
  open_target := is_open_Ioi,
  continuous_to_fun := (continuous_pow 2).continuous_on,
  continuous_inv_fun := continuous_on_id.sqrt }

lemma deriv_sqrt_aux {x : ℝ} (hx : x ≠ 0) :
  has_strict_deriv_at sqrt (1 / (2 * sqrt x)) x ∧ ∀ n, times_cont_diff_at ℝ n sqrt x :=
begin
  cases hx.lt_or_lt with hx hx,
  { rw [sqrt_eq_zero_of_nonpos hx.le, mul_zero, div_zero],
    have : sqrt =ᶠ[𝓝 x] (λ _, 0) := (gt_mem_nhds hx).mono (λ x hx, sqrt_eq_zero_of_nonpos hx.le),
    exact ⟨(has_strict_deriv_at_const x (0 : ℝ)).congr_of_eventually_eq this.symm,
      λ n, times_cont_diff_at_const.congr_of_eventually_eq this⟩ },
  { have : ↑2 * sqrt x ^ (2 - 1) ≠ 0, by simp [(sqrt_pos.2 hx).ne', @two_ne_zero ℝ],
    split,
    { simpa using sq_local_homeomorph.has_strict_deriv_at_symm hx this
        (has_strict_deriv_at_pow 2 _) },
    { exact λ n, sq_local_homeomorph.times_cont_diff_at_symm_deriv this hx
        (has_deriv_at_pow 2 (sqrt x)) (times_cont_diff_at_id.pow 2) } }
end

lemma has_strict_deriv_at_sqrt {x : ℝ} (hx : x ≠ 0) :
  has_strict_deriv_at sqrt (1 / (2 * sqrt x)) x :=
(deriv_sqrt_aux hx).1

lemma times_cont_diff_at_sqrt {x : ℝ} {n : with_top ℕ} (hx : x ≠ 0) :
  times_cont_diff_at ℝ n sqrt x :=
(deriv_sqrt_aux hx).2 n

lemma has_deriv_at_sqrt {x : ℝ} (hx : x ≠ 0) : has_deriv_at sqrt (1 / (2 * sqrt x)) x :=
(has_strict_deriv_at_sqrt hx).has_deriv_at

end real

open real

section deriv

variables {f : ℝ → ℝ} {s : set ℝ} {f' x : ℝ}

lemma has_deriv_within_at.sqrt (hf : has_deriv_within_at f f' s x) (hx : f x ≠ 0) :
  has_deriv_within_at (λ y, sqrt (f y)) (f' / (2 * sqrt (f x))) s x :=
by simpa only [(∘), div_eq_inv_mul, mul_one]
  using (has_deriv_at_sqrt hx).comp_has_deriv_within_at x hf

lemma has_deriv_at.sqrt (hf : has_deriv_at f f' x) (hx : f x ≠ 0) :
  has_deriv_at (λ y, sqrt (f y)) (f' / (2 * sqrt(f x))) x :=
by simpa only [(∘), div_eq_inv_mul, mul_one] using (has_deriv_at_sqrt hx).comp x hf

lemma has_strict_deriv_at.sqrt (hf : has_strict_deriv_at f f' x) (hx : f x ≠ 0) :
  has_strict_deriv_at (λ t, sqrt (f t)) (f' / (2 * sqrt (f x))) x :=
by simpa only [(∘), div_eq_inv_mul, mul_one] using (has_strict_deriv_at_sqrt hx).comp x hf

lemma deriv_within_sqrt (hf : differentiable_within_at ℝ f s x) (hx : f x ≠ 0)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λx, sqrt (f x)) s x = (deriv_within f s x) / (2 * sqrt (f x)) :=
(hf.has_deriv_within_at.sqrt hx).deriv_within hxs

@[simp] lemma deriv_sqrt (hf : differentiable_at ℝ f x) (hx : f x ≠ 0) :
  deriv (λx, sqrt (f x)) x = (deriv f x) / (2 * sqrt (f x)) :=
(hf.has_deriv_at.sqrt hx).deriv

end deriv

section fderiv

variables {E : Type*} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {n : with_top ℕ}
  {s : set E} {x : E} {f' : E →L[ℝ] ℝ}

lemma has_fderiv_at.sqrt (hf : has_fderiv_at f f' x) (hx : f x ≠ 0) :
  has_fderiv_at (λ y, sqrt (f y)) ((1 / (2 * sqrt (f x))) • f') x :=
(has_deriv_at_sqrt hx).comp_has_fderiv_at x hf

lemma has_strict_fderiv_at.sqrt (hf : has_strict_fderiv_at f f' x) (hx : f x ≠ 0) :
  has_strict_fderiv_at (λ y, sqrt (f y)) ((1 / (2 * sqrt (f x))) • f') x :=
(has_strict_deriv_at_sqrt hx).comp_has_strict_fderiv_at x hf

lemma has_fderiv_within_at.sqrt (hf : has_fderiv_within_at f f' s x) (hx : f x ≠ 0) :
  has_fderiv_within_at (λ y, sqrt (f y)) ((1 / (2 * sqrt (f x))) • f') s x :=
(has_deriv_at_sqrt hx).comp_has_fderiv_within_at x hf

lemma differentiable_within_at.sqrt (hf : differentiable_within_at ℝ f s x) (hx : f x ≠ 0) :
  differentiable_within_at ℝ (λ y, sqrt (f y)) s x :=
(hf.has_fderiv_within_at.sqrt hx).differentiable_within_at

lemma differentiable_at.sqrt (hf : differentiable_at ℝ f x) (hx : f x ≠ 0) :
  differentiable_at ℝ (λ y, sqrt (f y)) x :=
(hf.has_fderiv_at.sqrt hx).differentiable_at

lemma differentiable_on.sqrt (hf : differentiable_on ℝ f s) (hs : ∀ x ∈ s, f x ≠ 0) :
  differentiable_on ℝ (λ y, sqrt (f y)) s :=
λ x hx, (hf x hx).sqrt (hs x hx)

lemma differentiable.sqrt (hf : differentiable ℝ f) (hs : ∀ x, f x ≠ 0) :
  differentiable ℝ (λ y, sqrt (f y)) :=
λ x, (hf x).sqrt (hs x)

lemma fderiv_within_sqrt (hf : differentiable_within_at ℝ f s x) (hx : f x ≠ 0)
  (hxs : unique_diff_within_at ℝ s x) :
  fderiv_within ℝ (λx, sqrt (f x)) s x = (1 / (2 * sqrt (f x))) • fderiv_within ℝ f s x :=
(hf.has_fderiv_within_at.sqrt hx).fderiv_within hxs

@[simp] lemma fderiv_sqrt (hf : differentiable_at ℝ f x) (hx : f x ≠ 0) :
  fderiv ℝ (λx, sqrt (f x)) x = (1 / (2 * sqrt (f x))) • fderiv ℝ f x :=
(hf.has_fderiv_at.sqrt hx).fderiv

lemma times_cont_diff_at.sqrt (hf : times_cont_diff_at ℝ n f x) (hx : f x ≠ 0) :
  times_cont_diff_at ℝ n (λ y, sqrt (f y)) x :=
(times_cont_diff_at_sqrt hx).comp x hf

lemma times_cont_diff_within_at.sqrt (hf : times_cont_diff_within_at ℝ n f s x) (hx : f x ≠ 0) :
  times_cont_diff_within_at ℝ n (λ y, sqrt (f y)) s x :=
(times_cont_diff_at_sqrt hx).comp_times_cont_diff_within_at x hf

lemma times_cont_diff_on.sqrt (hf : times_cont_diff_on ℝ n f s) (hs : ∀ x ∈ s, f x ≠ 0) :
  times_cont_diff_on ℝ n (λ y, sqrt (f y)) s :=
λ x hx, (hf x hx).sqrt (hs x hx)

lemma times_cont_diff.sqrt (hf : times_cont_diff ℝ n f) (h : ∀ x, f x ≠ 0) :
  times_cont_diff ℝ n (λ y, sqrt (f y)) :=
times_cont_diff_iff_times_cont_diff_at.2 $ λ x, (hf.times_cont_diff_at.sqrt (h x))

end fderiv
