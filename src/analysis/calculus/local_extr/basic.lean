/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.calculus.deriv.add

/-!
# Local extrema of smooth functions

## Main definitions

In a real normed space `E` we define `pos_tangent_cone_at (s : set E) (x : E)`.
This would be the same as `tangent_cone_at ℝ≥0 s x` if we had a theory of normed semifields.
This set is used in the proof of Fermat's Theorem (see below), and can be used to formalize
[Lagrange multipliers](https://en.wikipedia.org/wiki/Lagrange_multiplier) and/or
[Karush–Kuhn–Tucker conditions](https://en.wikipedia.org/wiki/Karush–Kuhn–Tucker_conditions).

## Main statements

For each theorem name listed below,
we also prove similar theorems for `min`, `extr` (if applicable)`,
and `(f)deriv` instead of `has_fderiv`.

* `is_local_max_on.has_fderiv_within_at_nonpos` : `f' y ≤ 0` whenever `a` is a local maximum
  of `f` on `s`, `f` has derivative `f'` at `a` within `s`, and `y` belongs to the positive tangent
  cone of `s` at `a`.

* `is_local_max_on.has_fderiv_within_at_eq_zero` : In the settings of the previous theorem, if both
  `y` and `-y` belong to the positive tangent cone, then `f' y = 0`.

* `is_local_max.has_fderiv_at_eq_zero` :
  [Fermat's Theorem](https://en.wikipedia.org/wiki/Fermat's_theorem_(stationary_points)),
  the derivative of a differentiable function at a local extremum point equals zero.

## Implementation notes

For each mathematical fact we prove several versions of its formalization:

* for maxima and minima;
* using `has_fderiv*`/`has_deriv*` or `fderiv*`/`deriv*`.

For the `fderiv*`/`deriv*` versions we omit the differentiability condition whenever it is possible
due to the fact that `fderiv` and `deriv` are defined to be zero for non-differentiable functions.

## References

* [Fermat's Theorem](https://en.wikipedia.org/wiki/Fermat's_theorem_(stationary_points));
* [Tangent cone](https://en.wikipedia.org/wiki/Tangent_cone);

## Tags

local extremum, Fermat's Theorem
-/

universes u v

open filter set
open_locale topology classical

section module

variables {E : Type u} [normed_add_comm_group E] [normed_space ℝ E] {f : E → ℝ} {a : E}
  {f' : E →L[ℝ] ℝ}

/-- "Positive" tangent cone to `s` at `x`; the only difference from `tangent_cone_at`
is that we require `c n → ∞` instead of `‖c n‖ → ∞`. One can think about `pos_tangent_cone_at`
as `tangent_cone_at nnreal` but we have no theory of normed semifields yet. -/
def pos_tangent_cone_at (s : set E) (x : E) : set E :=
{y : E | ∃(c : ℕ → ℝ) (d : ℕ → E), (∀ᶠ n in at_top, x + d n ∈ s) ∧
  (tendsto c at_top at_top) ∧ (tendsto (λn, c n • d n) at_top (𝓝 y))}

lemma pos_tangent_cone_at_mono : monotone (λ s, pos_tangent_cone_at s a) :=
begin
  rintros s t hst y ⟨c, d, hd, hc, hcd⟩,
  exact ⟨c, d, mem_of_superset hd $ λ h hn, hst hn, hc, hcd⟩
end

lemma mem_pos_tangent_cone_at_of_segment_subset {s : set E} {x y : E} (h : segment ℝ x y ⊆ s) :
  y - x ∈ pos_tangent_cone_at s x :=
begin
  let c := λn:ℕ, (2:ℝ)^n,
  let d := λn:ℕ, (c n)⁻¹ • (y-x),
  refine ⟨c, d, filter.univ_mem' (λn, h _),
    tendsto_pow_at_top_at_top_of_one_lt one_lt_two, _⟩,
  show x + d n ∈ segment ℝ x y,
  { rw segment_eq_image',
    refine ⟨(c n)⁻¹, ⟨_, _⟩, rfl⟩,
    exacts [inv_nonneg.2 (pow_nonneg zero_le_two _),
      inv_le_one (one_le_pow_of_one_le one_le_two _)] },
  show tendsto (λ n, c n • d n) at_top (𝓝 (y - x)),
  { convert tendsto_const_nhds, ext n,
    simp only [d, smul_smul],
    rw [mul_inv_cancel, one_smul],
    exact pow_ne_zero _ two_ne_zero }
end

lemma mem_pos_tangent_cone_at_of_segment_subset' {s : set E} {x y : E}
  (h : segment ℝ x (x + y) ⊆ s) :
  y ∈ pos_tangent_cone_at s x :=
by simpa only [add_sub_cancel'] using mem_pos_tangent_cone_at_of_segment_subset h

lemma pos_tangent_cone_at_univ : pos_tangent_cone_at univ a = univ :=
eq_univ_of_forall $ λ x, mem_pos_tangent_cone_at_of_segment_subset' (subset_univ _)

/-- If `f` has a local max on `s` at `a`, `f'` is the derivative of `f` at `a` within `s`, and
`y` belongs to the positive tangent cone of `s` at `a`, then `f' y ≤ 0`. -/
lemma is_local_max_on.has_fderiv_within_at_nonpos {s : set E} (h : is_local_max_on f s a)
  (hf : has_fderiv_within_at f f' s a) {y} (hy : y ∈ pos_tangent_cone_at s a) :
  f' y ≤ 0 :=
begin
  rcases hy with ⟨c, d, hd, hc, hcd⟩,
  have hc' : tendsto (λ n, ‖c n‖) at_top at_top,
    from tendsto_at_top_mono (λ n, le_abs_self _) hc,
  refine le_of_tendsto (hf.lim at_top hd hc' hcd) _,
  replace hd : tendsto (λ n, a + d n) at_top (𝓝[s] (a + 0)),
  from tendsto_inf.2 ⟨tendsto_const_nhds.add (tangent_cone_at.lim_zero _ hc' hcd),
    by rwa tendsto_principal⟩,
  rw [add_zero] at hd,
  replace h : ∀ᶠ n in at_top, f (a + d n) ≤ f a, from mem_map.1 (hd h),
  replace hc : ∀ᶠ n in at_top, 0 ≤ c n, from mem_map.1 (hc (mem_at_top (0:ℝ))),
  filter_upwards [h, hc],
  simp only [smul_eq_mul, mem_preimage, subset_def],
  assume n hnf hn,
  exact mul_nonpos_of_nonneg_of_nonpos hn (sub_nonpos.2 hnf)
end

/-- If `f` has a local max on `s` at `a` and `y` belongs to the positive tangent cone
of `s` at `a`, then `f' y ≤ 0`. -/
lemma is_local_max_on.fderiv_within_nonpos {s : set E} (h : is_local_max_on f s a)
  {y} (hy : y ∈ pos_tangent_cone_at s a) :
  (fderiv_within ℝ f s a : E → ℝ) y ≤ 0 :=
if hf : differentiable_within_at ℝ f s a
then h.has_fderiv_within_at_nonpos hf.has_fderiv_within_at hy
else by { rw fderiv_within_zero_of_not_differentiable_within_at hf, refl }

/-- If `f` has a local max on `s` at `a`, `f'` is a derivative of `f` at `a` within `s`, and
both `y` and `-y` belong to the positive tangent cone of `s` at `a`, then `f' y ≤ 0`. -/
lemma is_local_max_on.has_fderiv_within_at_eq_zero {s : set E} (h : is_local_max_on f s a)
  (hf : has_fderiv_within_at f f' s a) {y} (hy : y ∈ pos_tangent_cone_at s a)
  (hy' : -y ∈ pos_tangent_cone_at s a) :
  f' y = 0 :=
le_antisymm (h.has_fderiv_within_at_nonpos hf hy) $
  by simpa using h.has_fderiv_within_at_nonpos hf hy'

/-- If `f` has a local max on `s` at `a` and both `y` and `-y` belong to the positive tangent cone
of `s` at `a`, then `f' y = 0`. -/
lemma is_local_max_on.fderiv_within_eq_zero {s : set E} (h : is_local_max_on f s a)
  {y} (hy : y ∈ pos_tangent_cone_at s a) (hy' : -y ∈ pos_tangent_cone_at s a) :
  (fderiv_within ℝ f s a : E → ℝ) y = 0 :=
if hf : differentiable_within_at ℝ f s a
then h.has_fderiv_within_at_eq_zero hf.has_fderiv_within_at hy hy'
else by { rw fderiv_within_zero_of_not_differentiable_within_at hf, refl }

/-- If `f` has a local min on `s` at `a`, `f'` is the derivative of `f` at `a` within `s`, and
`y` belongs to the positive tangent cone of `s` at `a`, then `0 ≤ f' y`. -/
lemma is_local_min_on.has_fderiv_within_at_nonneg {s : set E} (h : is_local_min_on f s a)
  (hf : has_fderiv_within_at f f' s a) {y} (hy : y ∈ pos_tangent_cone_at s a) :
  0 ≤ f' y :=
by simpa using h.neg.has_fderiv_within_at_nonpos hf.neg hy

/-- If `f` has a local min on `s` at `a` and `y` belongs to the positive tangent cone
of `s` at `a`, then `0 ≤ f' y`. -/
lemma is_local_min_on.fderiv_within_nonneg {s : set E} (h : is_local_min_on f s a)
  {y} (hy : y ∈ pos_tangent_cone_at s a) :
  (0:ℝ) ≤ (fderiv_within ℝ f s a : E → ℝ) y :=
if hf : differentiable_within_at ℝ f s a
then h.has_fderiv_within_at_nonneg hf.has_fderiv_within_at hy
else by { rw [fderiv_within_zero_of_not_differentiable_within_at hf], refl }

/-- If `f` has a local max on `s` at `a`, `f'` is a derivative of `f` at `a` within `s`, and
both `y` and `-y` belong to the positive tangent cone of `s` at `a`, then `f' y ≤ 0`. -/
lemma is_local_min_on.has_fderiv_within_at_eq_zero {s : set E} (h : is_local_min_on f s a)
  (hf : has_fderiv_within_at f f' s a) {y} (hy : y ∈ pos_tangent_cone_at s a)
  (hy' : -y ∈ pos_tangent_cone_at s a) :
  f' y = 0 :=
by simpa using h.neg.has_fderiv_within_at_eq_zero hf.neg hy hy'

/-- If `f` has a local min on `s` at `a` and both `y` and `-y` belong to the positive tangent cone
of `s` at `a`, then `f' y = 0`. -/
lemma is_local_min_on.fderiv_within_eq_zero {s : set E} (h : is_local_min_on f s a)
  {y} (hy : y ∈ pos_tangent_cone_at s a) (hy' : -y ∈ pos_tangent_cone_at s a) :
  (fderiv_within ℝ f s a : E → ℝ) y = 0 :=
if hf : differentiable_within_at ℝ f s a
then h.has_fderiv_within_at_eq_zero hf.has_fderiv_within_at hy hy'
else by { rw fderiv_within_zero_of_not_differentiable_within_at hf, refl }

/-- **Fermat's Theorem**: the derivative of a function at a local minimum equals zero. -/
lemma is_local_min.has_fderiv_at_eq_zero (h : is_local_min f a) (hf : has_fderiv_at f f' a) :
  f' = 0 :=
begin
  ext y,
  apply (h.on univ).has_fderiv_within_at_eq_zero hf.has_fderiv_within_at;
    rw pos_tangent_cone_at_univ; apply mem_univ
end

/-- **Fermat's Theorem**: the derivative of a function at a local minimum equals zero. -/
lemma is_local_min.fderiv_eq_zero (h : is_local_min f a) : fderiv ℝ f a = 0 :=
if hf : differentiable_at ℝ f a then h.has_fderiv_at_eq_zero hf.has_fderiv_at
else fderiv_zero_of_not_differentiable_at hf

/-- **Fermat's Theorem**: the derivative of a function at a local maximum equals zero. -/
lemma is_local_max.has_fderiv_at_eq_zero (h : is_local_max f a) (hf : has_fderiv_at f f' a) :
  f' = 0 :=
neg_eq_zero.1 $ h.neg.has_fderiv_at_eq_zero hf.neg

/-- **Fermat's Theorem**: the derivative of a function at a local maximum equals zero. -/
lemma is_local_max.fderiv_eq_zero (h : is_local_max f a) : fderiv ℝ f a = 0 :=
if hf : differentiable_at ℝ f a then h.has_fderiv_at_eq_zero hf.has_fderiv_at
else fderiv_zero_of_not_differentiable_at hf

/-- **Fermat's Theorem**: the derivative of a function at a local extremum equals zero. -/
lemma is_local_extr.has_fderiv_at_eq_zero (h : is_local_extr f a) :
  has_fderiv_at f f' a → f' = 0 :=
h.elim is_local_min.has_fderiv_at_eq_zero is_local_max.has_fderiv_at_eq_zero

/-- **Fermat's Theorem**: the derivative of a function at a local extremum equals zero. -/
lemma is_local_extr.fderiv_eq_zero (h : is_local_extr f a) : fderiv ℝ f a = 0 :=
h.elim is_local_min.fderiv_eq_zero is_local_max.fderiv_eq_zero

end module

section real

variables {f : ℝ → ℝ} {f' : ℝ} {a b : ℝ}

/-- **Fermat's Theorem**: the derivative of a function at a local minimum equals zero. -/
lemma is_local_min.has_deriv_at_eq_zero (h : is_local_min f a) (hf : has_deriv_at f f' a) :
  f' = 0 :=
by simpa using continuous_linear_map.ext_iff.1
  (h.has_fderiv_at_eq_zero (has_deriv_at_iff_has_fderiv_at.1 hf)) 1

/-- **Fermat's Theorem**: the derivative of a function at a local minimum equals zero. -/
lemma is_local_min.deriv_eq_zero (h : is_local_min f a) : deriv f a = 0 :=
if hf : differentiable_at ℝ f a then h.has_deriv_at_eq_zero hf.has_deriv_at
else deriv_zero_of_not_differentiable_at hf

/-- **Fermat's Theorem**: the derivative of a function at a local maximum equals zero. -/
lemma is_local_max.has_deriv_at_eq_zero (h : is_local_max f a) (hf : has_deriv_at f f' a) :
  f' = 0 :=
neg_eq_zero.1 $ h.neg.has_deriv_at_eq_zero hf.neg

/-- **Fermat's Theorem**: the derivative of a function at a local maximum equals zero. -/
lemma is_local_max.deriv_eq_zero (h : is_local_max f a) : deriv f a = 0 :=
if hf : differentiable_at ℝ f a then h.has_deriv_at_eq_zero hf.has_deriv_at
else deriv_zero_of_not_differentiable_at hf

/-- **Fermat's Theorem**: the derivative of a function at a local extremum equals zero. -/
lemma is_local_extr.has_deriv_at_eq_zero (h : is_local_extr f a) :
  has_deriv_at f f' a → f' = 0 :=
h.elim is_local_min.has_deriv_at_eq_zero is_local_max.has_deriv_at_eq_zero

/-- **Fermat's Theorem**: the derivative of a function at a local extremum equals zero. -/
lemma is_local_extr.deriv_eq_zero (h : is_local_extr f a) : deriv f a = 0 :=
h.elim is_local_min.deriv_eq_zero is_local_max.deriv_eq_zero

end real
