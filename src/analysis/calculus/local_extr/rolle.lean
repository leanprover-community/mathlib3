/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Anatole Dedecker
-/
import analysis.calculus.local_extr.basic
import topology.algebra.order.rolle

/-!
# Rolle's Theorem

In this file we prove Rolle's Theorem. The theorem says that for a function `f : ℝ → ℝ` such that

* $f$ is differentiable on an open interval $(a, b)$, $a < b$;
* $f$ is continuous on the corresponding closed interval $[a, b]$;
* $f(a) = f(b)$,

there exists a point $c∈(a, b)$ such that $f'(c)=0$.

We prove four versions of this theorem.

* `exists_has_deriv_at_eq_zero` is closest to the statement given above. It assumes that at every
  point $x ∈ (a, b)$ function $f$ has derivative $f'(x)$, then concludes that $f'(c)=0$ for some
  $c∈(a, b)$.

* `exists_deriv_eq_zero` deals with `deriv f` instead of an arbitrary function `f'` and a predicate
  `has_deriv_at`; since we use zero as the "junk" value for `deriv f c`, this version does not
  assume that `f` is differentiable on the open interval.

* `exists_has_deriv_at_eq_zero'` is similar to `exists_has_deriv_at_eq_zero` but instead of assuming
  continuity on the closed interval $[a, b]$ it assumes that $f$ tends to the same limit as $x$
  tends to $a$ from the right and as $x$ tends to $b$ from the left.

* `exists_deriv_eq_zero'` relates to `exists_deriv_eq_zero` as `exists_has_deriv_at_eq_zero'`
  relates to ``exists_has_deriv_at_eq_zero`.

## References

* [Rolle's Theorem](https://en.wikipedia.org/wiki/Rolle's_theorem);

## Keywords

local extremum, Rolle's Theorem
-/

open set filter
open_locale filter topology

variables {f f' : ℝ → ℝ} {a b l : ℝ}

/-- **Rolle's Theorem** `has_deriv_at` version. -/
lemma exists_has_deriv_at_eq_zero (hab : a < b) (hfc : continuous_on f (Icc a b)) (hfI : f a = f b)
  (hff' : ∀ x ∈ Ioo a b, has_deriv_at f (f' x) x) :
  ∃ c ∈ Ioo a b, f' c = 0 :=
let ⟨c, cmem, hc⟩ := exists_local_extr_Ioo hab hfc hfI in
  ⟨c, cmem, hc.has_deriv_at_eq_zero $ hff' c cmem⟩

/-- **Rolle's Theorem** `deriv` version. Note that we do not assume differentiability of `f` because
we use zero as the "junk" value of `deriv f c` when the function `f` is not differentiable at
`c`. -/
lemma exists_deriv_eq_zero (hab : a < b) (hfc : continuous_on f (Icc a b)) (hfI : f a = f b) :
  ∃ c ∈ Ioo a b, deriv f c = 0 :=
let ⟨c, cmem, hc⟩ := exists_local_extr_Ioo hab hfc hfI in
  ⟨c, cmem, hc.deriv_eq_zero⟩

/-- **Rolle's Theorem**, a version for a function on an open interval: if `f` has derivative `f'`
on `(a, b)` and has the same limit `l` at `𝓝[>] a` and `𝓝[<] b`, then `f' c = 0`
for some `c ∈ (a, b)`.  -/
lemma exists_has_deriv_at_eq_zero' (hab : a < b)
  (hfa : tendsto f (𝓝[>] a) (𝓝 l)) (hfb : tendsto f (𝓝[<] b) (𝓝 l))
  (hff' : ∀ x ∈ Ioo a b, has_deriv_at f (f' x) x) :
  ∃ c ∈ Ioo a b, f' c = 0 :=
let ⟨c, cmem, hc⟩ := exists_is_local_extr_Ioo_of_tendsto hab
  (λ x hx, (hff' x hx).continuous_at.continuous_within_at) hfa hfb in
  ⟨c, cmem, hc.has_deriv_at_eq_zero $ hff' c cmem⟩

/-- **Rolle's Theorem**, a version for a function on an open interval: if `f` has the same limit
`l` at `𝓝[>] a` and `𝓝[<] b`, then `deriv f c = 0` for some `c ∈ (a, b)`. This version
does not require differentiability of `f` because we define `deriv f c = 0` whenever `f` is not
differentiable at `c`. -/
lemma exists_deriv_eq_zero' (hab : a < b) (hfa : tendsto f (𝓝[>] a) (𝓝 l))
  (hfb : tendsto f (𝓝[<] b) (𝓝 l)) : ∃ c ∈ Ioo a b, deriv f c = 0 :=
begin
  by_cases h : ∀ x ∈ Ioo a b, differentiable_at ℝ f x,
  { exact exists_has_deriv_at_eq_zero' hab hfa hfb (λ x hx, (h x hx).has_deriv_at) },
  { push_neg at h,
    obtain ⟨c, hc, hcd⟩ := h,
    exact ⟨c, hc, deriv_zero_of_not_differentiable_at hcd⟩ }
end
