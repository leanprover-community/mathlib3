/-
Copyright (c) 2019 Gabriel Ebner All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sébastien Gouëzel, Yury Kudryashov, Anatole Dedecker
-/
import analysis.calculus.deriv.basic
import analysis.calculus.fderiv.add

/-!
# One-dimensional derivatives of sums etc

In this file we prove formulas about derivatives of `f + g`, `-f`, `f - g`, and `∑ i, f i x` for
functions from the base field to a normed space over this field.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`analysis/calculus/deriv/basic`.

## Keywords

derivative
-/

universes u v w
open_locale classical topology big_operators filter ennreal
open filter asymptotics set

variables {𝕜 : Type u} [nontrivially_normed_field 𝕜]
variables {F : Type v} [normed_add_comm_group F] [normed_space 𝕜 F]
variables {E : Type w} [normed_add_comm_group E] [normed_space 𝕜 E]

variables {f f₀ f₁ g : 𝕜 → F}
variables {f' f₀' f₁' g' : F}
variables {x : 𝕜}
variables {s t : set 𝕜}
variables {L : filter 𝕜}

section add
/-! ### Derivative of the sum of two functions -/

theorem has_deriv_at_filter.add
  (hf : has_deriv_at_filter f f' x L) (hg : has_deriv_at_filter g g' x L) :
  has_deriv_at_filter (λ y, f y + g y) (f' + g') x L :=
by simpa using (hf.add hg).has_deriv_at_filter

theorem has_strict_deriv_at.add
  (hf : has_strict_deriv_at f f' x) (hg : has_strict_deriv_at g g' x) :
  has_strict_deriv_at (λ y, f y + g y) (f' + g') x :=
by simpa using (hf.add hg).has_strict_deriv_at

theorem has_deriv_within_at.add
  (hf : has_deriv_within_at f f' s x) (hg : has_deriv_within_at g g' s x) :
  has_deriv_within_at (λ y, f y + g y) (f' + g') s x :=
hf.add hg

theorem has_deriv_at.add
  (hf : has_deriv_at f f' x) (hg : has_deriv_at g g' x) :
  has_deriv_at (λ x, f x + g x) (f' + g') x :=
hf.add hg

lemma deriv_within_add (hxs : unique_diff_within_at 𝕜 s x)
  (hf : differentiable_within_at 𝕜 f s x) (hg : differentiable_within_at 𝕜 g s x) :
  deriv_within (λy, f y + g y) s x = deriv_within f s x + deriv_within g s x :=
(hf.has_deriv_within_at.add hg.has_deriv_within_at).deriv_within hxs

@[simp] lemma deriv_add
  (hf : differentiable_at 𝕜 f x) (hg : differentiable_at 𝕜 g x) :
  deriv (λy, f y + g y) x = deriv f x + deriv g x :=
(hf.has_deriv_at.add hg.has_deriv_at).deriv

theorem has_deriv_at_filter.add_const
  (hf : has_deriv_at_filter f f' x L) (c : F) :
  has_deriv_at_filter (λ y, f y + c) f' x L :=
add_zero f' ▸ hf.add (has_deriv_at_filter_const x L c)

theorem has_deriv_within_at.add_const
  (hf : has_deriv_within_at f f' s x) (c : F) :
  has_deriv_within_at (λ y, f y + c) f' s x :=
hf.add_const c

theorem has_deriv_at.add_const
  (hf : has_deriv_at f f' x) (c : F) :
  has_deriv_at (λ x, f x + c) f' x :=
hf.add_const c

lemma deriv_within_add_const (hxs : unique_diff_within_at 𝕜 s x) (c : F) :
  deriv_within (λy, f y + c) s x = deriv_within f s x :=
by simp only [deriv_within, fderiv_within_add_const hxs]

lemma deriv_add_const (c : F) : deriv (λy, f y + c) x = deriv f x :=
by simp only [deriv, fderiv_add_const]

@[simp] lemma deriv_add_const' (c : F) : deriv (λ y, f y + c) = deriv f :=
funext $ λ x, deriv_add_const c

theorem has_deriv_at_filter.const_add (c : F) (hf : has_deriv_at_filter f f' x L) :
  has_deriv_at_filter (λ y, c + f y) f' x L :=
zero_add f' ▸ (has_deriv_at_filter_const x L c).add hf

theorem has_deriv_within_at.const_add (c : F) (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ y, c + f y) f' s x :=
hf.const_add c

theorem has_deriv_at.const_add (c : F) (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, c + f x) f' x :=
hf.const_add c

lemma deriv_within_const_add (hxs : unique_diff_within_at 𝕜 s x) (c : F) :
  deriv_within (λy, c + f y) s x = deriv_within f s x :=
by simp only [deriv_within, fderiv_within_const_add hxs]

lemma deriv_const_add (c : F)  : deriv (λy, c + f y) x = deriv f x :=
by simp only [deriv, fderiv_const_add]

@[simp] lemma deriv_const_add' (c : F) : deriv (λ y, c + f y) = deriv f :=
funext $ λ x, deriv_const_add c

end add

section sum
/-! ### Derivative of a finite sum of functions -/

open_locale big_operators

variables {ι : Type*} {u : finset ι} {A : ι → (𝕜 → F)} {A' : ι → F}

theorem has_deriv_at_filter.sum (h : ∀ i ∈ u, has_deriv_at_filter (A i) (A' i) x L) :
  has_deriv_at_filter (λ y, ∑ i in u, A i y) (∑ i in u, A' i) x L :=
by simpa [continuous_linear_map.sum_apply] using (has_fderiv_at_filter.sum h).has_deriv_at_filter

theorem has_strict_deriv_at.sum (h : ∀ i ∈ u, has_strict_deriv_at (A i) (A' i) x) :
  has_strict_deriv_at (λ y, ∑ i in u, A i y) (∑ i in u, A' i) x :=
by simpa [continuous_linear_map.sum_apply] using (has_strict_fderiv_at.sum h).has_strict_deriv_at

theorem has_deriv_within_at.sum (h : ∀ i ∈ u, has_deriv_within_at (A i) (A' i) s x) :
  has_deriv_within_at (λ y, ∑ i in u, A i y) (∑ i in u, A' i) s x :=
has_deriv_at_filter.sum h

theorem has_deriv_at.sum (h : ∀ i ∈ u, has_deriv_at (A i) (A' i) x) :
  has_deriv_at (λ y, ∑ i in u, A i y) (∑ i in u, A' i) x :=
has_deriv_at_filter.sum h

lemma deriv_within_sum (hxs : unique_diff_within_at 𝕜 s x)
  (h : ∀ i ∈ u, differentiable_within_at 𝕜 (A i) s x) :
  deriv_within (λ y, ∑ i in u, A i y) s x = ∑ i in u, deriv_within (A i) s x :=
(has_deriv_within_at.sum (λ i hi, (h i hi).has_deriv_within_at)).deriv_within hxs

@[simp] lemma deriv_sum (h : ∀ i ∈ u, differentiable_at 𝕜 (A i) x) :
  deriv (λ y, ∑ i in u, A i y) x = ∑ i in u, deriv (A i) x :=
(has_deriv_at.sum (λ i hi, (h i hi).has_deriv_at)).deriv

end sum


section neg
/-! ### Derivative of the negative of a function -/

theorem has_deriv_at_filter.neg (h : has_deriv_at_filter f f' x L) :
  has_deriv_at_filter (λ x, -f x) (-f') x L :=
by simpa using h.neg.has_deriv_at_filter

theorem has_deriv_within_at.neg (h : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, -f x) (-f') s x :=
h.neg

theorem has_deriv_at.neg (h : has_deriv_at f f' x) : has_deriv_at (λ x, -f x) (-f') x :=
h.neg

theorem has_strict_deriv_at.neg (h : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ x, -f x) (-f') x :=
by simpa using h.neg.has_strict_deriv_at

lemma deriv_within.neg (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (λy, -f y) s x = - deriv_within f s x :=
by simp only [deriv_within, fderiv_within_neg hxs, continuous_linear_map.neg_apply]

lemma deriv.neg : deriv (λy, -f y) x = - deriv f x :=
by simp only [deriv, fderiv_neg, continuous_linear_map.neg_apply]

@[simp] lemma deriv.neg' : deriv (λy, -f y) = (λ x, - deriv f x) :=
funext $ λ x, deriv.neg

end neg

section neg2
/-! ### Derivative of the negation function (i.e `has_neg.neg`) -/

variables (s x L)

theorem has_deriv_at_filter_neg : has_deriv_at_filter has_neg.neg (-1) x L :=
has_deriv_at_filter.neg $ has_deriv_at_filter_id _ _

theorem has_deriv_within_at_neg : has_deriv_within_at has_neg.neg (-1) s x :=
has_deriv_at_filter_neg _ _

theorem has_deriv_at_neg : has_deriv_at has_neg.neg (-1) x :=
has_deriv_at_filter_neg _ _

theorem has_deriv_at_neg' : has_deriv_at (λ x, -x) (-1) x :=
has_deriv_at_filter_neg _ _

theorem has_strict_deriv_at_neg : has_strict_deriv_at has_neg.neg (-1) x :=
has_strict_deriv_at.neg $ has_strict_deriv_at_id _

lemma deriv_neg : deriv has_neg.neg x = -1 :=
has_deriv_at.deriv (has_deriv_at_neg x)

@[simp] lemma deriv_neg' : deriv (has_neg.neg : 𝕜 → 𝕜) = λ _, -1 :=
funext deriv_neg

@[simp] lemma deriv_neg'' : deriv (λ x : 𝕜, -x) x = -1 :=
deriv_neg x

lemma deriv_within_neg (hxs : unique_diff_within_at 𝕜 s x) : deriv_within has_neg.neg s x = -1 :=
(has_deriv_within_at_neg x s).deriv_within hxs

lemma differentiable_neg : differentiable 𝕜 (has_neg.neg : 𝕜 → 𝕜) :=
differentiable.neg differentiable_id

lemma differentiable_on_neg : differentiable_on 𝕜 (has_neg.neg : 𝕜 → 𝕜) s :=
differentiable_on.neg differentiable_on_id

end neg2

section sub
/-! ### Derivative of the difference of two functions -/

theorem has_deriv_at_filter.sub
  (hf : has_deriv_at_filter f f' x L) (hg : has_deriv_at_filter g g' x L) :
  has_deriv_at_filter (λ x, f x - g x) (f' - g') x L :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem has_deriv_within_at.sub
  (hf : has_deriv_within_at f f' s x) (hg : has_deriv_within_at g g' s x) :
  has_deriv_within_at (λ x, f x - g x) (f' - g') s x :=
hf.sub hg

theorem has_deriv_at.sub
  (hf : has_deriv_at f f' x) (hg : has_deriv_at g g' x) :
  has_deriv_at (λ x, f x - g x) (f' - g') x :=
hf.sub hg

theorem has_strict_deriv_at.sub
  (hf : has_strict_deriv_at f f' x) (hg : has_strict_deriv_at g g' x) :
  has_strict_deriv_at (λ x, f x - g x) (f' - g') x :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma deriv_within_sub (hxs : unique_diff_within_at 𝕜 s x)
  (hf : differentiable_within_at 𝕜 f s x) (hg : differentiable_within_at 𝕜 g s x) :
  deriv_within (λy, f y - g y) s x = deriv_within f s x - deriv_within g s x :=
(hf.has_deriv_within_at.sub hg.has_deriv_within_at).deriv_within hxs

@[simp] lemma deriv_sub
  (hf : differentiable_at 𝕜 f x) (hg : differentiable_at 𝕜 g x) :
  deriv (λ y, f y - g y) x = deriv f x - deriv g x :=
(hf.has_deriv_at.sub hg.has_deriv_at).deriv

theorem has_deriv_at_filter.sub_const
  (hf : has_deriv_at_filter f f' x L) (c : F) :
  has_deriv_at_filter (λ x, f x - c) f' x L :=
by simpa only [sub_eq_add_neg] using hf.add_const (-c)

theorem has_deriv_within_at.sub_const
  (hf : has_deriv_within_at f f' s x) (c : F) :
  has_deriv_within_at (λ x, f x - c) f' s x :=
hf.sub_const c

theorem has_deriv_at.sub_const
  (hf : has_deriv_at f f' x) (c : F) :
  has_deriv_at (λ x, f x - c) f' x :=
hf.sub_const c

lemma deriv_within_sub_const (hxs : unique_diff_within_at 𝕜 s x) (c : F) :
  deriv_within (λy, f y - c) s x = deriv_within f s x :=
by simp only [deriv_within, fderiv_within_sub_const hxs]

lemma deriv_sub_const (c : F) : deriv (λ y, f y - c) x = deriv f x :=
by simp only [deriv, fderiv_sub_const]

theorem has_deriv_at_filter.const_sub (c : F) (hf : has_deriv_at_filter f f' x L) :
  has_deriv_at_filter (λ x, c - f x) (-f') x L :=
by simpa only [sub_eq_add_neg] using hf.neg.const_add c

theorem has_deriv_within_at.const_sub (c : F) (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, c - f x) (-f') s x :=
hf.const_sub c

theorem has_strict_deriv_at.const_sub (c : F) (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ x, c - f x) (-f') x :=
by simpa only [sub_eq_add_neg] using hf.neg.const_add c

theorem has_deriv_at.const_sub (c : F) (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, c - f x) (-f') x :=
hf.const_sub c

lemma deriv_within_const_sub (hxs : unique_diff_within_at 𝕜 s x) (c : F) :
  deriv_within (λy, c - f y) s x = -deriv_within f s x :=
by simp [deriv_within, fderiv_within_const_sub hxs]

lemma deriv_const_sub (c : F) : deriv (λ y, c - f y) x = -deriv f x :=
by simp only [← deriv_within_univ,
  deriv_within_const_sub (unique_diff_within_at_univ : unique_diff_within_at 𝕜 _ _)]

end sub

