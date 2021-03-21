/-
Copyright (c) 2020 Kexing Ying and Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Kevin Buzzard
-/

import data.set.finite
import data.set.disjointed
import algebra.big_operators
import data.indicator_function

/-!
# Finite products and sums over types and sets

We define products sums over types and subsets of types, with no finiteness hypotheses. All infinite
product and sums are defined to be junk values (i.e. one or zero). This approach is sometimes easier
to use than `finset.sum` when issues arise with `finset` and `fintype` being data.

## Main definitions

We use the following variables:

* `α`, `β` - types with no structure;
* `s`, `t` - sets
* `M`, `N` - additive or multiplicative commutative monoids
* `f`, `g` - functions

Definitions in this file:

* `finsum f : M` : the sum of `f x` as `x` ranges over the support of `f`, if it's finite.
   Zero otherwise.

* `finsum_in s f : M` : the sum of `f x` as `x` ranges over the elements of `s` for which `f x ≠ 0`,
  if this is a finite sum. Zero otherwise.

* `finprod f : M` : the product of `f x` as `x` ranges over the multiplicative support of `f`, if
   it's finite. One otherwise.

* `finprod_in s f : M` : the product of `f x` as `x` ranges over the elements of `s` for which
  `f x ≠ 1`, if this is a finite sum. One otherwise.

## Notation

* `∑ᶠ i, f i` and `∑ᶠ i : α, f i` for `finsum f`

* `∑ᶠ i in s, f i` for `finsum_in s f`

* `∏ᶠ i, f i` and `∑ᶠ i : α, f i` for `finprod f`

* `∏ᶠ i in s, f i` for `finprod_in s f`

## Implementation notes

`finsum` and `finprod` is "yet another way of doing finite sums and products in Lean". However
experiments in the wild (e.g. with matroids) indicate that it is a helpful approach in settings
where the user is not interested in computability and wants to do reasoning without running into
typeclass diamonds caused by the constructive finiteness used in definitions such as `finset` and
`fintype`. By sticking solely to `set.finite` we avoid these problems. We are aware that there are
other solutions but for beginner mathematicians this approach is easier in practice.

Another application is the construction of a partition of unity from a collection of “bump”
function. In this case the finite set depends on the point and it's convenient to have a definition
that does not mention the set explicitly.

## Todo

We did not add `is_finite (X : Type) : Prop`, because it is simply `nonempty (fintype X)`.
There is work on `fincard` in the pipeline, which returns the cardinality of `X` if it
is finite, and 0 otherwise.

## Tags

finsum, finsum_in, finprod, finprod_in, finite sum, finite product
-/

open_locale classical
open function set

/-!
### Definition and relation to `finset.sum` and `finset.prod`
-/

section finsum

variables {α β M N : Type*} [add_comm_monoid M] [add_comm_monoid N]

open_locale big_operators

/-- Sum of `f x` as `x` ranges over the elements of the support of `f`, if it's finite. Zero
  otherwise. -/
@[irreducible] noncomputable def finsum (f : α → M) : M :=
if h : finite (support f) then ∑ i in h.to_finset, f i else 0

/-- Sum of `f x` over `x ∈ s` such that `f x ≠ 0`, if this set is finite. Zero otherwise. -/
noncomputable def finsum_in (s : set α) (f : α → M) : M :=
finsum (s.indicator f)

/-- Product of `f x` as `x` ranges over the elements of the multiplicative support of `f`, if it's
finite. One otherwise. -/
@[irreducible, to_additive finsum]
noncomputable def finprod {M : Type*} [comm_monoid M] (f : α → M) : M :=
if h : finite (mul_support f) then ∏ i in h.to_finset, f i else 1

/-- Product of `f x` over `x ∈ s` such that `f x ≠ 1`, if this set is finite. One otherwise. -/
@[to_additive]
noncomputable def finprod_in {M : Type*} [comm_monoid M] (s : set α) (f : α → M) : M :=
finprod (s.indicator f)

localized "notation `∑ᶠ` binders `, ` r:(scoped:67 f, finsum f) := r"
  in big_operators

localized "notation `∑ᶠ` binders ` in ` s `, ` r:(scoped:67 f, finsum_in s f) := r"
  in big_operators

lemma finsum_eq_sum_of_support_to_finset_subset (f : α → M) (hf : finite (support f))
  {s : finset α} (h : hf.to_finset ⊆ s) :
  ∑ᶠ i, f i = ∑ i in s, f i :=
begin
  rw [finsum, dif_pos hf],
  exact finset.sum_subset h (λ x _, not_imp_comm.1 hf.mem_to_finset.2)
end

lemma finsum_eq_sum_of_support_subset (f : α → M) {s : finset α} (h : support f ⊆ s) :
  ∑ᶠ i, f i = ∑ i in s, f i :=
finsum_eq_sum_of_support_to_finset_subset f (s.finite_to_set.subset h) $
  λ x hx, h $ (finite.mem_to_finset _).1 hx

lemma finsum_def (f : α → M) :
  ∑ᶠ i : α, f i = if h : (support f).finite then finset.sum (h.to_finset) f else 0 :=
by rw finsum

lemma finsum_in_def (s : set α) (f : α → M) :
  ∑ᶠ i in s, f i = finsum (s.indicator f) := rfl

lemma finsum_of_infinite_support {f : α → M} (hf : (support f).infinite) :
  ∑ᶠ i, f i = 0 :=
by rw [finsum_def, dif_neg hf]

lemma finsum_eq_sum (f : α → M) (hf : (support f).finite) :
  ∑ᶠ i : α, f i = ∑ i in hf.to_finset, f i :=
by rw [finsum_def, dif_pos hf]

lemma finsum_eq_sum_of_fintype [fintype α] (f : α → M) :
  ∑ᶠ i : α, f i = ∑ i, f i :=
finsum_eq_sum_of_support_subset _ $ by simp only [finset.coe_univ, set.subset_univ]

lemma finsum_in_eq_sum_of_mem_iff (f : α → M) {s : set α} {t : finset α}
  (h : ∀ {x}, f x ≠ 0 → (x ∈ s ↔ x ∈ t)) :
  ∑ᶠ i in s, f i = ∑ i in t, f i :=
begin
  have : support (s.indicator f) ⊆ t,
  { rw [set.support_indicator], intros x hx, exact (h hx.2).1 hx.1 },
  rw [finsum_in, finsum_eq_sum_of_support_subset _ this],
  refine finset.sum_congr rfl (λ x hx, indicator_apply_eq_self.2 $ λ hxs, _),
  contrapose! hxs,
  exact (h hxs).2 hx
end

lemma finsum_in_eq_sum_of_inter_support_eq (f : α → M) {s : set α} {t : finset α}
  (h : s ∩ support f = t ∩ support f) :
  ∑ᶠ i in s, f i = ∑ i in t, f i :=
finsum_in_eq_sum_of_mem_iff _ $ by simpa [set.ext_iff] using h

lemma finsum_in_eq_sum_of_subset (f : α → M) {s : set α} {t : finset α}
  (h₁ : s ∩ support f ⊆ t) (h₂ : ↑t ⊆ s) :
  ∑ᶠ i in s, f i = ∑ i in t, f i :=
finsum_in_eq_sum_of_mem_iff _ $ λ x hx, ⟨λ h, h₁ ⟨h, hx⟩, λ h, h₂ h⟩

lemma finsum_in_eq_sum (f : α → M) {s : set α}
  (hf : (s ∩ support f).finite) :
  ∑ᶠ i in s, f i = ∑ i in hf.to_finset, f i :=
finsum_in_eq_sum_of_inter_support_eq _ $ by simp [inter_assoc]

lemma finsum_in_eq_sum_filter (f : α → M) (s : set α)
  (hf : (support f).finite) :
  ∑ᶠ i in s, f i = ∑ i in finset.filter (∈ s) hf.to_finset, f i :=
finsum_in_eq_sum_of_inter_support_eq _ $ by simp [inter_comm, inter_left_comm]

lemma finsum_in_eq_to_finset_sum (f : α → M) (s : set α) [fintype s] :
  ∑ᶠ i in s, f i = ∑ i in s.to_finset, f i :=
finsum_in_eq_sum_of_inter_support_eq _ $ by rw [coe_to_finset]

lemma finsum_in_eq_finite_to_finset_sum (f : α → M) {s : set α} (hs : s.finite) :
  ∑ᶠ i in s, f i = ∑ i in hs.to_finset, f i :=
finsum_in_eq_sum_of_inter_support_eq _ $ by rw [hs.coe_to_finset]

lemma finsum_in_coe_eq_sum (f : α → M) (s : finset α) :
  ∑ᶠ i in ↑s, f i = ∑ i in s, f i :=
finsum_in_eq_sum_of_inter_support_eq _ rfl

lemma finsum_in_eq_zero_of_infinite {f : α → M} {s : set α}
  (hs : (s ∩ support f).infinite) : ∑ᶠ i in s, f i = 0 :=
finsum_of_infinite_support $ by rwa [← support_indicator] at hs

lemma finsum_in_inter_support (f : α → M) (s : set α) :
  ∑ᶠ i in (s ∩ support f), f i = ∑ᶠ i in s, f i :=
by rw [finsum_in_def, finsum_in_def, indicator_inter_support]

lemma finsum_in_inter_support_eq (f : α → M) (s t : set α)
  (h : s ∩ support f = t ∩ support f) :
  ∑ᶠ i in s, f i = ∑ᶠ i in t, f i :=
by rw [← finsum_in_inter_support, h, finsum_in_inter_support]

lemma finsum_in_inter_support_eq' (f : α → M) (s t : set α)
  (h : ∀ x ∈ support f, x ∈ s ↔ x ∈ t) :
  ∑ᶠ i in s, f i = ∑ᶠ i in t, f i :=
begin
  apply finsum_in_inter_support_eq,
  ext x,
  exact and_congr_left (h x)
end

lemma finsum_in_univ (f : α → M) : ∑ᶠ i in set.univ, f i = ∑ᶠ i : α, f i :=
by rw [finsum_in, indicator_univ]

variables {f g : α → M} {a b : α} {s t : set α}

@[congr]
lemma finsum_in_congr (h₀ : s = t) (h₁ : ∀ x ∈ t, f x = g x) : finsum_in s f = finsum_in t g :=
by { subst h₀, rw [finsum_in, finsum_in, indicator_congr h₁] }

/-!
### Distributivity w.r.t. addition, subtraction, and (scalar) multiplication
-/

/-- Given the support of `f` and `g` are finite, the sum over `f + g` equals the sum over `f` plus
  the sum over `g`. -/
lemma finsum_add_distrib (hf : (support f).finite) (hg : (support g).finite) :
  ∑ᶠ i, (f i + g i) = ∑ᶠ i, f i + ∑ᶠ i, g i :=
begin
  rw [finsum_eq_sum_of_support_to_finset_subset _ hf (finset.subset_union_left _ _),
    finsum_eq_sum_of_support_to_finset_subset _ hg (finset.subset_union_right _ _),
    ← finset.sum_add_distrib],
  refine finsum_eq_sum_of_support_subset _ _,
  simp [support_add]
end

/-- A more general version of `finsum_in_distrib` that requires `s ∩ support f` and
  `s ∩ support g` instead of `s` to be finite. -/
lemma finsum_in_add_distrib' (hf : (s ∩ support f).finite) (hg : (s ∩ support g).finite) :
  ∑ᶠ i in s, (f i + g i) = ∑ᶠ i in s, f i + ∑ᶠ i in s, g i :=
begin
  rw [← support_indicator] at hf hg,
  rw [finsum_in, finsum_in, finsum_in, indicator_add, finsum_add_distrib hf hg]
end

@[simp] lemma finsum_zero : ∑ᶠ i : α, (0 : M) = 0 :=
by { rw finsum_def, split_ifs; simp }

/-- The sum on any set over the zero function equals zero. -/
lemma finsum_in_zero (s : set α) : ∑ᶠ i in s, (0 : M) = 0 :=
by rw [finsum_in, indicator_zero, finsum_zero]

/-- The sum on the set `s` over the function `f` equals zero if for all `x ∈ s, f x = 0`. -/
lemma finsum_in_of_eq_on_zero (hf : eq_on f 0 s) : ∑ᶠ i in s, f i = 0 :=
by { rw ← finsum_in_zero s, exact finsum_in_congr rfl hf }

/-- If the sum on `s` over the function `f` is nonzero, then there is some `x ∈ s, f x ≠ 0`. -/
lemma exists_ne_zero_of_finsum_in_ne_zero (h : ∑ᶠ i in s, f i ≠ 0) :
  ∃ x ∈ s, f x ≠ 0 :=
begin
  by_contra h', push_neg at h',
  exact h (finsum_in_of_eq_on_zero h')
end

/-- Given a finite set `s`, the sum on `s` over `f + g` equals the sum over `f` plus the sum over
  `g`. -/
lemma finsum_in_add_distrib (hs : s.finite) :
  ∑ᶠ i in s, (f i + g i) = ∑ᶠ i in s, f i + ∑ᶠ i in s, g i :=
finsum_in_add_distrib' (hs.inter_of_left _) (hs.inter_of_left _)

lemma finsum_hom [add_comm_monoid N] {f : α → M} (g : M →+ N)
  (hf : (support f).finite) :
  ∑ᶠ i, g (f i) = g (∑ᶠ i, f i) :=
begin
  rw [finsum_eq_sum _ hf, g.map_sum],
  refine finsum_eq_sum_of_support_subset _ _,
  simp [support_comp_subset g.map_zero]
end

/-- A more general version of `finsum_in_hom` that requires `s ∩ support f` and instead of
  `s` to be finite. -/
lemma finsum_in_hom' [add_comm_monoid N] {f : α → M} (g : M →+ N)
  (h₀ : (s ∩ support f).finite) :
  ∑ᶠ i in s, (g (f i)) = g (∑ᶠ j in s, f j) :=
begin
  rw [finsum_in, indicator_comp_of_zero g.map_zero, finsum_hom, finsum_in],
  rwa support_indicator
end

/-- Given a monoid homomorphism `g : β → M`, and a function `f : α → β`, the sum on `s` over `g ∘ f`
  equals `g` of the sum on `s` over `f`. -/
lemma finsum_in_hom [add_comm_monoid N] (f : α → M) (g : M →+ N) (hs : s.finite) :
  ∑ᶠ i in s, (g ∘ f) i = g (∑ᶠ j in s, f j) :=
finsum_in_hom' g (hs.inter_of_left _)

lemma finsum_in_hom'' [add_comm_monoid N] (f : α → M) (g : M →+ N) (hs : s.finite) :
  ∑ᶠ i in s, g (f i) = g (∑ᶠ j in s, f j) :=
finsum_in_hom f g hs

/-!
### `finsum_in` and set operations
-/

/-- The sum on an empty set over any function is zero. -/
@[simp] lemma finsum_in_empty : ∑ᶠ i in ∅, f i = 0 :=
by rw [finsum_in, indicator_empty, finsum_zero]

/-- A set `s` is not empty if the sum on `s` is not equal to zero. -/
lemma nonempty_of_finsum_in_ne_zero (h : ∑ᶠ i in s, f i ≠ 0) : s ≠ ∅ :=
λ h', h $ h'.symm ▸ finsum_in_empty


/-- Given finite sets `s` and `t`, the sum on `s ∪ t` over the function `f` plus the sum on `s ∩ t`
  over `f` equals the sum on `s` over `f` plus the sum on `t` over `f`. -/
lemma finsum_in_union_inter (hs : s.finite) (ht : t.finite) :
  ∑ᶠ i in (s ∪ t), f i + ∑ᶠ i in (s ∩ t), f i = ∑ᶠ i in s, f i + ∑ᶠ i in t, f i :=
begin
  unfreezingI { lift s to finset α using hs, lift t to finset α using ht },
  simp only [finsum_in_coe_eq_sum, ← finset.coe_union, ← finset.coe_inter, finset.sum_union_inter]
end

/-- A more general version of `finsum_in_union_inter` that requires `s ∩ support f` and
  `t ∩ support f` instead of `s` and `t` to be finite. -/
lemma finsum_in_union_inter'
  (hs : (s ∩ support f).finite) (ht : (t ∩ support f).finite) :
  ∑ᶠ i in (s ∪ t), f i + ∑ᶠ i in (s ∩ t), f i = ∑ᶠ i in s, f i + ∑ᶠ i in t, f i :=
begin
  rw [← finsum_in_inter_support f s, ← finsum_in_inter_support f t, ← finsum_in_union_inter hs ht,
    ← union_inter_distrib_right, finsum_in_inter_support, ← finsum_in_inter_support f (s ∩ t)],
  congr' 2,
  rw [inter_left_comm, inter_assoc, inter_assoc, inter_self, inter_left_comm]
end

/-- A more general version of `finsum_in_union` that requires `s ∩ support f` and
  `t ∩ support f` instead of `s` and `t` to be finite. -/
lemma finsum_in_union'
  (hs : (s ∩ support f).finite) (ht : (t ∩ support f).finite)
  (hst : disjoint s t) : ∑ᶠ i in (s ∪ t), f i = ∑ᶠ i in s, f i + ∑ᶠ i in t, f i :=
by rw [← finsum_in_union_inter' hs ht, disjoint_iff_inter_eq_empty.1 hst, finsum_in_empty,
  add_zero]

/-- Given two finite disjoint sets `s` and `t`, the sum on `s ∪ t` over the function `f` equals the
  sum on `s` over `f` plus the sum on `t` over `f`. -/
lemma finsum_in_union (hs : s.finite) (ht : t.finite) (hst : disjoint s t) :
  ∑ᶠ i in (s ∪ t), f i = ∑ᶠ i in s, f i + ∑ᶠ i in t, f i :=
finsum_in_union' (hs.inter_of_left _) (ht.inter_of_left _) hst

/-- A more general version of `finsum_in_union'` that requires `s ∩ support f` and
  `t ∩ support f` instead of `s` and `t` to be disjoint -/
lemma finsum_in_union''
  (hs : (s ∩ support f).finite) (ht : (t ∩ support f).finite)
  (hst : disjoint (s ∩ support f) (t ∩ support f)) :
  ∑ᶠ i in (s ∪ t), f i = ∑ᶠ i in s, f i + ∑ᶠ i in t, f i :=
by rw [← finsum_in_inter_support f s, ← finsum_in_inter_support f t, ← finsum_in_union hs ht hst,
  ← union_inter_distrib_right, finsum_in_inter_support]

/-- The sum on a singleton `{a}` over the function `f` is `f a`. -/
@[simp] lemma finsum_in_singleton : ∑ᶠ i in {a}, f i = f a :=
by rw [← finset.coe_singleton, finsum_in_coe_eq_sum, finset.sum_singleton]

/-- A more general version of `finsum_in_insert` that requires `s ∩ support f` instead of
  `s` to be finite. -/
@[simp] lemma finsum_in_insert' (f : α → M) (h : a ∉ s) (hs : (s ∩ support f).finite) :
  ∑ᶠ i in insert a s, f i = f a + ∑ᶠ i in s, f i :=
begin
  rw [insert_eq, finsum_in_union' _ hs, finsum_in_singleton],
  { rwa disjoint_singleton_left },
  { exact (finite_singleton a).inter_of_left _ }
end

/-- Given `a` and element not in the set `s`, the sum on `insert a s` over the function `f` equals
  the `f a` plus the sum on `s` over `f`. -/
lemma finsum_in_insert (f : α → M) (h : a ∉ s) (hs : s.finite) :
  ∑ᶠ i in insert a s, f i = f a + ∑ᶠ i in s, f i :=
finsum_in_insert' f h $ hs.inter_of_left _

/-- If `f a = 0` for all `a ∉ s`, then the sum on `insert a s` over the function `f` equals the sum
  on `s` over `f`. -/
lemma finsum_in_insert_of_eq_zero_if_not_mem (h : a ∉ s → f a = 0) :
  ∑ᶠ i in (insert a s), f i = ∑ᶠ i in s, f i :=
begin
  refine finsum_in_inter_support_eq' _ _ _ (λ x hx, ⟨_, or.inr⟩),
  rintro (rfl|hxs),
  exacts [not_imp_comm.1 h hx, hxs]
end

/-- If `f a = 0`, then the sum on `insert a s` over the function `f` equals the sum on `s` over `f`.
  -/
@[simp] lemma finsum_insert_zero (h : f a = 0) :
  ∑ᶠ i in (insert a s), f i = ∑ᶠ i in s, f i :=
finsum_in_insert_of_eq_zero_if_not_mem (λ _, h)

/-- The sum on the set of two unique elements `{a, b}` over the function `f` equals `f a + f b`. -/
@[simp] lemma finsum_pair (h : a ≠ b) : finsum_in {a, b} f = f a + f b :=
by { rw [finsum_in_insert, finsum_in_singleton], exacts [h, finite_singleton b] }

/-- The sum on the image `g '' s` over the function `f` equals the sum on `s` over `f ∘ g` given `g`
  is injective on `s ∩ support (f ∘ g)`. -/
@[simp] lemma finsum_in_image' {s : set β} {g : β → α} (hg : set.inj_on g (s ∩ support (f ∘ g))) :
  ∑ᶠ i in (g '' s), f i = ∑ᶠ j in s, f (g j) :=
begin
  by_cases hs : finite (s ∩ support (f ∘ g)),
  { have hg : ∀ (x ∈ hs.to_finset) (y ∈ hs.to_finset), g x = g y → x = y,
      by simpa only [hs.mem_to_finset],
    rw [finsum_in_eq_sum _ hs, ← finset.sum_image hg],
    refine finsum_in_eq_sum_of_inter_support_eq f _,
    rw [finset.coe_image, hs.coe_to_finset, ← image_inter_support_eq, inter_assoc, inter_self] },
  { rw [finsum_in_eq_zero_of_infinite hs, finsum_in_eq_zero_of_infinite],
    rwa [image_inter_support_eq, infinite_image_iff hg] }
end

/-- The sum on the image `g '' s` over the function `f` equals the sum on `s` over `f ∘ g` given `g`
  is injective on `s`. -/
@[simp] lemma finsum_in_image {β} {s : set β} {g : β → α} (hg : set.inj_on g s) :
  ∑ᶠ i in (g '' s), f i = ∑ᶠ j in s, f (g j) :=
finsum_in_image' $ hg.mono $ inter_subset_left _ _

/-- The sum on the range of `g` over the function `f` equals the sum over `f ∘ g` given `g`
is injective on `support (f ∘ g)`. -/
lemma finsum_in_range' {g : β → α} (hg : set.inj_on g (support (f ∘ g))) :
  ∑ᶠ i in range g, f i = ∑ᶠ j, f (g j) :=
begin
  rw [← image_univ, finsum_in_image', finsum_in_univ],
  rwa univ_inter
end

/-- The sum on the range of `g` over the function `f` equals the sum over `f ∘ g` given `g`
is injective. -/
lemma finsum_in_range {g : β → α} (hg : injective g) :
  ∑ᶠ i in range g, f i = ∑ᶠ j, f (g j) :=
finsum_in_range' (hg.inj_on _)

/-- The sum on `s : set α` over `f : α → M` equals the sum on `t : set β` over `g : β → M` if there
  exists some function `e : α → β` that is bijective on `s` to `t` such that for all `x` in `s`,
  `f x = g (e x)`. -/
lemma finsum_in_eq_of_bij_on {s : set α} {t : set β} {f : α → M} {g : β → M}
  (e : α → β) (he₀ : set.bij_on e s t) (he₁ : ∀ x ∈ s, f x = g (e x)) :
  ∑ᶠ i in s, f i = ∑ᶠ j in t, g j :=
begin
  rw [← set.bij_on.image_eq he₀, finsum_in_image he₀.2.1],
  exact finsum_in_congr rfl he₁
end

lemma finsum_subtype_eq_finsum_in (s : set α) : ∑ᶠ j : s, f j = ∑ᶠ i in s, f i :=
begin
  rw [← finsum_in_range, subtype.range_coe],
  exact subtype.coe_injective
end

lemma finsum_in_inter_add_diff' (h : (s ∩ support f).finite) :
  ∑ᶠ i in s ∩ t, f i + ∑ᶠ i in s \ t, f i = ∑ᶠ i in s, f i :=
begin
  rw [← finsum_in_union', inter_union_diff],
  exacts [h.subset (λ x hx, ⟨hx.1.1, hx.2⟩), h.subset (λ x hx, ⟨hx.1.1, hx.2⟩),
    λ x hx, hx.2.2 hx.1.2]
end

lemma finsum_in_inter_add_diff (h : s.finite) :
  ∑ᶠ i in s ∩ t, f i + ∑ᶠ i in s \ t, f i = ∑ᶠ i in s, f i :=
finsum_in_inter_add_diff' $ h.inter_of_left _

/-- A more general version of `finsum_in_add_diff` that requires `t ∩ support f` instead of
  `t` to be finite. -/
lemma finsum_in_add_diff' (ht : (t ∩ support f).finite) (hst : s ⊆ t) :
  ∑ᶠ i in s, f i + ∑ᶠ i in t \ s, f i = ∑ᶠ i in t, f i :=
by rw [← finsum_in_inter_add_diff' ht, inter_eq_self_of_subset_right hst]

/-- Given a finite set `t` and a subset `s` of `t`, the sum on `s` over the function `f` plus the
  sum on `t \ s` over `f` equals the sum on `t` over `f`. -/
lemma finsum_in_add_diff (ht : t.finite) (hst : s ⊆ t) :
  ∑ᶠ i in s, f i + ∑ᶠ i in t \ s, f i = ∑ᶠ i in t, f i :=
finsum_in_add_diff' (ht.inter_of_left _) hst

/-- An alternative version of `finsum_in_bUnion` in which we sum on the a fintype rather than a
  finite set. -/
lemma finsum_in_Union [fintype β] {t : β → set α}
  (ht : ∀ b, (t b).finite) (h : pairwise (disjoint on t)) :
  ∑ᶠ i in (⋃ x : β, t x), f i = ∑ᶠ i, (∑ᶠ j in (t i), f j) :=
begin
  unfreezingI { lift t to β → finset α using ht },
  rw [← bUnion_univ, ← finset.coe_univ, ← finset.coe_bUnion,
    finsum_in_coe_eq_sum, finset.sum_bUnion],
  { simp only [finsum_in_coe_eq_sum, finsum_eq_sum_of_fintype] },
  { exact λ x _ y _ hxy, finset.disjoint_iff_disjoint_coe.2 (h x y hxy) }
end

/-- Given the function `t : β → set α` in which for all `b : β`, `t b` is finite and for all
  distinct `x y ∈ s`, `t x` and `t y` are disjoint, then the sum on `⋃ x ∈ s, t x` over the
  function `f` equals the sum on `s` over `λ x, finsum_in (t x) f`. -/
lemma finsum_in_bUnion {s : set β} {t : β → set α} (hs : s.finite)
  (ht : ∀ b ∈ s, (t b).finite) (h : pairwise_on s (disjoint on t)) :
  ∑ᶠ i in (⋃ x ∈ s, t x), f i = ∑ᶠ i in s, (∑ᶠ j in (t i), f j) :=
begin
  haveI := hs.fintype,
  rw [← Union_subtype, finsum_in_Union, ← finsum_subtype_eq_finsum_in],
  exacts [λ b, ht b b.2, λ x y hxy, h x x.2 y y.2 (subtype.coe_injective.ne hxy)]
end

/-- An alternative version of `finsum_in_bUnion` in which `t` is a finite set of `set α`s. -/
lemma finsum_in_sUnion {t : set (set α)} (ht₀ : t.finite)
  (ht₁ : ∀ x ∈ t, set.finite x) (h : pairwise_on t disjoint):
  ∑ᶠ i in (⋃₀ t), f i = ∑ᶠ s in t, (∑ᶠ i in s, f i) :=
by rw [set.sUnion_eq_bUnion, finsum_in_bUnion ht₀ ht₁ h]

/-- Given the function `f : α → β → M`, the finite sets `s : set α`, `t : set β`, the sum on `s`
  over `λ x, finsum_in t (λ y, f x y)` equals the sum on `t` over `λ y, finsum_in s (λ x, f x y)`.
  -/
lemma finsum_in_comm {s : set α} {t : set β}
  (f : α → β → M) (hs : s.finite) (ht : t.finite) :
  ∑ᶠ i in s, ∑ᶠ j in t, f i j = ∑ᶠ j in t, ∑ᶠ i in s, f i j :=
begin
  unfreezingI { lift s to finset α using hs, lift t to finset β using ht },
  simp only [finsum_in_coe_eq_sum],
  exact finset.sum_comm
end

/-- To prove a property of a sum, it suffices to prove that the property is additive and holds on
  summands. -/
lemma finsum_in_induction (p : M → Prop) (hp₀ : p 0)
  (hp₁ : ∀ x y, p x → p y → p (x + y)) (hp₂ : ∀ x ∈ s, p $ f x) :
  p (∑ᶠ i in s, f i) :=
begin
  by_cases hs : (s ∩ support f).finite,
  { rw [finsum_in_eq_sum _ hs],
    refine finset.sum_induction _ p hp₁ hp₀ (λ x hx, hp₂ x _),
    rw hs.mem_to_finset at hx, exact hx.1 },
  { exact (finsum_in_eq_zero_of_infinite hs).symm ▸ hp₀ }
end

end finsum
