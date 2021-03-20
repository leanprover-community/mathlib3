/-
Copyright (c) 2020 Kexing Ying and Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Kevin Buzzard
-/

import data.set.finite
import algebra.big_operators
import data.support
import data.finsupp

/-!
# Finite sums over types and sets

We define sums over types and subsets of types, with no finiteness hypotheses. All infinite
sums are defined to be junk values (i.e. zero). This approach is sometimes easier to use
than `finset.sum` when issues arise with `finset` and `fintype` being data.

## Main definitions

Variables:

`(α : Type u)`
`(s : set α)`
`(M : Type v) [add_comm_monoid M]`
`(f : α → M)`

Definitions in this file:

* `univ' α : finset α` : `α` as a finset if `α` is finite, and the empty finset otherwise

* `finsum f : M` : the sum of `f x` as `x` ranges over the support of `f`, if it's finite.
   Zero otherwise.

* `finsum_in s f : M` : the sum of `f x` as `x` ranges over the elements of `s` for which `f x ≠ 0`,
  if this is a finite sum. Zero otherwise.

## Notation

* `∑ᶠ i, f i` and `∑ᶠ i : α, f i` for `finsum f`

* `∑ᶠ i in s, f i` for `finsum_in s f`

## Implementation notes

There is no `finprod` right now. This is because `function.support` and `finsupp` etc
are all focussed on 0, and there are no analogous definitions for 1.

`finsum` is "yet another way of doing finite sums in Lean". However experiments in the wild
(e.g. with matroids) indicate that it is a helpful approach in settings where the user is
not interested in computability and wants to do reasoning without running into typeclass
diamonds caused by the constructive finiteness used in definitions such as `finset` and
`fintype`. By sticking solely to `set.finite` we avoid these problems. We are aware that
there are other solutions but for beginner mathematicians this approach is easier in practice.

## Todo

We did not add `is_finite (X : Type) : Prop`, because it is simply `nonempty (fintype X)`.
There is work on `fincard` in the pipeline, which returns the cardinality of `X` if it
is finite, and 0 otherwise.

If there were a multiplicative version of `function.support`, returning the terms which
were not mapped to `1`, then this could be refactored into a multiplicative version.

## Tags

finsum, finsum_in, univ', finiteness
-/

open_locale classical
open function set

universes u v w

-- TODO move to data.finset.something?
/-- `set.to_finset' s` is the finset corresponding to `s` if `s` is finite, and the empty set
    otherwise -/
noncomputable def set.to_finset' {α : Type u} (s : set α) : finset α :=
if h : s.finite then h.to_finset else ∅

theorem set.to_finset'_eq_to_finset {α : Type u} {s : set α} [fintype s] :
  s.to_finset' = s.to_finset :=
begin
  have h : s.finite := ⟨infer_instance⟩,
  unfold set.to_finset',
  rw dif_pos h,
  unfold set.finite.to_finset,
  congr',
end

/-!

# finset.univ' -- noncomputable univ (empty set if infinite)

-/

namespace finset

/-- `univ' α` is the finset corresponding to all of α if α is finite, and the empty set otherwise.
Note that it is noncomputable -/
noncomputable def univ' (α : Type u) : finset α :=
if h : nonempty (fintype α) then (classical.choice h).elems else ∅

variable {α : Type u}

/-- `univ' α` is `finset.univ` if `α` is a fintype. -/
@[simp] lemma univ'_eq_univ [h : fintype α] : univ' α = univ :=
by convert (dif_pos (nonempty.intro h))

lemma univ'_eq_empty (h : ¬ nonempty (fintype α)) : univ' α = ∅ :=
dif_neg h

lemma univ'_eq_empty' (h : fintype α → false) : univ' α = ∅ :=
univ'_eq_empty $ not_nonempty_fintype.2 $ ⟨h⟩

lemma mem_univ' [h : fintype α] (x : α) : x ∈ univ' α :=
(@univ'_eq_univ _ h).symm ▸ mem_univ _

@[simp] lemma mem_univ'' [h : nonempty (fintype α)] (x : α) : x ∈ univ' α :=
@mem_univ' α (nonempty.some h) x

end finset

/-!
### Definition and relation to `finset.sum` and `finsupp.sum`
-/

section finsum

variables {α : Type u} {M : Type v} [add_comm_monoid M]

/-- Sum of `f x` as `x` ranges over the elements of the support of `f`, if it's finite. Zero
  otherwise. -/
@[irreducible] noncomputable def finsum (f : α → M) : M :=
if h : ∃ f₀ : α →₀ M, ⇑f₀ = f then h.some.sum (λ i x, x) else 0

/-- Sum of `f x` for `x ∈ s`, if `s ∩ f.support` is finite. Zero if it's infinite.  -/
noncomputable def finsum_in (s : set α) (f : α → M) : M :=
finsum (s.indicator f)

localized "notation `∑ᶠ` binders `, ` r:(scoped:67 f, finsum f) := r"
  in big_operators

localized "notation `∑ᶠ` binders ` in ` s `, ` r:(scoped:67 f, finsum_in s f) := r"
  in big_operators

open_locale big_operators

@[simp] lemma finsum_coe_finsupp (f : α →₀ M) : ∑ᶠ i : α, f i = f.sum (λ i x, x) :=
have ∃ f₀ : α →₀ M, ⇑f₀ = f, from ⟨f, rfl⟩,
by rw [finsum, dif_pos this, finsupp.coe_fn_injective this.some_spec]

lemma finsum_eq_sum_of_support_subset (f : α → M) {s : finset α} (h : support f ⊆ s) :
  ∑ᶠ i, f i = ∑ i in s, f i :=
begin
  lift f to α →₀ M using s.finite_to_set.subset h,
  rw [finsum_coe_finsupp],
  exact f.sum_of_support_subset (by exact_mod_cast h) _ (λ _ _, rfl)
end

lemma finsum_def (f : α → M) :
  ∑ᶠ i : α, f i = if h : (support f).finite then finset.sum (h.to_finset) f else 0 :=
begin
  split_ifs,
  { apply finsum_eq_sum_of_support_subset,
    simp only [set.finite.coe_to_finset, subset.rfl] },
  { rw finsum,
    apply dif_neg,
    rintro ⟨f, rfl⟩,
    exact h f.finite_support }
end

lemma finsum_in_def (s : set α) (f : α → M) :
  ∑ᶠ i in s, f i = finsum (s.indicator f) := rfl

lemma finsum_of_infinite_support {f : α → M} (hf : (support f).infinite) :
  ∑ᶠ i, f i = 0 :=
by rw [finsum_def, dif_neg hf]

lemma finsum_eq_finsupp_sum' (f : α → M) (hf : (support f).finite) :
  ∑ᶠ i : α, f i = finsupp.sum (finsupp.of_support_finite f hf) (λ x m, m) :=
by rw [← finsum_coe_finsupp, finsupp.of_support_finite_coe]

lemma finsum_eq_sum (f : α → M) (hf : (support f).finite) :
  ∑ᶠ i : α, f i = finset.sum hf.to_finset f :=
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

variables {N : Type w} {f g : α → M} {a b : α} {s t : set α}

@[congr]
lemma finsum_in_congr (h₀ : s = t) (h₁ : ∀ x ∈ t, f x = g x) : finsum_in s f = finsum_in t g :=
by { subst h₀, rw [finsum_in, finsum_in, indicator_congr h₁] }

/-!
### Distributivity w.r.t. addition, subtraction, and (scalar) multiplication
-/

/-- Given the support of `f` and `g` are finite, the sum over `f + g` equals the sum over `f` plus
  the sum over `g`. -/
lemma finsum_add_distrib
  (hf : (support f).finite) (hg : (support g).finite) :
  ∑ᶠ i, (f i + g i) = ∑ᶠ i, f i + ∑ᶠ i, g i :=
begin
  unfreezingI { lift f to α →₀ M using hf, lift g to α →₀ M using hg },
  simp only [← finsupp.add_apply, finsum_coe_finsupp],
  exact finsupp.sum_add_index (λ _, rfl) (λ _ _ _, rfl)
end

/-- A more general version of `finsum_in_distrib` that requires `s ∩ support f` and
  `s ∩ support g` instead of `s` to be finite. -/
lemma finsum_in_add_distrib'
  (hf : (s ∩ support f).finite) (hg : (s ∩ support g).finite) :
  ∑ᶠ i in s, (f i + g i) = ∑ᶠ i in s, f i + ∑ᶠ i in s, g i :=
begin
  rw [← support_indicator] at hf hg,
  rw [finsum_in, finsum_in, finsum_in, indicator_add, finsum_add_distrib hf hg]
end

@[simp] lemma finsum_zero : ∑ᶠ i : α, (0 : M) = 0 :=
by { rw finsum_def, split_ifs; simp }

/-- Given a finite set `s`, the sum on `s` over `f + g` equals the sum over `f` plus the sum over
  `g`. -/
lemma finsum_in_add_distrib (hs : s.finite) :
  ∑ᶠ i in s, (f i + g i) = ∑ᶠ i in s, f i + ∑ᶠ i in s, g i :=
finsum_in_add_distrib' (hs.subset $ inter_subset_left _ _) (hs.subset $ inter_subset_left _ _)

lemma finsum_hom [add_comm_monoid N] {f : α → M} (g : M →+ N)
  (hf : (support f).finite) :
  ∑ᶠ i, g (f i) = g (∑ᶠ i, f i) :=
begin
  unfreezingI { lift f to α →₀ M using hf },
  simp only [← @finsupp.map_range_apply _ _ _ _ _ _ g.map_zero],
  rw [finsum_coe_finsupp, finsum_coe_finsupp, g.map_finsupp_sum, finsupp.sum_map_range_index],
  exact λ _, rfl
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
finsum_in_hom' g (hs.subset $ inter_subset_left _ _)

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

/-- A more general version of `finsum_in_union` that requires `s ∩ support f` and
  `t ∩ support f` instead of `s` and `t` to be finite. -/
lemma finsum_in_union'
  (hs : (s ∩ support f).finite) (ht : (t ∩ support f).finite)
  (hst : disjoint s t) : ∑ᶠ i in (s ∪ t), f i = ∑ᶠ i in s, f i + ∑ᶠ i in t, f i :=
begin
  simp only [finsum_in],
  rw ← support_indicator at hs ht,
  rw [indicator_union_of_disjoint hst, finsum_add_distrib hs ht]
end

/-- Given two finite disjoint sets `s` and `t`, the sum on `s ∪ t` over the function `f` equals the
  sum on `s` over `f` plus the sum on `t` over `f`. -/
lemma finsum_in_union (hs : s.finite) (ht : t.finite) (hst : disjoint s t) :
  ∑ᶠ i in (s ∪ t), f i = ∑ᶠ i in s, f i + ∑ᶠ i in t, f i :=
finsum_in_union' (hs.subset $ inter_subset_left _ _) (ht.subset $ inter_subset_left _ _) hst

/-- A more general version of `finsum_in_union'` that requires `s ∩ support f` and
  `t ∩ support f` instead of `s` and `t` to be disjoint -/
lemma finsum_in_union''
  (hs : (s ∩ support f).finite) (ht : (t ∩ support f).finite)
  (hst : disjoint (s ∩ support f) (t ∩ support f)) :
  ∑ᶠ i in (s ∪ t), f i = ∑ᶠ i in s, f i + ∑ᶠ i in t, f i :=
by rw [← finsum_in_inter_support f s, ← finsum_in_inter_support f t, ← finsum_in_union hs ht hst,
  ← union_inter_distrib_right, finsum_in_inter_support]

/-- A more general version of `finsum_in_union_inter` that requires `s ∩ support f` and
  `t ∩ support f` instead of `s` and `t` to be finite. -/
lemma finsum_in_union_inter'
  (hs : (s ∩ support f).finite) (ht : (t ∩ support f).finite) :
  ∑ᶠ i in (s ∪ t), f i + ∑ᶠ i in (s ∩ t), f i = ∑ᶠ i in s, f i + ∑ᶠ i in t, f i :=
begin
  
end

/-- Given `a` and element not in the set `s`, the sum on `insert a s` over the function `f` equals
  the `f a` plus the sum on `s` over `f`. -/
lemma finsum_in_insert (f : α → M) (h : a ∉ s) (hs : s.finite) :
  ∑ᶠ i in insert a s, f i = f a + ∑ᶠ i in s, f i :=
begin
  rw [finsum_in_eq_finite_to_finset_sum f (set.finite.insert a hs),
      finsum_in_eq_finite_to_finset_sum f hs, set.finite.to_finset, set.finite.to_finset,
      ← finset.sum_insert],
    { congr, ext, simp },
    { rw set.mem_to_finset, exact h }
end

/-- A more general version of `finsum_in_insert` that requires `s ∩ support f` instead of
  `s` to be finite. -/
@[simp] lemma finsum_in_insert' (f : α → M) (h : a ∉ s) (hs : (s ∩ support f).finite) :
  ∑ᶠ i in insert a s, f i = f a + ∑ᶠ i in s, f i :=
begin
  by_cases ha : a ∈ support f,
    { have := finsum_in_insert f
        (show a ∉ s ∩ support f, by exact λ h', h h'.1) hs,
      rw [← finsum_in_inter_support] at this,
      rw [← this, finsum_in_inter_support],
      congr, rw [set.insert_inter, set.insert_eq_of_mem ha] },
    { rw [finsum_in_inter_support,
          set.insert_inter_of_not_mem ha,
         ← finsum_in_inter_support, function.nmem_support.1 ha, zero_add] }
end

/-- If `f a = 0` for all `a ∉ s`, then the sum on `insert a s` over the function `f` equals the sum
  on `s` over `f`. -/
lemma finsum_in_insert_of_eq_zero_if_not_mem (h : a ∉ s → f a = 0) :
  ∑ᶠ i in (insert a s), f i = ∑ᶠ i in s, f i :=
begin
  by_cases hs : ((s ∩ support f).finite),
    { by_cases hm : a ∈ s,
        { simp_rw set.insert_eq_of_mem hm },
        { rw [finsum_in_insert' f hm hs, h hm, zero_add] } },
    { rw [finsum_in_eq_zero_of_infinite hs, finsum_in_eq_zero_of_infinite],
      intro hs', apply hs,
      by_cases hm : a ∈ support f,
        { apply set.finite.subset hs',
          apply set.inter_subset_inter_left,
          apply set.subset_insert },
        { rwa set.insert_inter_of_not_mem hm at hs' } }
end

/-- If `f a = 0`, then the sum on `insert a s` over the function `f` equals the sum on `s` over `f`.
  -/
@[simp] lemma finsum_insert_zero (h : f a = 0) :
  ∑ᶠ i in (insert a s), f i = ∑ᶠ i in s, f i :=
finsum_in_insert_of_eq_zero_if_not_mem (λ _, h)

/-- The sum on a singleton `{a}` over the function `f` is `f a`. -/
@[simp] lemma finsum_singleton : ∑ᶠ i in {a}, f i = f a :=
begin
  rw [finsum_in_eq_finite_to_finset_sum f (set.finite_singleton a), set.finite.to_finset,
      ← @finset.sum_singleton _ _ a f _],
  congr, ext, simp
end

/-- The sum on the set of two unique elements `{a, b}` over the function `f` equals `f a + f b`. -/
@[simp] lemma finsum_pair (h : a ≠ b) : finsum_in {a, b} f = f a + f b :=
begin
  rw [finsum_in_eq_finite_to_finset_sum f (show set.finite {a, b}, by simp),
      set.finite.to_finset, ← finset.sum_pair h],
  congr, ext, simp
end

/-- The sum on the image `g '' s` over the function `f` equals the sum on `s` over `f ∘ g` given `g`
  is injective on `s`. -/
@[simp] lemma finsum_in_image {s : set β} {g : β → α}
  (hg : set.inj_on g s) : ∑ᶠ i in (g '' s), f i = ∑ᶠ j in s, f (g j) :=
begin
  by_cases hs : (g '' s ∩ support f).finite,
  { rw [finsum_in_eq_finset_sum _ hs, finsum_in_eq_finset_sum _
          ((set.image_inter_support_finite_iff hg).1 hs)],
    convert @finset.sum_image α _ _ _ _ infer_instance _ _ _,
    { ext,
      simp only [exists_prop, set.mem_image, set.mem_inter_eq, set.finite.mem_to_finset,
        finset.mem_image, ← exists_and_distrib_right, function.mem_support],
      apply exists_congr,
      intro b,
      split,
      { rintro ⟨⟨h1, rfl⟩, h2⟩,
        exact ⟨⟨h1, h2⟩, rfl⟩ },
      { rintro ⟨⟨h1, h2⟩, rfl⟩,
        exact ⟨⟨h1, rfl⟩, h2⟩ } },
    { intros x hx y hy,
      exact hg ((set.finite.mem_to_finset _).1 hx).1 ((set.finite.mem_to_finset _).1 hy).1 } },
  { rw [finsum_in_eq_zero_of_infinite hs, finsum_in_eq_zero_of_infinite],
    intro hs', apply hs,
    rwa set.image_inter_support_finite_iff hg }
end

/-- The sum on `s : set α` over `f : α → M` equals the sum on `t : set β` over `g : β → M` if there
  exists some function `e : α → β` that is bijective on `s` to `t` such that for all `x` in `s`,
  `f x = g (e x)`. -/
lemma finsum_in_eq_of_bij_on {s : set α} {t : set β} {f : α → M} {g : β → M}
  (e : α → β) (he₀ : set.bij_on e s t) (he₁ : ∀ x ∈ s, f x = g (e x)) :
  ∑ᶠ i in s, f i = ∑ᶠ j in t, g j :=
begin
  rw [(set.bij_on.image_eq he₀).symm, finsum_in_image he₀.2.1],
  exact finsum_in_congr rfl he₁
end

lemma finsum_subtype_eq_finsum_in (s : set α) : ∑ᶠ j : s, f j.val = ∑ᶠ i in s, f i :=
begin
  rw ← finsum_eq_finsum_in_univ,
  refine finsum_in_eq_of_bij_on subtype.val _ (λ _ _, rfl),
  exact ⟨λ ⟨x, hx⟩ _, hx, λ _ _ _ _, subtype.eq, λ x hx, ⟨⟨x, hx⟩, set.mem_univ _, rfl⟩⟩,
end

/-- Given finite sets `s` and `t`, the sum on `s ∪ t` over the function `f` plus the sum on `s ∩ t`
  over `f` equals the sum on `s` over `f` plus the sum on `t` over `f`. -/
lemma finsum_in_union_inter (hs : s.finite) (ht : t.finite) :
  ∑ᶠ i in (s ∪ t), f i + ∑ᶠ i in (s ∩ t), f i = ∑ᶠ i in s, f i + ∑ᶠ i in t, f i :=
begin
  rw [finsum_in_eq_finite_to_finset_sum f hs, finsum_in_eq_finite_to_finset_sum f ht,
      finsum_in_eq_finite_to_finset_sum f (set.finite.union hs ht),
      finsum_in_eq_finite_to_finset_sum f (set.finite.subset hs (set.inter_subset_left _ _)),
      set.finite.to_finset],
  convert finset.sum_union_inter,
  { ext,
    rw [set.mem_to_finset, finset.mem_union, set.mem_union],
    simp only [set.finite.mem_to_finset] },
  { ext, simp only [set.mem_inter_eq, set.finite.mem_to_finset, iff_self, finset.mem_inter] },
end

/-- A more general version of `finsum_in_union_inter` that requires `s ∩ support f` and
  `t ∩ support f` instead of `s` and `t` to be finite. -/
lemma finsum_in_union_inter'
  (hs : (s ∩ support f).finite) (ht : (t ∩ support f).finite) :
  ∑ᶠ i in (s ∪ t), f i + ∑ᶠ i in (s ∩ t), f i = ∑ᶠ i in s, f i + ∑ᶠ i in t, f i :=
begin
  rw [finsum_in_inter_support f s, finsum_in_inter_support f t,
      finsum_in_inter_support f (s ∪ t), finsum_in_inter_support f (s ∩ t),
      ← finsum_in_union_inter hs ht, set.inter_distrib_right],
  conv_rhs { congr, skip, congr,
    rw [set.inter_assoc, ← set.inter_assoc _ t, set.inter_comm _ t,
        set.inter_assoc, set.inter_self, ← set.inter_assoc] }
end

/-- Given a finite set `t` and a subset `s` of `t`, the sum on `s` over the function `f` plus the
  sum on `t \ s` over `f` equals the sum on `t` over `f`. -/
lemma finsum_in_sdiff (ht : t.finite) (hst : s ⊆ t) :
  ∑ᶠ i in s, f i + ∑ᶠ i in t \ s, f i = ∑ᶠ i in t, f i :=
begin
  conv_rhs { rw ← set.union_diff_cancel hst },
  exact (finsum_in_union (set.finite.subset ht hst)
    (set.finite.subset ht $ set.diff_subset t s) set.disjoint_diff).symm
end

/-- A more general version of `finsum_in_sdiff` that requires `t ∩ support f` instead of
  `t` to be finite. -/
lemma finsum_in_sdiff' (ht : (t ∩ support f).finite)
  (hst : s ⊆ t) : ∑ᶠ i in s, f i + ∑ᶠ i in t \ s, f i = ∑ᶠ i in t, f i :=
begin
  conv_rhs { rw ← set.union_diff_cancel hst },
  exact (finsum_in_union' (set.finite.subset ht (set.inter_subset_inter_left _ hst))
    (set.finite.subset ht (set.inter_subset_inter (set.diff_subset t s) $ set.subset.refl _))
      set.disjoint_diff).symm
end

/-- Given the function `t : β → set α` in which for all `b : β`, `t b` is finite and for all
  distinct `x y ∈ s`, `t x` and `t y` are disjoint, then the sum on `⋃ x ∈ s, t x` over the
  function `f` equals the sum on `s` over `λ x, finsum_in (t x) f`. -/
lemma finsum_in_bUnion {s : set β} {t : β → set α} (hs : s.finite)
  (ht : ∀ b, (t b).finite) (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → disjoint (t x) (t y)) :
  ∑ᶠ i in (⋃ x ∈ s, t x), f i = ∑ᶠ i in s, (∑ᶠ j in (t i), f j) :=
begin
  rw finsum_in_eq_finite_to_finset_sum _ hs,
  rw finsum_in_eq_finite_to_finset_sum f (set.finite.bUnion hs (λ i _, ht i)),
  conv_rhs { congr, skip, funext, rw finsum_in_eq_finite_to_finset_sum f (ht i) },
  convert @finset.sum_bUnion _ _ _ f _ _ hs.to_finset (λ x, (ht x).to_finset)
    (begin
      intros x hx y hy hxy a ha,
      specialize h x ((set.finite.mem_to_finset _).1 hx) y ((set.finite.mem_to_finset _).1 hy) hxy,
      apply @h a, simpa using ha
    end),
  ext, rw [finset.mem_bUnion, set.finite.mem_to_finset, set.mem_bUnion_iff],
  split; intro ha; rcases ha with ⟨x, hx₀, hx₁⟩,
    exact ⟨x, (set.finite.mem_to_finset _).2 hx₀, (set.finite.mem_to_finset _).2 hx₁⟩,
    exact ⟨x, (set.finite.mem_to_finset _).1 hx₀, (set.finite.mem_to_finset _).1 hx₁⟩
end .

/-- An alternative version of `finsum_in_bUnion` in which we sum on the a fintype rather than a
  finite set. -/
lemma finsum_in_Union [fintype β] {t : β → set α}
  (ht : ∀ b, (t b).finite) (h : ∀ x y, x ≠ y → disjoint (t x) (t y)) :
  ∑ᶠ i in (⋃ x : β, t x), f i = ∑ᶠ i, (∑ᶠ j in (t i), f j) :=
begin
  rw ← finsum_eq_finsum_in_univ,
  rw ← finsum_in_bUnion (set.finite.of_fintype _) ht (λ x _ y _, h x y),
    { congr, funext y, simp only [set.Union_pos, set.mem_univ] },
end

/-- An alternative version of `finsum_in_bUnion` in which `t` is a finite set of `set α`s. -/
lemma finsum_in_sUnion {t : set (set α)} (ht₀ : t.finite)
  (ht₁ : ∀ x ∈ t, set.finite x) (h : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → disjoint x y):
  ∑ᶠ i in (⋃₀ t), f i = ∑ᶠ s in t, (∑ᶠ i in s, f i) :=
begin
  rw [set.sUnion_eq_bUnion],
  convert @finsum_in_bUnion α M _ t f set.univ subtype.val
    (set.univ_finite_iff_nonempty_fintype.mpr ⟨ht₀.fintype⟩)
    (λ s, ht₁ s.1 s.2)
    (λ x hx y hy hxy, h x.1 x.2 y.1 y.2 (λ hn, hxy (subtype.val_injective hn)))
    using 1,
    refine finsum_in_congr (by {ext, simp}) (by simp),
    rw [finsum_eq_finsum_in_univ, ← finsum_subtype_eq_finsum_in ]
end

/-- Given a subset `t` of the set `s`, such that for all elements of `s` not in `t`, `f x = 0`, the
  sum on `t` over `f` equals the sum on `s` over `f`. -/
lemma finsum_in_eq_finsum_in_of_subset (hst : s ⊆ t)
  (hf : ∀ x : α, x ∈ t \ s → f x = 0) : ∑ᶠ i in s, f i = ∑ᶠ i in t, f i :=
begin
  rw [finsum_in_def, finsum_in_def],
  congr', ext x, split_ifs,
  { refl },
  { exact false.elim (h_1 $ hst h) },
  { exact (hf _ ⟨h_1, h⟩).symm },
  { refl }
end

/-- An alternative version of `finsum_in_eq_finsum_in_of_subset'` where we don't use sdiff. -/
lemma finsum_in_eq_finsum_in_of_subset'
  (ht₀ : t ⊆ s) (ht₁ : ∀ x ∈ s, x ∉ t → f x = 0) :
  ∑ᶠ i in t, f i = ∑ᶠ i in s, f i :=
begin
  refine finsum_in_eq_finsum_in_of_subset ht₀ _,
  intros x hx,
  rw set.mem_diff at hx,
  exact ht₁ x hx.1 hx.2,
end

/-- Given a set `t` thats smaller than `s` but greater than `s ∩ support f`, the sum on `t`
  equals the sum on `s`. -/
lemma finsum_in_eq_finsum_in_of_subset''
  (ht₀ : t ⊆ s) (ht₁ : s ∩ support f ⊆ t) :
  ∑ᶠ i in t, f i = ∑ᶠ i in s, f i :=
begin
  refine finsum_in_eq_finsum_in_of_subset' ht₀ (λ _ hx₀ hx₁, _),
  rw ← function.nmem_support,
  exact λ hx₂, hx₁ (ht₁ ⟨hx₀, hx₂⟩)
end

/-- Given the function `f : α → β → M`, the finite sets `s : set α`, `t : set β`, the sum on `s`
  over `λ x, finsum_in t (λ y, f x y)` equals the sum on `t` over `λ y, finsum_in s (λ x, f x y)`.
  -/
lemma finsum_in_comm {s : set α} {t : set β}
  (f : α → β → M) (hs : s.finite) (ht : t.finite) :
  ∑ᶠ i in s, ∑ᶠ j in t, f i j = ∑ᶠ j in t, ∑ᶠ i in s, f i j :=
begin
  rw [finsum_in_eq_finite_to_finset_sum _ hs, finsum_in_eq_finite_to_finset_sum _ ht],
  conv_lhs { congr, skip, funext, rw finsum_in_eq_finite_to_finset_sum _ ht },
  conv_rhs { congr, skip, funext, rw finsum_in_eq_finite_to_finset_sum _ hs },
  exact finset.sum_comm,
end

/-- Given a proposition `p` such that for all `x ∈ s, f x ≠ 0 → p x`, the sum on the elements of `s`
  satisfied by `p` equals the sum on `s`. -/
lemma finsum_in_inter_of_ne {p : α → Prop} (hp : ∀ x ∈ s, f x ≠ 0 → p x) :
  ∑ᶠ i in (s ∩ p), f i = ∑ᶠ i in s, f i :=
finsum_in_eq_finsum_in_of_subset'' (set.inter_subset_left _ _)
  (λ _ ⟨hsx, hfx⟩, ⟨hsx, hp _ hsx $ function.mem_support.1 hfx⟩)

/-- Given a proposition `p`, the sum on the elements of `s` satisfied by `p` over `f` equals the sum
  on `s` over the function `λ i, if p i then f i else 0`. -/
lemma finsum_in_inter (p : α → Prop) :
  ∑ᶠ i in (s ∩ p), f i = ∑ᶠ i in s, if p i then f i else 0 :=
begin
  rw ← @finsum_in_inter_of_ne _ _ _ (λ a, if p a then f a else 0) _ p,
  refine finsum_in_congr rfl (λ x ⟨hsx, hxp⟩, (if_pos hxp).symm),
  finish
end .

lemma finsum_in_inter' (p : α → Prop) :
  ∑ᶠ i in (s ∩ p), f i = ∑ᶠ i in s, if p i then f i else 0 :=
finsum_in_inter p

/-- The sum on any set over the zero function equals zero. -/
lemma finsum_in_const_zero (s : set α) : ∑ᶠ i in s, (0 : M) = 0 :=
begin
  rw [finsum_in_def, finsum_def, dif_pos],
    { simp },
    { convert set.finite_empty, ext,
      rw function.mem_support, finish }
end

/-- The sum on the set `s` over the function `f` equals zero if for all `x ∈ s, f x = 0`. -/
lemma finsum_in_const_zero_fun (hf : ∀ x ∈ s, f x = 0) : ∑ᶠ i in s, f i = 0 :=
by { rw ← finsum_in_const_zero s, exact finsum_in_congr rfl hf }

/-- If the sum on `s` over the function `f` is nonzero, then there is some `x ∈ s, f x ≠ 0`. -/
lemma exists_ne_zero_of_finsum_in_ne_zero
  (h : ∑ᶠ i in s, f i ≠ 0) : ∃ x ∈ s, f x ≠ 0 :=
begin
  by_contra h', push_neg at h',
  exact h (finsum_in_const_zero_fun h')
end

/-- To prove a property of a sum, it suffices to prove that the property is additive and holds on
  summands. -/
lemma finsum_in_induction (p : M → Prop) (hp₀ : p 0)
  (hp₁ : ∀ x y, p x → p y → p (x + y)) (hp₂ : ∀ x ∈ s, p $ f x) :
  p (∑ᶠ i in s, f i) :=
begin
  by_cases hs : (s ∩ support f).finite,
    { rw [finsum_in_inter_support, finsum_in_eq_finite_to_finset_sum _ hs, set.finite.to_finset],
      refine finset.sum_induction _ p hp₁ hp₀ (λ x hx, hp₂ x _),
      rw set.mem_to_finset at hx, exact hx.1 },
    { exact (finsum_in_eq_zero_of_infinite hs).symm ▸ hp₀ }
end

end finsum
