/-
Copyright (c) 2020 Kexing Ying and Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Kevin Buzzard
-/

import data.finsupp

/-!
# Finite sums over types and sets

We define sums over types and subsets of types, with no finiteness hypotheses. All infinite
sums are defined to be junk values (i.e. zero). This approach is sometimes easier to use
than `finset.sum` when issues arise with `finset` and `fintype` being data.

## Main definitions

Variables:`

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

/-! # noncomputable finite sums -/

section finsum

variables {α : Type u} {M : Type v} [add_comm_monoid M]

/-- Sum of `f x` as `x` ranges over the elements of the support of `f`, if it's finite. Zero
  otherwise. -/
noncomputable def finsum (f : α → M) : M :=
(function.support f).to_finset'.sum f

/-- Sum of `f x` for `x ∈ s`, if `s ∩ f.support` is finite. Zero if it's infinite.  -/
noncomputable def finsum_in (s : set α) (f : α → M) : M :=
finsum $ s.indicator f

localized "notation `∑ᶠ` binders `, ` r:(scoped:67 f, finsum f) := r"
  in big_operators

localized "notation `∑ᶠ` binders ` in ` s `, ` r:(scoped:67 f, finsum_in s f) := r"
  in big_operators

open_locale big_operators

lemma finsum_def (f : α → M) :
  ∑ᶠ i : α, f i = if h : (function.support f).finite then finset.sum (h.to_finset) f else 0 :=
begin
  split_ifs,
  { unfold finsum set.to_finset',
    rw dif_pos h },
  { unfold finsum,
    convert finset.sum_empty,
    exact dif_neg h }
end

lemma finsum_in_def (s : set α) (f : α → M) :
  ∑ᶠ i in s, f i = finsum (λ x, if x ∈ s then f x else 0) := rfl

namespace finsupp

variables {β : Type v} [has_zero β]

lemma support_finite (f : α →₀ β) : (function.support f).finite :=
by { rw fun_support_eq, exact f.support.finite_to_set }

/-- The natural `finsupp` induced by the function `f` given that it has finite support. -/
noncomputable def of_support_finite
  (f : α → β) (hf : (function.support f).finite) : α →₀ β :=
{ support := hf.to_finset,
  to_fun := f,
  mem_support_to_fun := λ _, hf.mem_to_finset }

lemma of_support_finite_def {f : α → β} {hf : (function.support f).finite} :
  (of_support_finite f hf : α → β) = f := rfl

end finsupp

lemma finsum_eq_finsupp_sum (f : α →₀ M) : ∑ᶠ i : α, f i = finsupp.sum f (λ x m, m) :=
begin
  rw [finsum_def, dif_pos (finsupp.support_finite f)],
  congr',
  simp
end

lemma finsum_eq_finsupp_sum' (f : α → M) (hf : (function.support f).finite) :
  ∑ᶠ i : α, f i = finsupp.sum (finsupp.of_support_finite f hf) (λ x m, m) :=
by rw [← finsum_eq_finsupp_sum, finsupp.of_support_finite_def]

lemma finsum_eq_finset_sum (f : α → M) (hf : (function.support f).finite) :
  ∑ᶠ i : α, f i = finset.sum hf.to_finset f :=
by rw [finsum_def, dif_pos hf]

lemma finsum_eq_finset_sum_of_fintype [fintype α] (f : α → M) :
  ∑ᶠ i : α, f i = (finset.univ' α).sum f :=
begin
  rw [finsum_def, dif_pos (set.finite.of_fintype (_ : set α))],
  refine finset.sum_subset (λ _ _, finset.mem_univ' _) (λ _ _ hx, _),
    rw set.finite.mem_to_finset at hx,
    exact function.nmem_support.1 (λ h, hx h),
end

lemma finsum_eq_finsupp_sum_of_ne_zero_mem_finset (f : α → M)
  {s : finset α} (hs : ∀ x, f x ≠ 0 → x ∈ s) : ∑ᶠ i : α, f i = s.sum f :=
begin
  rw finsum_eq_finset_sum,
  { apply finset.sum_subset,
    { intros x hx,
      rw set.finite.mem_to_finset at hx,
      exact hs _ hx },
    { intros x _ hx,
      rw set.finite.mem_to_finset at hx,
      exact not_not.1 hx } },
  { exact set.finite.subset (finset.finite_to_set s) (λ x hx, hs _ hx) }
end

lemma finsum_in_eq_finset_sum (f : α → M) {s : set α}
  (hf : (s ∩ function.support f).finite) :
  ∑ᶠ i in s, f i = ∑ i in hf.to_finset, f i :=
begin
  rw [finsum_in_def, finsum_eq_finset_sum],
  { apply finset.sum_congr,
    { ext,
      rw [set.finite.mem_to_finset, set.finite.mem_to_finset, set.mem_inter_iff,
          function.mem_support, function.mem_support],
      split,
      { split_ifs,
        { exact and.intro h },
        { intro h2, exact false.elim (h2 rfl) } },
      { rintro ⟨h1, h2⟩, rwa if_pos h1 } },
    { intros x hx,
      rw set.finite.mem_to_finset at hx,
      exact if_pos hx.1 } },
  { refine set.finite.subset hf (λ x hx, set.mem_inter _ _),
    { rw function.mem_support at hx,
      exact set.mem_of_indicator_ne_zero hx },
    { change x ∈ function.support (s.indicator f) at hx,
      rw set.support_indicator at hx,
      exact hx.2 } },
end

lemma finsum_in_eq_sum_filter (f : α → M) (s : set α)
  (hf : (function.support f).finite) :
  ∑ᶠ i in s, f i = (finset.filter (∈ s) hf.to_finset).sum f :=
begin
  rw finsum_in_eq_finset_sum f (set.finite.subset hf (set.inter_subset_right _ _)),
  congr, ext, finish
end

lemma finsum_in_eq_to_finset_sum [fintype α] (f : α → M) (s : set α):
  ∑ᶠ i in s, f i = ∑ i in s.to_finset, f i :=
begin
  rw finsum_in_eq_sum_filter f s (set.finite.of_fintype _),
  conv_rhs { rw ← finset.sum_filter_ne_zero },
  exact finset.sum_congr (by ext; finish) (λ _ _, rfl),
end

lemma finsum_in_eq_finite_to_finset_sum (f : α → M) {s : set α} (hs : s.finite) :
  ∑ᶠ i in s, f i = ∑ i in hs.to_finset, f i :=
begin
  rw finsum_in_eq_finset_sum f (set.finite.subset hs (set.inter_subset_left _ _)),
  conv_rhs { rw ← finset.sum_filter_ne_zero },
  refine finset.sum_congr _ (λ _ _, rfl),
  ext, rw [set.finite.to_finset, set.finite.to_finset, finset.mem_filter, set.mem_to_finset,
           set.mem_to_finset, set.mem_inter_iff, function.mem_support]
end

lemma finsum_in_coe_eq_sum (f : α → M) (s : finset α) :
  ∑ᶠ i in ↑s, f i = ∑ i in s, f i :=
begin
  rw [finsum_in_eq_finite_to_finset_sum f (finset.finite_to_set s), set.finite.to_finset],
  congr, ext, simp
end

lemma finsum_in_eq_zero_of_infinite {f : α → M} {s : set α}
  (hs : ¬ (s ∩ function.support f).finite) : ∑ᶠ i in s, f i = 0 :=
begin
  rw [finsum_in_def, finsum_def, dif_neg],
  intro h,
  apply hs,
  convert h,
  exact set.support_indicator.symm,
end

lemma finsum_in_inter_support (f : α → M) (s : set α) :
  ∑ᶠ i in s, f i = ∑ᶠ i in (s ∩ function.support f), f i :=
begin
  rw [finsum_in_def, finsum_in_def],
  congr', ext x, split_ifs with h h1 h2,
  { refl },
  { rw ←function.nmem_support, exact λ h2, h1 ⟨h, h2⟩ },
  { exact false.elim (h h2.1) },
  { refl }
end

lemma finsum_in_inter_support_eq (f : α → M) (s t : set α)
  (h : s ∩ function.support f = t ∩ function.support f) :
  ∑ᶠ i in s, f i = ∑ᶠ i in t, f i :=
by rw [finsum_in_inter_support, h, ← finsum_in_inter_support]

example (p q r : Prop) : (p → (q ↔ r)) → (p ∧ q ↔ p ∧ r) := and_congr_right

lemma finsum_in_inter_support_eq' (f : α → M) (s t : set α)
  (h : ∀ x ∈ function.support f, x ∈ s ↔ x ∈ t) :
  ∑ᶠ i in s, f i = ∑ᶠ i in t, f i :=
begin
  apply finsum_in_inter_support_eq,
  ext x,
  simpa [and_congr_right (h x)] using h x,
end

lemma finsum_eq_finsum_in_univ (f : α → M) : ∑ᶠ i in set.univ, f i = ∑ᶠ i : α, f i :=
by { rw finsum_in_def, congr, funext, rw if_pos (set.mem_univ _) }

variables {β : Type w} {f g : α → M} {a b : α} {s t : set α}

@[congr]
lemma finsum_in_congr (h₀ : s = t) (h₁ : ∀ x ∈ t, f x = g x) : finsum_in s f = finsum_in t g :=
h₀ ▸ by { rw [finsum_in_def, finsum_in_def], congr', ext x, split_ifs; finish }

/-- The sum on an empty set over any function is zero. -/
@[simp] lemma finsum_in_empty : ∑ᶠ i in ∅, f i = 0 :=
begin
  rw [finsum_in_eq_finite_to_finset_sum _ (set.finite_empty), ← @finset.sum_empty _ _ _ f],
  congr, ext, simp
end

/-- A set `s` is not empty if the sum on `s` is not equal to zero. -/
lemma nonempty_of_finsum_in_ne_zero (h : ∑ᶠ i in s, f i ≠ 0) : s ≠ ∅ :=
λ h', h $ h'.symm ▸ finsum_in_empty

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

/-- A more general version of `finsum_in_insert` that requires `s ∩ function.support f` instead of
  `s` to be finite. -/
@[simp] lemma finsum_in_insert' (f : α → M) (h : a ∉ s) (hs : (s ∩ function.support f).finite) :
  ∑ᶠ i in insert a s, f i = f a + ∑ᶠ i in s, f i :=
begin
  by_cases ha : a ∈ function.support f,
    { have := finsum_in_insert f
        (show a ∉ s ∩ function.support f, by exact λ h', h h'.1) hs,
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
  by_cases hs : ((s ∩ function.support f).finite),
    { by_cases hm : a ∈ s,
        { simp_rw set.insert_eq_of_mem hm },
        { rw [finsum_in_insert' f hm hs, h hm, zero_add] } },
    { rw [finsum_in_eq_zero_of_infinite hs, finsum_in_eq_zero_of_infinite],
      intro hs', apply hs,
      by_cases hm : a ∈ function.support f,
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
  by_cases hs : (g '' s ∩ function.support f).finite,
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

/-- A more general version of `finsum_in_union_inter` that requires `s ∩ function.support f` and
  `t ∩ function.support f` instead of `s` and `t` to be finite. -/
lemma finsum_in_union_inter'
  (hs : (s ∩ function.support f).finite) (ht : (t ∩ function.support f).finite) :
  ∑ᶠ i in (s ∪ t), f i + ∑ᶠ i in (s ∩ t), f i = ∑ᶠ i in s, f i + ∑ᶠ i in t, f i :=
begin
  rw [finsum_in_inter_support f s, finsum_in_inter_support f t,
      finsum_in_inter_support f (s ∪ t), finsum_in_inter_support f (s ∩ t),
      ← finsum_in_union_inter hs ht, set.inter_distrib_right],
  conv_rhs { congr, skip, congr,
    rw [set.inter_assoc, ← set.inter_assoc _ t, set.inter_comm _ t,
        set.inter_assoc, set.inter_self, ← set.inter_assoc] }
end

/-- Given two finite disjoint sets `s` and `t`, the sum on `s ∪ t` over the function `f` equals the
  sum on `s` over `f` plus the sum on `t` over `f`. -/
lemma finsum_in_union (hs : s.finite) (ht : t.finite) (hst : disjoint s t) :
  ∑ᶠ i in (s ∪ t), f i = ∑ᶠ i in s, f i + ∑ᶠ i in t, f i :=
by rw [← finsum_in_union_inter hs ht,
       show s ∩ t = ∅, by exact disjoint_iff.1 hst, finsum_in_empty, add_zero]

/-- A more general version of `finsum_in_union` that requires `s ∩ function.support f` and
  `t ∩ function.support f` instead of `s` and `t` to be finite. -/
lemma finsum_in_union'
  (hs : (s ∩ function.support f).finite) (ht : (t ∩ function.support f).finite)
  (hst : disjoint s t) : ∑ᶠ i in (s ∪ t), f i = ∑ᶠ i in s, f i + ∑ᶠ i in t, f i :=
by rw [← finsum_in_union_inter' hs ht,
       show s ∩ t = ∅, by exact disjoint_iff.1 hst, finsum_in_empty, add_zero]

/-- Given a finite set `t` and a subset `s` of `t`, the sum on `s` over the function `f` plus the
  sum on `t \ s` over `f` equals the sum on `t` over `f`. -/
lemma finsum_in_sdiff (ht : t.finite) (hst : s ⊆ t) :
  ∑ᶠ i in s, f i + ∑ᶠ i in t \ s, f i = ∑ᶠ i in t, f i :=
begin
  conv_rhs { rw ← set.union_diff_cancel hst },
  exact (finsum_in_union (set.finite.subset ht hst)
    (set.finite.subset ht $ set.diff_subset t s) set.disjoint_diff).symm
end

/-- A more general version of `finsum_in_sdiff` that requires `t ∩ function.support f` instead of
  `t` to be finite. -/
lemma finsum_in_sdiff' (ht : (t ∩ function.support f).finite)
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

/-- Given a set `t` thats smaller than `s` but greater than `s ∩ function.support f`, the sum on `t`
  equals the sum on `s`. -/
lemma finsum_in_eq_finsum_in_of_subset''
  (ht₀ : t ⊆ s) (ht₁ : s ∩ function.support f ⊆ t) :
  ∑ᶠ i in t, f i = ∑ᶠ i in s, f i :=
begin
  refine finsum_in_eq_finsum_in_of_subset' ht₀ (λ _ hx₀ hx₁, _),
  rw ← function.nmem_support,
  exact λ hx₂, hx₁ (ht₁ ⟨hx₀, hx₂⟩)
end

/-- Given a finite set `s`, the sum on `s` over `f + g` equals the sum over `f` plus the sum over
  `g`. -/
lemma finsum_in_add_distrib (hs : s.finite) :
  ∑ᶠ i in s, (f i + g i) = ∑ᶠ i in s, f i + ∑ᶠ i in s, g i :=
by iterate 3 { rw [finsum_in_eq_finite_to_finset_sum _ hs, set.finite.to_finset] };
  exact finset.sum_add_distrib

/-- A more general version of `finsum_in_distrib` that requires `s ∩ function.support f` and
  `s ∩ function.support g` instead of `s` to be finite. -/
lemma finsum_in_add_distrib'
  (hf : (s ∩ function.support f).finite) (hg : (s ∩ function.support g).finite) :
  ∑ᶠ i in s, (f i + g i) = ∑ᶠ i in s, f i + ∑ᶠ i in s, g i :=
begin
  convert @finset.sum_add_distrib _ _ ((hf.to_finset ∪ hg.to_finset).filter s) f g _,
  { rw [←finsum_in_coe_eq_sum, finsum_in_inter_support],
    refine finsum_in_eq_finsum_in_of_subset _ _,
    { rintros x ⟨hx₁, hx₂⟩,
      rw [finset.mem_coe, finset.mem_filter],
      refine ⟨_, hx₁⟩,
      by_cases hf : f x = 0,
      { rw [function.mem_support, hf, zero_add] at hx₂,
        apply finset.subset_union_right,
        rw set.finite.mem_to_finset,
        exact ⟨hx₁, hx₂⟩ },
      { apply finset.subset_union_left,
        rw set.finite.mem_to_finset,
        exact ⟨hx₁, hf⟩ } },
    { rintros x ⟨hxs, hx⟩,
      rw [finset.mem_coe, finset.mem_filter] at hxs,
      by_contra hfg, exact hx ⟨hxs.2, hfg⟩ } },
  all_goals { rw [← finsum_in_coe_eq_sum, finsum_in_inter_support],
              apply finsum_in_eq_finsum_in_of_subset },
  { rintro x ⟨hxs, hxf⟩,
    apply finset.mem_filter.2,
    rw finset.mem_union,
    refine ⟨or.inl _, hxs⟩,
    rw set.finite.mem_to_finset,
    exact ⟨hxs, hxf⟩ },
  { intro x,
    rw set.mem_diff,
    rintro ⟨hx, hnx⟩,
    rw ← function.nmem_support,
    intro hxf,
    exact hnx ⟨(finset.mem_filter.1 hx).2, hxf⟩ },
  { rintro x ⟨hxs, hxg⟩,
    apply finset.mem_filter.2,
    rw finset.mem_union,
    refine ⟨or.inr _, hxs⟩,
    rw set.finite.mem_to_finset,
    exact ⟨hxs, hxg⟩ },
  { intro x,
    rw set.mem_diff,
    rintro ⟨hx, hnx⟩,
    rw ← function.nmem_support,
    intro hxg,
    exact hnx ⟨(finset.mem_filter.1 hx).2, hxg⟩ },
end

/-- Given the support of `f` and `g` are finite, the sum over `f + g` equals the sum over `f` plus
  the sum over `g`. -/
lemma finsum_add_distrib
  (hf : (function.support f).finite) (hg : (function.support g).finite) :
  ∑ᶠ i, (f + g) i = ∑ᶠ i, f i + ∑ᶠ i, g i :=
begin
  rw [← finsum_eq_finsum_in_univ, ← finsum_eq_finsum_in_univ, ← finsum_eq_finsum_in_univ],
  apply finsum_in_add_distrib',
  { convert hf, simp },
  { convert hg, simp }
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

/-- Given a monoid homomorphism `g : β → M`, and a function `f : α → β`, the sum on `s` over `g ∘ f`
  equals `g` of the sum on `s` over `f`. -/
lemma finsum_in_hom [add_comm_monoid β] (f : α → β) (g : β →+ M) (hs : s.finite) :
  ∑ᶠ i in s, (g ∘ f) i = g (∑ᶠ j in s, f j) :=
by rw [finsum_in_eq_finite_to_finset_sum _ hs, finsum_in_eq_finite_to_finset_sum _ hs,
       set.finite.to_finset, add_monoid_hom.map_sum]

lemma finsum_in_hom'' [add_comm_monoid β] (f : α → β) (g : β →+ M) (hs : s.finite) :
  ∑ᶠ i in s, g (f i) = g (∑ᶠ j in s, f j) :=
finsum_in_hom f g hs

/-- A more general version of `finsum_in_hom` that requires `s ∩ function.support f` and instead of
  `s` to be finite. -/
lemma finsum_in_hom' [add_comm_monoid β] {f : α → β} (g : β →+ M)
  (h₀ : (s ∩ function.support f).finite) :
  ∑ᶠ i in s, (g (f i)) = g (∑ᶠ j in s, f j) :=
begin
  rw [finsum_in_inter_support f, ← finsum_in_hom _ _ h₀],
  symmetry,
  refine finsum_in_eq_finsum_in_of_subset'' (set.inter_subset_left _ _)
    (set.inter_subset_inter_right _ (λ x hgx, _)),
  rw function.mem_support at hgx ⊢,
  intro hfx, refine hgx _, simp only [hfx, function.comp],
  exact add_monoid_hom.map_zero g
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
  by_cases hs : (s ∩ function.support f).finite,
    { rw [finsum_in_inter_support, finsum_in_eq_finite_to_finset_sum _ hs, set.finite.to_finset],
      refine finset.sum_induction _ p hp₁ hp₀ (λ x hx, hp₂ x _),
      rw set.mem_to_finset at hx, exact hx.1 },
    { exact (finsum_in_eq_zero_of_infinite hs).symm ▸ hp₀ }
end

end finsum
