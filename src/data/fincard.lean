/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Kexing Ying
-/

import data.set.finite
import algebra.big_operators
import data.support
import data.finsupp

/-!
# Noncomputable finiteness

This file contains various noncomputable definitions of finiteness, which hopefully
avoid issues that people who want to reason about finite types run into when
they end up with two non-defeq terms of type `fintype α`. Definitions are noncomputable
and hence cannot be `#eval`'ed, but are still perfectly fine for theorems such
as Sylow's theorems.

## Main definitions

Variables:`

`(α : Type u)`
`(s : set α)`
`(M : Type v) [add_comm_monoid M]`
`(f : α → M)`

Definitions in this file:

* `univ' α : finset α` : α as a finset if α is finite, and the empty finset otherwise

* `finsum f : M` : the sum of `f x` as `x` ranges over the support of `f`, if it's finite.
   Zero otherwise.

* `finsum_in s f : M` : the sum of `f x` as `x` ranges over the elements of `s` for which `f x ≠ 0`,
  if this is a finite sum. Zero otherwise.

* `fincard α : ℕ` is the size of α if it's finite, and 0 otherwise

## Implementation notes

TODO

## Tags

finsum, finsum_in, fincard, univ', finiteness
-/

open_locale classical

universes u v w

/-! # finset.univ' -- noncomputable univ (empty set if infinite) -/

namespace finset

/-- `univ' α` is the finset corresponding to all of α if α is finite, and the empty set otherwise.
Note that it is noncomputable -/
noncomputable def univ' (α : Type u) : finset α :=
if h : nonempty (fintype α) then (classical.choice h).elems else ∅

/-- `set.to_finset s` is the finset corresponding to `s` if `s` is finite, and the empty set
    otherwise -/
noncomputable def set.to_finset {α : Type u} (s : set α) : finset α :=
if h : s.finite then h.to_finset else ∅

variable {α : Type u}

/-- `univ' α` is finset.univ if `α` is a fintype. -/
lemma univ'_eq_univ [h : fintype α] : univ' α = univ :=
by convert (dif_pos (nonempty.intro h))

lemma univ'_eq_empty (h : ¬ nonempty (fintype α)) : univ' α = ∅ :=
dif_neg h

@[simp] lemma mem_univ' [h : fintype α] (x : α) : x ∈ univ' α :=
(@univ'_eq_univ _ h).symm ▸ mem_univ _

end finset

/-! # noncomputable finite sums -/

section finsum

variables {α : Type u} {M : Type v} [add_comm_monoid M]

/-- Sum of `f x` as `x` ranges over the elements of the support of `f`, if it's finite. Zero
  otherwise. -/
noncomputable def finsum (f : α → M) : M :=
if h : (function.support f).finite then finset.sum (h.to_finset) f else 0

/-- Sum of `f x` for `x ∈ s`, if `s ∩ f.support` is finite. Zero if it's infinite.  -/
noncomputable def finsum_in (s : set α) (f : α → M) : M :=
finsum (λ x, if x ∈ s then f x else 0)

lemma finsum_def (f : α → M) :
  finsum f = if h : (function.support f).finite then finset.sum (h.to_finset) f else 0 := rfl

lemma finsum_in_def (s : set α) (f : α → M) :
  finsum_in s f = finsum (λ x, if x ∈ s then f x else 0) := rfl

-- **TODO** function.support doesn't import data.finsupp and vice versa
-- so this lemma can't go in either place
lemma function.support_eq_support {α : Type u} {β : Type v} [has_zero β] (f : α →₀ β) :
  function.support f = ↑(f.support) :=
set.ext $ λ x, finsupp.mem_support_iff.symm

namespace finsupp

variables {β : Type v} [has_zero β]

lemma support_finite (f : α →₀ β) : (function.support f).finite :=
by { rw function.support_eq_support, exact f.support.finite_to_set }

@[simp] lemma support_finite.to_finset (f : α →₀ β) : (support_finite f).to_finset = f.support :=
finset.ext $ λ x, by {simp, refl}

/-- The natural `finsupp` induced by the function `f` given it has finite support. -/
noncomputable def of_support_finite
  {f : α → β} (hf : (function.support f).finite) : α →₀ β :=
{ support := hf.to_finset,
  to_fun := f,
  mem_support_to_fun := λ _, set.finite.mem_to_finset }

lemma of_support_finite_def {f : α → β} {hf : (function.support f).finite} :
  (of_support_finite hf : α → β) = f := rfl

end finsupp

lemma finsum_eq_finsupp_sum (f : α →₀ M) : finsum f = finsupp.sum f (λ x m, m) :=
begin
  rw [finsum_def, dif_pos (finsupp.support_finite f)],
  congr',
  simp
end

lemma finsum_eq_finsupp_sum' (f : α → M) (hf : (function.support f).finite) :
  finsum f = finsupp.sum (finsupp.of_support_finite hf) (λ x m, m) :=
by rw [← finsum_eq_finsupp_sum, finsupp.of_support_finite_def]

lemma finsum_eq_finset_sum (f : α → M) (hf : (function.support f).finite) :
  finsum f = finset.sum hf.to_finset f :=
by rw [finsum_def, dif_pos hf]

lemma finsum_eq_finset_sum' [fintype α] (f : α → M) :
  finsum f = (finset.univ' α).sum f :=
begin
  rw [finsum_def, dif_pos (set.finite.of_fintype (_ : set α))],
  refine finset.sum_subset (λ _ _, finset.mem_univ' _) (λ _ _ hx, _),
    rw set.finite.mem_to_finset at hx,
    exact function.nmem_support.1 (λ h, hx h),
end

lemma finsum_in_eq_finset_sum (f : α → M) {s : set α}
  (hf : (s ∩ function.support f).finite) :
  finsum_in s f = hf.to_finset.sum f :=
begin
  rw [finsum_in_def, finsum_eq_finset_sum],
    { apply finset.sum_congr,
      { ext, rw [set.finite.mem_to_finset, set.finite.mem_to_finset, set.mem_inter_iff,
                 function.mem_support, function.mem_support],
        split; finish },
      { finish } },
    { refine set.finite.subset hf (λ x hx, set.mem_inter _ _);
      rw function.mem_support at hx; finish }
end .

lemma finsum_in_eq_finset_sum' (f : α → M) (s : set α)
  (hf : (function.support f).finite) :
  finsum_in s f = (finset.filter (∈ s) hf.to_finset).sum f :=
begin
  rw finsum_in_eq_finset_sum f (set.finite.subset hf (set.inter_subset_right _ _)),
  congr, ext, finish
end

lemma finsum_in_eq_finset_sum'' [fintype α] (f : α → M) (s : set α):
  finsum_in s f = s.to_finset.sum f :=
begin
  rw finsum_in_eq_finset_sum' f s (set.finite.of_fintype _),
  conv_rhs { rw ← finset.sum_filter_ne_zero },
  exact finset.sum_congr (by ext; finish) (λ _ _, rfl),
end

lemma finsum_in_eq_finset_sum''' (f : α → M) {s : set α} (hs : s.finite) :
  finsum_in s f = hs.to_finset.sum f :=
begin
  rw finsum_in_eq_finset_sum f (set.finite.subset hs (set.inter_subset_left _ _)),
  conv_rhs { rw ← finset.sum_filter_ne_zero },
  refine finset.sum_congr _ (λ _ _, rfl),
  ext, rw [set.finite.to_finset, set.finite.to_finset, finset.mem_filter, set.mem_to_finset,
           set.mem_to_finset, set.mem_inter_iff, function.mem_support]
end

lemma finsum_in_eq_finset_sum'''' (f : α → M) (s : finset α) :
  finsum_in ↑s f = s.sum f :=
begin
  rw [finsum_in_eq_finset_sum''' f (finset.finite_to_set s), set.finite.to_finset],
  congr, ext, simp
end

lemma finsum_in_eq_zero_of_nfinite {f : α → M} {s : set α}
  (hs : ¬ (s ∩ function.support f).finite) : finsum_in s f = 0 :=
begin
  rw [finsum_in_def, finsum_def, dif_neg],
  intro h,
  apply hs,
  convert h,
  ext,  rw function.mem_support, split,
    { rintro ⟨hsx, hfx⟩,
      rw function.mem_support at hfx,
      rwa if_pos hsx },
    { split_ifs; finish }
end .

lemma finsum_in_inter_support (f : α → M) (s : set α) :
  finsum_in s f = finsum_in (s ∩ function.support f) f :=
begin
  rw [finsum_in_def, finsum_in_def],
  congr', ext x, split_ifs,
  { refl },
  { rw ←function.nmem_support, finish },
  { finish },
  { refl }
end .

lemma finsum_eq_finsum_in_univ (f : α → M) : finsum f = finsum_in set.univ f :=
by { rw finsum_in_def, congr, funext, rw if_pos (set.mem_univ _) }

variables {β : Type w} {f g : α → M} {a b : α} {s t : set α}

@[congr]
lemma finsum_in_congr (h₀ : s = t) (h₁ : ∀ x ∈ t, f x = g x) : finsum_in s f = finsum_in t g :=
h₀ ▸ by { rw [finsum_in_def, finsum_in_def], congr', ext x, split_ifs; finish }

/-- The sum on an empty set over any function is zero. -/
@[simp] lemma finsum_in_empty : finsum_in ∅ f = 0 :=
begin
  rw [finsum_in_eq_finset_sum''' _ (set.finite_empty), ← @finset.sum_empty _ _ _ f],
  congr, ext, simp
end

/-- Given `a` and element not in the set `s`, the sum on `insert a s` over the function `f` equals
  the `f a` plus the sum on `s` over `f`. -/
@[simp] lemma finsum_in_insert (f : α → M) (h : a ∉ s) (hs : s.finite) :
  finsum_in (insert a s) f = f a + finsum_in s f :=
begin
  rw [finsum_in_eq_finset_sum''' f (set.finite.insert a hs), finsum_in_eq_finset_sum''' f hs,
      set.finite.to_finset, set.finite.to_finset, ← finset.sum_insert],
    { congr, ext, simp },
    { rw set.mem_to_finset, exact h }
end

-- ↓ these two lemmas should go in data.set.basic probably
lemma set.insert_inter_of_mem {s₁ s₂ : set α} {a : α} (h : a ∈ s₂) :
  insert a s₁ ∩ s₂ = insert a (s₁ ∩ s₂) :=
by { ext, split; finish }

lemma set.insert_inter_of_not_mem {s₁ s₂ : set α} {a : α} (h : a ∉ s₂) :
  insert a s₁ ∩ s₂ = s₁ ∩ s₂ :=
by { ext, split; finish }

/-- A more general version of `finsum_in_insert` that requires `s ∩ function.support f` instead of
  `s` to be finite. -/
@[simp] lemma finsum_in_insert' (f : α → M) (h : a ∉ s) (hs : (s ∩ function.support f).finite) :
  finsum_in (insert a s) f = f a + finsum_in s f :=
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

/-- A more general version of `finsum_in_insert_of_eq_zero_if_not_mem` that requires
  `s ∩ function.support f` instead of `s` to be finite. -/
lemma finsum_in_insert_of_eq_zero_if_not_mem' (h : a ∉ s → f a = 0) :
  finsum_in (insert a s) f = finsum_in s f :=
begin
  by_cases hs : ((s ∩ function.support f).finite),
    { by_cases hm : a ∈ s,
        { simp_rw set.insert_eq_of_mem hm },
        { rw [finsum_in_insert' f hm hs, h hm, zero_add] } },
    { rw [finsum_in_eq_zero_of_nfinite hs, finsum_in_eq_zero_of_nfinite],
      intro hs', apply hs,
      by_cases hm : a ∈ function.support f,
        { apply set.finite.subset hs',
          finish },
        { rwa set.insert_inter_of_not_mem hm at hs' } }
end

/-- If `f a = 0` for all `a ∉ s`, then the sum on `insert a s` over the function `f` equals the sum
  on `s` over `f`. -/
lemma finsum_in_insert_of_eq_zero_if_not_mem (h : a ∉ s → f a = 0) :
  finsum_in (insert a s) f = finsum_in s f :=
finsum_in_insert_of_eq_zero_if_not_mem' h

/-- If `f a = 0`, then the sum on `insert a s` over the function `f` equals the sum on `s` over `f`.
  -/
@[simp] lemma finsum_insert_zero (h : f a = 0) :
  finsum_in (insert a s) f = finsum_in s f :=
finsum_in_insert_of_eq_zero_if_not_mem (λ _, h)

/-- The sum on a singleton `{a}` over the function `f` is `f a`. -/
@[simp] lemma finsum_singleton : finsum_in {a} f = f a :=
begin
  rw [finsum_in_eq_finset_sum''' f (set.finite_singleton a), set.finite.to_finset,
      ← @finset.sum_singleton _ _ a f _],
  congr, ext, simp
end

/-- The sum on the set of two unique elements `{a, b}` over the function `f` equals `f a + f b`. -/
@[simp] lemma finsum_pair (h : a ≠ b) : finsum_in {a, b} f = f a + f b :=
begin
  rw [finsum_in_eq_finset_sum''' f (show set.finite {a, b}, by simp),
      set.finite.to_finset, ← finset.sum_pair h],
  congr, ext, simp
end

-- finsum_const_zero follows from finsum_const so we will prove it after finsum_const

/-- The sum on the image `g '' s` over the function `f` equals the sum on `s` over `f ∘ g` given `g`
  is injective on `s`. -/
@[simp] lemma finsum_in_image' {s : set β} {g : β → α} (hs : s.finite) (hg : set.inj_on g s) :
  finsum_in (g '' s) f = finsum_in s (f ∘ g) :=
begin
  rw [finsum_in_eq_finset_sum''' (f ∘ g) hs, finsum_in_eq_finset_sum''' f (set.finite.image g hs),
    ←finset.sum_image
    (λ x hx y hy hxy, hg (set.finite.mem_to_finset.1 hx) (set.finite.mem_to_finset.1 hy) hxy)],
  congr, ext, simp
end

lemma set.image_inter_support_eq {s : set β} {g : β → α} :
  (g '' s ∩ function.support f) = g '' (s ∩ function.support (f ∘ g)) :=
begin
  ext y, split; intro hy,
    { rcases hy with ⟨⟨x, hx₀, rfl⟩, hy⟩,
      exact ⟨x, ⟨hx₀, hy⟩, rfl⟩ },
    { finish }
end .

lemma set.image_inter_support_finite_iff {s : set β} {g : β → α} (hg : set.inj_on g s) :
  (g '' s ∩ function.support f).finite ↔ (s ∩ function.support (f ∘ g)).finite :=
begin
  rw [set.image_inter_support_eq, set.finite_image_iff],
  exact set.inj_on.mono (set.inter_subset_left s _) hg
end

/-- A more general version of `finsum_in_image'` that does not require `s` to be finite. -/
@[simp] lemma finsum_in_image {s : set β} {g : β → α}
  (hg : set.inj_on g s) : finsum_in (g '' s) f = finsum_in s (f ∘ g) :=
begin
  by_cases hs : (g '' s ∩ function.support f).finite,
    { rw [finsum_in_eq_finset_sum _ hs, finsum_in_eq_finset_sum _
            ((set.image_inter_support_finite_iff hg).1 hs),
        ← finsum_in_eq_finset_sum''', ← finsum_in_eq_finset_sum''',
        ← (@finsum_in_image' _ _ _ _ f (s ∩ function.support (f ∘ g)) g
            ((set.image_inter_support_finite_iff hg).1 hs)
          (set.inj_on.mono (set.inter_subset_left s _) hg))],
        { congr, ext y, refine ⟨_, by finish⟩,
          rintro ⟨⟨x, hx, rfl⟩, hy⟩,
          exact ⟨x, ⟨hx, hy⟩, rfl⟩ } },
    { rw [finsum_in_eq_zero_of_nfinite hs, finsum_in_eq_zero_of_nfinite],
      intro hs', apply hs,
      rwa set.image_inter_support_finite_iff hg }
end .

/-- The sum on `s : set α` over `f : α → M` equals the sum on `t : set β` over `g : β → M` if there
  exists some function `e : α → β` that is bijective on `s` to `t` such that for all `x` in `s`,
  `f x = (g ∘ e) x`. -/
lemma finsum_in_eq_of_bij_on {s : set α} {t : set β} {f : α → M} {g : β → M}
  (e : α → β) (he₀ : set.bij_on e s t) (he₁ : ∀ x ∈ s, f x = (g ∘ e) x) :
  finsum_in s f = finsum_in t g :=
begin
  rw [(set.bij_on.image_eq he₀).symm, finsum_in_image he₀.2.1],
  exact finsum_in_congr rfl he₁
end

/-- Given finite sets `s` and `t`, the sum on `s ∪ t` over the function `f` plus the sum on `s ∩ t`
  over `f` equals the sum on `s` over `f` plus the sum on `t` over `f`. -/
lemma finsum_in_union_inter (hs : s.finite) (ht : t.finite) :
  finsum_in (s ∪ t) f + finsum_in (s ∩ t) f = finsum_in s f + finsum_in t f :=
begin
  rw [finsum_in_eq_finset_sum''' f hs, finsum_in_eq_finset_sum''' f ht,
      finsum_in_eq_finset_sum''' f (set.finite.union hs ht),
      finsum_in_eq_finset_sum''' f (set.finite.subset hs (set.inter_subset_left _ _)),
      set.finite.to_finset],
  convert finset.sum_union_inter; { { ext, split; finish } <|> apply_instance }
end .

/-- A more general version of `finsum_in_union_inter` that requires `s ∩ function.support f` and
  `t ∩ function.support f` instead of `s` and `t` to be finite. -/
lemma finsum_in_union_inter'
  (hs : (s ∩ function.support f).finite) (ht : (t ∩ function.support f).finite) :
  finsum_in (s ∪ t) f + finsum_in (s ∩ t) f = finsum_in s f + finsum_in t f :=
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
  finsum_in (s ∪ t) f = finsum_in s f + finsum_in t f :=
by rw [← finsum_in_union_inter hs ht,
       show s ∩ t = ∅, by exact disjoint_iff.1 hst, finsum_in_empty, add_zero]

/-- A more general version of `finsum_in_union` that requires `s ∩ function.support f` and
  `t ∩ function.support f` instead of `s` and `t` to be finite. -/
lemma finsum_in_union'
  (hs : (s ∩ function.support f).finite) (ht : (t ∩ function.support f).finite)
  (hst : disjoint s t) : finsum_in (s ∪ t) f = finsum_in s f + finsum_in t f :=
by rw [← finsum_in_union_inter' hs ht,
       show s ∩ t = ∅, by exact disjoint_iff.1 hst, finsum_in_empty, add_zero]

/-- Given a finite set `t` and a subset `s` of `t`, the sum on `s` over the function `f` plus the
  sum on `t \ s` over `f` equals the sum on `t` over `f`. -/
lemma finsum_in_sdiff (ht : t.finite) (hst : s ⊆ t) :
  finsum_in s f + finsum_in (t \ s) f = finsum_in t f :=
begin
  conv_rhs { rw ← set.union_diff_cancel hst },
  exact (finsum_in_union (set.finite.subset ht hst)
    (set.finite.subset ht $ set.diff_subset t s) set.disjoint_diff).symm
end

/-- A more general version of `finsum_in_sdiff` that requires `t ∩ function.support f` instead of
  `t` to be finite. -/
lemma finsum_in_sdiff' (ht : (t ∩ function.support f).finite)
  (hst : s ⊆ t) : finsum_in s f + finsum_in (t \ s) f = finsum_in t f :=
begin
  conv_rhs { rw ← set.union_diff_cancel hst },
  exact (finsum_in_union' (set.finite.subset ht (set.inter_subset_inter_left _ hst))
    (set.finite.subset ht (set.inter_subset_inter (set.diff_subset t s) $ set.subset.refl _))
      set.disjoint_diff).symm
end

lemma finsum_in_bind {s : set β} {t : β → set α} (hs : s.finite)
  (ht : ∀ b, (t b).finite) -- I would like to change this to ∀ b ∈ s, (t b).finite
  (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → disjoint (t x) (t y)) :
  finsum_in (⋃ x ∈ s, t x) f = finsum_in s (λ x, finsum_in (t x) f) :=
begin
  rw finsum_in_eq_finset_sum''' _ hs,
  rw finsum_in_eq_finset_sum''' f (set.finite.bUnion hs (λ i _, ht i)),
  conv_rhs { congr, skip, funext, rw finsum_in_eq_finset_sum''' f (ht x) },
  convert @finset.sum_bind _ _ _ f _ _ hs.to_finset (λ x, (ht x).to_finset)
    (begin
      intros x hx y hy hxy a ha,
      specialize h x (set.finite.mem_to_finset.1 hx) y (set.finite.mem_to_finset.1 hy) hxy,
      apply @h a, simpa using ha
    end),
  ext, rw [finset.mem_bind, set.finite.mem_to_finset, set.mem_bUnion_iff],
  split; intro ha; rcases ha with ⟨x, hx₀, hx₁⟩,
    exact ⟨x, set.finite.mem_to_finset.2 hx₀, set.finite.mem_to_finset.2 hx₁⟩,
    exact ⟨x, set.finite.mem_to_finset.1 hx₀, set.finite.mem_to_finset.1 hx₁⟩
end .

lemma finsum_in_Union [fintype β] {t : β → set α}
  (ht : ∀ b, (t b).finite) (h : ∀ x y, x ≠ y → disjoint (t x) (t y)) :
  finsum_in (⋃ x : β, t x) f = finsum (λ x, finsum_in (t x) f) :=
begin
  rw finsum_eq_finsum_in_univ,
  rw ← finsum_in_bind (set.finite.of_fintype _) ht (λ x _ y _, h x y),
    { congr, funext y, simp only [set.Union_pos, set.mem_univ] },
end

-- -- ↓ probably a bad way of phrasing this
-- lemma finsum_in_bUnion {s : set β} {t : Π (x : β), x ∈ s → set α}
--   (hs : s.finite) (ht : ∀ b (hb : b ∈ s), (t b hb).finite)
--   (h : ∀ x (hx : x ∈ s), ∀ y (hy : y ∈ s), x ≠ y → disjoint (t x hx) (t y hy)) :
--   finsum_in (⋃ x (hx : x ∈ s), t x hx) f =
--   finsum_in s (λ x, if hx : x ∈ s then finsum_in (t x hx) f else 0) :=
-- begin
--   sorry
-- end

-- lemma finsum_in_sUnion {t : set (set α)} (ht₀ : t.finite)
--   (ht₁ : ∀ (x : set α) (hs : x ∈ t), x.finite)
--   (h : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → disjoint x y) :
--   finsum_in (⋃₀ t) f = finsum_in t (λ x, finsum_in x f) :=
-- by rw [set.sUnion_eq_bUnion, finsum_in_bUnion ht₀ ht₁ (by simpa)];
--   exact finsum_in_congr rfl (λ x hx, dif_pos hx)

-- lemma foo (p : set α → M) (hp : ∀ s : set α, p (s ∩ function.support f) = p s)
--   (h : ∀ s : set α, s.finite → finsum_in s f = p s)
--   (hs : (s ∩ function.support f).finite) : finsum_in s f = p s :=
-- by rw [← finsum_in_eq _ _ hs, h _ hs]; exact hp s

-- lemma set.inter_support_add_finite
--   (hf : (s ∩ function.support f).finite) (hg : (s ∩ function.support g).finite) :
--   (s ∩ function.support (λ x, f x + g x)).finite :=
-- set.finite.subset (by rw set.inter_distrib_left; exact set.finite.union hf hg)
--   (set.inter_subset_inter_right _ (function.support_add f g))

/-- Given a subset `t` of the set `s`, such that for all elements of `s` not in `t`, `f x = 0`, the
  sum on `t` over `f` equals the sum on `s` over `f`. -/
lemma finsum_in_eq_finsum_in_of_subset (hst : s ⊆ t)
  (hf : ∀ x : α, x ∈ t \ s → f x = 0) : finsum_in s f = finsum_in t f :=
begin
  rw [finsum_in_def, finsum_in_def],
  congr', ext x, split_ifs,
  { refl },
  { exact false.elim (h_1 $ hst h) },
  { exact (hf _ ⟨h_1, h⟩).symm },
  { refl }
end

lemma finsum_in_eq_finsum_in_of_subset'
  (ht₀ : t ⊆ s) (ht₁ : ∀ x ∈ s, x ∉ t → f x = 0) :
  finsum_in t f = finsum_in s f :=
by { refine finsum_in_eq_finsum_in_of_subset ht₀ _, finish }

/-- Given a set `t` thats smaller than `s` but greater than `s ∩ function.support f`, the sum on `t`
  equals the sum on `s`. -/
lemma finsum_in_eq_finsum_in_of_subset''
  (ht₀ : t ⊆ s) (ht₁ : s ∩ function.support f ⊆ t) :
  finsum_in t f = finsum_in s f :=
begin
  refine finsum_in_eq_finsum_in_of_subset' ht₀ (λ _ hx₀ hx₁, _),
  rw ← function.nmem_support,
  exact λ hx₂, hx₁ (ht₁ ⟨hx₀, hx₂⟩)
end

lemma finsum_in_add_distrib (hs : s.finite) :
  finsum_in s (λ x, f x + g x) = finsum_in s f + finsum_in s g :=
by iterate 3 { rw [finsum_in_eq_finset_sum''' _ hs, set.finite.to_finset] };
  exact finset.sum_add_distrib

lemma finsum_in_add_distrib'
  (hf : (s ∩ function.support f).finite) (hg : (s ∩ function.support g).finite) :
  finsum_in s (λ x, f x + g x) = finsum_in s f + finsum_in s g :=
begin
  convert @finset.sum_add_distrib _ _ ((hf.to_finset ∪ hg.to_finset).filter s) f g _,
  { rw [←finsum_in_eq_finset_sum'''', finsum_in_inter_support],
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
  all_goals { rw [← finsum_in_eq_finset_sum'''', finsum_in_inter_support],
              apply finsum_in_eq_finsum_in_of_subset;
              { intro x, finish } },
end .

-- this should be `f + g` not `λ x, f x + g x` but we probably need to import algebra.big_operators for this
lemma finsum_add_distrib
  (hf : (function.support f).finite) (hg : (function.support g).finite) :
  finsum (λ x, f x + g x) = finsum f + finsum g :=
begin
  rw [finsum_eq_finsum_in_univ, finsum_eq_finsum_in_univ, finsum_eq_finsum_in_univ],
  apply finsum_in_add_distrib',
  { convert hf, simp },
  { convert hg, simp }
end

lemma finsum_in_comm {s : set α} {t : set β}
  (f : α → β → M) (hs : s.finite) (ht : t.finite) :
  finsum_in s (λ x, finsum_in t (λ y, f x y)) = finsum_in t (λ y, finsum_in s (λ x, f x y)) :=
begin
  rw [finsum_in_eq_finset_sum''' _ hs, finsum_in_eq_finset_sum''' _ ht],
  conv_lhs { congr, skip, funext, rw finsum_in_eq_finset_sum''' _ ht },
  conv_rhs { congr, skip, funext, rw finsum_in_eq_finset_sum''' _ hs },
  exact finset.sum_comm,
end

/-- Given a monoid homomorphism `g : β → M`, and a function `f : α → β`, the sum on `s` over `g ∘ f`
  equals `g` of the sum on `s` over `f`. -/
lemma finsum_in_hom [add_comm_monoid β] (f : α → β) (g : β →+ M) (hs : s.finite) :
  finsum_in s (g ∘ f) = g (finsum_in s f) :=
by rw [finsum_in_eq_finset_sum''' _ hs, finsum_in_eq_finset_sum''' _ hs,
       set.finite.to_finset, finset.sum_hom']

/-- A more general version of `finsum_in_hom` that requires `s ∩ function.support f` and instead of
  `s` to be finite. -/
lemma finsum_in_hom' [add_comm_monoid β] {f : α → β} (g : β →+ M)
  (h₀ : (s ∩ function.support f).finite) :
  finsum_in s (g ∘ f) = g (finsum_in s f) :=
begin
  rw [finsum_in_inter_support f, ← finsum_in_hom _ _ h₀],
  symmetry,
  refine finsum_in_eq_finsum_in_of_subset'' (set.inter_subset_left _ _)
    (set.inter_subset_inter_right _ (λ x hgx, _)),
  rw function.mem_support at hgx ⊢,
  intro hfx, refine hgx _, rw [function.comp_app, hfx],
  exact add_monoid_hom.map_zero g
end

/-- Given a proposition `p` such that for all `x ∈ s, f x ≠ 0 → p x`, the sum on the elements of `s`
  satisfied by `p` equals the sum on `s`. -/
lemma finsum_in_inter_of_ne {p : α → Prop} (hp : ∀ x ∈ s, f x ≠ 0 → p x) :
  finsum_in (s ∩ p) f = finsum_in s f :=
finsum_in_eq_finsum_in_of_subset'' (set.inter_subset_left _ _)
  (λ _ ⟨hsx, hfx⟩, ⟨hsx, hp _ hsx $ function.mem_support.1 hfx⟩)

/-- Given a proposition `p`, the sum on the elements of `s` satisfied by `p` over `f` equals the sum
  on `s` over the function `λ a, if p a then f a else 0`. -/
lemma finsum_in_inter (p : α → Prop) :
  finsum_in (s ∩ p) f = finsum_in s (λ a, if p a then f a else 0) :=
begin
  rw ← @finsum_in_inter_of_ne _ _ _ (λ a, if p a then f a else 0) _ p,
  refine finsum_in_congr rfl (λ x ⟨hsx, hxp⟩, (if_pos hxp).symm),
  finish
end .

end finsum

/-! # noncomputable ℕ-valued cardinality of a type -/

section fincard
/-- `fincard α : ℕ` is the size of α if it's finite, and 0 otherwise -/
noncomputable def fincard (α : Type u) : ℕ :=
if h : nonempty (fintype α) then @fintype.card α (classical.choice h) else 0

open finset

variable {α : Type u}

lemma fincard_eq_card [h : fintype α] : fincard α = fintype.card α :=
by convert dif_pos (nonempty.intro h)

end fincard
