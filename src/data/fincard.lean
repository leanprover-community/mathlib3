/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
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

Variables:

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

/-- univ' α is the finset corresponding to all of α if α is finite, and the empty set otherwise.
Note that it is noncomputable -/
noncomputable def univ' (α : Type u) : finset α :=
if h : nonempty (fintype α) then (classical.choice h).elems else ∅

variable {α : Type u}

/-- univ' α is finset.univ if α is a fintype. -/
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

/-- Sum of `f x` for `x ∈ s`, where `s : set α` is finite. Zero if s is infinite.  -/
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

lemma finsum_in_eq_finset_sum (f : α → M) (s : set α)
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
      rw function.mem_support at *; finish }
end .

lemma finsum_in_eq_finset_sum' (f : α → M) (s : set α)
  (hf : (function.support f).finite) :
  finsum_in s f = (finset.filter (∈ s) hf.to_finset).sum f :=
begin
  rw finsum_in_eq_finset_sum f s (set.finite.subset hf (set.inter_subset_right _ _)),
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
  rw finsum_in_eq_finset_sum f s (set.finite.subset hs (set.inter_subset_left _ _)),
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

lemma finsum_in_eq (f : α → M) (s : set α)
  (hf : (s ∩ function.support f).finite) : finsum_in (s ∩ function.support f) f = finsum_in s f :=
begin
  rw [finsum_in_eq_finset_sum f s hf, finsum_in_eq_finset_sum f (s ∩ function.support f) _],
    { rw [set.finite.to_finset, set.finite.to_finset],
      refine finset.sum_congr _ (λ _ _, rfl);
      simp_rw [set.inter_assoc, set.inter_self], assumption, congr }
end

variables {f g : α → M} {a b : α} {s t : set α}

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

-- ↓ this should go in data.set.basic probably
lemma set.insert_inter_of_not_mem (s₁ s₂ : set α) (a : α) (h : a ∉ s₂) :
  insert a s₁ ∩ s₂ = s₁ ∩ s₂ :=
by { ext, rw [set.mem_inter_iff, set.mem_insert_iff], split; finish }

/-- A more general version of `finsum_in_insert` that requires `s ∩ function.support f` instead of
  `s` to be finite. -/
@[simp] lemma finsum_in_insert' (f : α → M) (h : a ∉ s) (hs : (s ∩ function.support f).finite) :
  finsum_in (insert a s) f = f a + finsum_in s f :=
begin
  by_cases ha : a ∈ function.support f,
    { have := finsum_in_insert f
        (show a ∉ s ∩ function.support f, by exact λ h', h h'.1) hs,
      rw [finsum_in_eq _ _ hs] at this,
      rw [← this, ← finsum_in_eq f (insert a s)
          (by { rw [← set.insert_eq_of_mem ha, ← set.insert_inter], exact set.finite.insert _ hs })],
      congr, rw [set.insert_inter, set.insert_eq_of_mem ha] },
    { rw [← finsum_in_eq _ _ (show (insert a s ∩ function.support f).finite,
        by exact (set.insert_inter_of_not_mem s (function.support f) a ha).symm ▸ hs),
          set.insert_inter_of_not_mem s (function.support f) a ha,
          finsum_in_eq _ _ hs, function.nmem_support.1 ha, zero_add] }
end

/-- A more general version of `finsum_in_insert_of_eq_zero_if_not_mem` that requires
  `s ∩ function.support f` instead of `s` to be finite. -/
lemma finsum_in_insert_of_eq_zero_if_not_mem' (h : a ∉ s → f a = 0)
  (hs : (s ∩ function.support f).finite) : finsum_in (insert a s) f = finsum_in s f :=
begin
  by_cases hm : a ∈ s,
    { simp_rw set.insert_eq_of_mem hm },
    { rw [finsum_in_insert' f hm hs, h hm, zero_add] }
end

/-- If `f a = 0` for all `a ∉ s`, then the sum on `insert a s` over the function `f` equals the sum
  on `s` over `f`. -/
lemma finsum_in_insert_of_eq_zero_if_not_mem (h : a ∉ s → f a = 0) (hs : s.finite) :
  finsum_in (insert a s) f = finsum_in s f :=
finsum_in_insert_of_eq_zero_if_not_mem' h (set.finite.subset hs (set.inter_subset_left _ _))

/-- If `f a = 0`, then the sum on `insert a s` over the function `f` equals the sum on `s` over `f`.
  -/
@[simp] lemma finsum_insert_zero (h : f a = 0) (hs : s.finite) :
  finsum_in (insert a s) f = finsum_in s f :=
finsum_in_insert_of_eq_zero_if_not_mem (λ _, h) hs

/-- A more general version of `finsum_insert_zero` that requires `s ∩ function.support f` instead of
  `s` to be finite. -/
@[simp] lemma finsum_insert_zero' (h : f a = 0) (hs : (s ∩ function.support f).finite) :
  finsum_in (insert a s) f = finsum_in s f :=
finsum_in_insert_of_eq_zero_if_not_mem' (λ _, h) hs

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
