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

universes u v

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

lemma mem_univ' [h : fintype α] (x : α) : x ∈ univ' α :=
(@univ'_eq_univ _ h).symm ▸ mem_univ _

end finset

/-! # noncomputable finite sums -/

section finsum

variables {α : Type u} {M : Type v} [add_comm_monoid M]

/-- Sum of `f x` as `x` ranges over the elements of the support of `f`, if it's finite. Zero otherwise. -/
noncomputable def finsum (f : α → M) : M :=
if h : (function.support f).finite then finset.sum (h.to_finset) f else 0

/-- Sum of `f x` for `x ∈ s`, where `s : set α` is finite. Zero if s is infinite.  -/
noncomputable def finsum_in (s : set α) (f : α → M) : M :=
finsum (λ x, if x ∈ s then f x else 0)

def finsum_def (f : α → M) :
  finsum f = if h : (function.support f).finite then finset.sum (h.to_finset) f else 0 := rfl

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

lemma finsum_eq_finsupp_sum' {f : α → M} (hf : (function.support f).finite) :
  finsum f = finsupp.sum (finsupp.of_support_finite hf) (λ x m, m) :=
by rw [← finsum_eq_finsupp_sum, finsupp.of_support_finite_def]

lemma finsum_eq_finset_sum {f : α → M} (hf : (function.support f).finite) :
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
