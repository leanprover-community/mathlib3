/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.big_operators.finsupp
import data.finset.pointwise
import data.finsupp.indicator
import data.fintype.big_operators

/-!
# Finitely supported product of finsets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the finitely supported product of finsets as a `finset (ι →₀ α)`.

## Main declarations

* `finset.finsupp`: Finitely supported product of finsets. `s.finset t` is the product of the `t i`
  over all `i ∈ s`.
* `finsupp.pi`: `f.pi` is the finset of `finsupp`s whose `i`-th value lies in `f i`. This is the
  special case of `finset.finsupp` where we take the product of the `f i` over the support of `f`.

## Implementation notes

We make heavy use of the fact that `0 : finset α` is `{0}`. This scalar actions convention turns out
to be precisely what we want here too.
-/

noncomputable theory

open finsupp
open_locale big_operators classical pointwise

variables {ι α : Type*} [has_zero α] {s : finset ι} {f : ι →₀ α}

namespace finset

/-- Finitely supported product of finsets. -/
protected def finsupp (s : finset ι) (t : ι → finset α) : finset (ι →₀ α) :=
(s.pi t).map ⟨indicator s, indicator_injective s⟩

lemma mem_finsupp_iff {t : ι → finset α} : f ∈ s.finsupp t ↔ f.support ⊆ s ∧ ∀ i ∈ s, f i ∈ t i :=
begin
  refine mem_map.trans ⟨_, _⟩,
  { rintro ⟨f, hf, rfl⟩,
    refine ⟨support_indicator_subset _ _, λ i hi, _⟩,
    convert mem_pi.1 hf i hi,
    exact indicator_of_mem hi _ },
  { refine λ h, ⟨λ i _, f i, mem_pi.2 h.2, _⟩,
    ext i,
    exact ite_eq_left_iff.2 (λ hi, (not_mem_support_iff.1 $ λ H, hi $ h.1 H).symm) }
end

/-- When `t` is supported on `s`, `f ∈ s.finsupp t` precisely means that `f` is pointwise in `t`. -/
@[simp] lemma mem_finsupp_iff_of_support_subset {t : ι →₀ finset α} (ht : t.support ⊆ s) :
  f ∈ s.finsupp t ↔ ∀ i, f i ∈ t i :=
begin
  refine mem_finsupp_iff.trans (forall_and_distrib.symm.trans $ forall_congr $ λ i, ⟨λ h, _,
    λ h, ⟨λ hi, ht $ mem_support_iff.2 $ λ H, mem_support_iff.1 hi _, λ _, h⟩⟩),
  { by_cases hi : i ∈ s,
    { exact h.2 hi },
    { rw [not_mem_support_iff.1 (mt h.1 hi), not_mem_support_iff.1 (λ H, hi $ ht H)],
      exact zero_mem_zero } },
  { rwa [H, mem_zero] at h }
end

@[simp] lemma card_finsupp (s : finset ι) (t : ι → finset α) :
  (s.finsupp t).card = ∏ i in s, (t i).card :=
(card_map _).trans $ card_pi _ _

end finset

open finset

namespace finsupp

/-- Given a finitely supported function `f : ι →₀ finset α`, one can define the finset
`f.pi` of all finitely supported functions whose value at `i` is in `f i` for all `i`. -/
def pi (f : ι →₀ finset α) : finset (ι →₀ α) := f.support.finsupp f

@[simp] lemma mem_pi {f : ι →₀ finset α} {g : ι →₀ α} : g ∈ f.pi ↔ ∀ i, g i ∈ f i :=
mem_finsupp_iff_of_support_subset $ subset.refl _

@[simp] lemma card_pi (f : ι →₀ finset α) : f.pi.card = f.prod (λ i, (f i).card) :=
begin
  rw [pi, card_finsupp],
  exact finset.prod_congr rfl (λ i _, by simp only [pi.nat_apply, nat.cast_id]),
end

end finsupp
