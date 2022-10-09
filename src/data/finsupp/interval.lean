/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.finsupp
import data.finset.locally_finite
import data.finsupp.order

/-!
# Finite intervals of finitely supported functions

This file provides the `locally_finite_order` instance for `ι →₀ α` when `α` itself is locally
finite and calculates the cardinality of its finite intervals.

## Main declarations

* `finsupp.range_singleton`: Postcomposition with `has_singleton.singleton` on `finset` as a
  `finsupp`.
* `finsupp.range_Icc`: Postcomposition with `finset.Icc` as a `finsupp`.

Both these definitions use the fact that `0 = {0}` to ensure that the resulting function is finitely
supported.
-/

noncomputable theory

open finset finsupp function
open_locale big_operators classical pointwise

variables {ι α : Type*}

namespace finsupp
section range_singleton
variables [has_zero α] {f : ι →₀ α} {i : ι} {a : α}

/-- Pointwise `finset.singleton` bundled as a `finsupp`. -/
@[simps] def range_singleton (f : ι →₀ α) : ι →₀ finset α :=
{ to_fun := λ i, {f i},
  support := f.support,
  mem_support_to_fun := λ i, begin
    rw [←not_iff_not, not_mem_support_iff, not_ne_iff],
    exact singleton_injective.eq_iff.symm,
  end }

lemma mem_range_singleton_apply_iff : a ∈ f.range_singleton i ↔ a = f i := mem_singleton

end range_singleton

section range_Icc
variables [has_zero α] [partial_order α] [locally_finite_order α] {f g : ι →₀ α} {i : ι} {a : α}

/-- Pointwise `finset.Icc` bundled as a `finsupp`. -/
@[simps] def range_Icc (f g : ι →₀ α) : ι →₀ finset α :=
{ to_fun := λ i, Icc (f i) (g i),
  support := f.support ∪ g.support,
  mem_support_to_fun := λ i, begin
    rw [mem_union, ←not_iff_not, not_or_distrib, not_mem_support_iff, not_mem_support_iff,
      not_ne_iff],
    exact Icc_eq_singleton_iff.symm,
  end }

lemma mem_range_Icc_apply_iff : a ∈ f.range_Icc g i ↔ f i ≤ a ∧ a ≤ g i := mem_Icc

end range_Icc

variables [partial_order α] [has_zero α] [locally_finite_order α] (f g : ι →₀ α)

instance : locally_finite_order (ι →₀ α) :=
locally_finite_order.of_Icc (ι →₀ α)
  (λ f g, (f.support ∪ g.support).finsupp $ f.range_Icc g)
  (λ f g x, begin
    refine (mem_finsupp_iff_of_support_subset $ subset.rfl).trans _,
    simp_rw mem_range_Icc_apply_iff,
    exact forall_and_distrib,
  end)

lemma card_Icc : (Icc f g).card = ∏ i in f.support ∪ g.support, (Icc (f i) (g i)).card :=
card_finsupp _ _

lemma card_Ico : (Ico f g).card = ∏ i in f.support ∪ g.support, (Icc (f i) (g i)).card - 1 :=
by rw [card_Ico_eq_card_Icc_sub_one, card_Icc]

lemma card_Ioc : (Ioc f g).card = ∏ i in f.support ∪ g.support, (Icc (f i) (g i)).card - 1 :=
by rw [card_Ioc_eq_card_Icc_sub_one, card_Icc]

lemma card_Ioo : (Ioo f g).card = ∏ i in f.support ∪ g.support, (Icc (f i) (g i)).card - 2 :=
by rw [card_Ioo_eq_card_Icc_sub_two, card_Icc]

end finsupp
