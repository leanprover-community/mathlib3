/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import data.finset.locally_finite
import data.dfinsupp.interval
import data.dfinsupp.multiset
import data.nat.interval

/-!
# Finite intervals of multisets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides the `locally_finite_order` instance for `multiset α` and calculates the
cardinality of its finite intervals.

## Implementation notes

We implement the intervals via the intervals on `dfinsupp`, rather than via filtering
`multiset.powerset`; this is because `(multiset.replicate n x).powerset` has `2^n` entries not `n+1`
entries as it contains duplicates. We do not go via `finsupp` as this would be noncomputable, and
multisets are typically used computationally.

-/

open finset dfinsupp function
open_locale big_operators pointwise

variables {α : Type*} {β : α → Type*}

namespace multiset

variables [decidable_eq α] (f g : multiset α)

instance : locally_finite_order (multiset α) :=
locally_finite_order.of_Icc (multiset α)
  (λ f g, (finset.Icc f.to_dfinsupp g.to_dfinsupp).map
    (multiset.equiv_dfinsupp.to_equiv.symm.to_embedding))
  (λ f g x, by simp)

lemma Icc_eq :
  finset.Icc f g =
    (finset.Icc f.to_dfinsupp g.to_dfinsupp).map
      (multiset.equiv_dfinsupp.to_equiv.symm.to_embedding) := rfl

lemma card_Icc  :
  (finset.Icc f g).card = ∏ i in f.to_finset ∪ g.to_finset, (g.count i + 1 - f.count i) :=
by simp_rw [Icc_eq, finset.card_map, dfinsupp.card_Icc, nat.card_Icc, multiset.to_dfinsupp_apply,
  to_dfinsupp_support]

lemma card_Ico :
  (finset.Ico f g).card = ∏ i in f.to_finset ∪ g.to_finset, (g.count i + 1 - f.count i) - 1 :=
by rw [card_Ico_eq_card_Icc_sub_one, card_Icc]

lemma card_Ioc :
  (finset.Ioc f g).card = ∏ i in f.to_finset ∪ g.to_finset, (g.count i + 1 - f.count i) - 1 :=
by rw [card_Ioc_eq_card_Icc_sub_one, card_Icc]

lemma card_Ioo :
  (finset.Ioo f g).card = ∏ i in f.to_finset ∪ g.to_finset, (g.count i + 1 - f.count i) - 2 :=
by rw [card_Ioo_eq_card_Icc_sub_two, card_Icc]

lemma card_Iic :
  (finset.Iic f).card = ∏ i in f.to_finset, (f.count i + 1) :=
by simp_rw [Iic_eq_Icc, card_Icc, bot_eq_zero, to_finset_zero, empty_union, count_zero, tsub_zero]

end multiset
