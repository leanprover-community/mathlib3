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

variables {α : Type*}

namespace multiset
variables [decidable_eq α] (s t : multiset α)

instance : locally_finite_order (multiset α) :=
locally_finite_order.of_Icc (multiset α)
  (λ s t, (finset.Icc s.to_dfinsupp t.to_dfinsupp).map
    (multiset.equiv_dfinsupp.to_equiv.symm.to_embedding))
  (λ s t x, by simp)

lemma Icc_eq :
  finset.Icc s t =
    (finset.Icc s.to_dfinsupp t.to_dfinsupp).map
      (multiset.equiv_dfinsupp.to_equiv.symm.to_embedding) := rfl

lemma interval_eq :
  interval s t =
    (interval s.to_dfinsupp t.to_dfinsupp).map
      (multiset.equiv_dfinsupp.to_equiv.symm.to_embedding) :=
(Icc_eq _ _).trans $ by simp [interval]

lemma card_Icc  :
  (finset.Icc s t).card = ∏ i in s.to_finset ∪ t.to_finset, (t.count i + 1 - s.count i) :=
by simp_rw [Icc_eq, finset.card_map, dfinsupp.card_Icc, nat.card_Icc, multiset.to_dfinsupp_apply,
  to_dfinsupp_support]

lemma card_Ico :
  (finset.Ico s t).card = ∏ i in s.to_finset ∪ t.to_finset, (t.count i + 1 - s.count i) - 1 :=
by rw [card_Ico_eq_card_Icc_sub_one, card_Icc]

lemma card_Ioc :
  (finset.Ioc s t).card = ∏ i in s.to_finset ∪ t.to_finset, (t.count i + 1 - s.count i) - 1 :=
by rw [card_Ioc_eq_card_Icc_sub_one, card_Icc]

lemma card_Ioo :
  (finset.Ioo s t).card = ∏ i in s.to_finset ∪ t.to_finset, (t.count i + 1 - s.count i) - 2 :=
by rw [card_Ioo_eq_card_Icc_sub_two, card_Icc]

lemma card_interval  :
  (interval s t).card =
    ∏ i in s.to_finset ∪ t.to_finset, ((t.count i - s.count i : ℤ).nat_abs + 1) :=
begin
  rw [interval, card_Icc, union_eq_right_iff_subset.2 (to_finset_subset.2 $ subset_of_le $
    @inf_le_sup _ _ s t), sup_eq_union, inf_eq_inter, to_finset_union],
  congr,
  ext a,
  rw [count_union, count_inter, ←int.coe_nat_inj', int.coe_nat_sub (min_le_max.trans le_self_add)],
  push_cast,
  rw [add_sub_right_comm, max_sub_min_eq_abs],
end

lemma card_Iic :
  (finset.Iic s).card = ∏ i in s.to_finset, (s.count i + 1) :=
by simp_rw [Iic_eq_Icc, card_Icc, bot_eq_zero, to_finset_zero, empty_union, count_zero, tsub_zero]

end multiset
