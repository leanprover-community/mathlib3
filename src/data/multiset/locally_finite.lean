/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.locally_finite

/-!
# Intervals as multisets

This file provides basic results about all the `multiset.Ixx`, which are defined in
`order.locally_finite`.

## TODO

Bring the lemmas about `multiset.Ico` in `data.multiset.intervals` here and in `data.nat.interval`.
-/

variables {α : Type*}

namespace multiset
section preorder
variables [preorder α] [locally_finite_order α] {a b : α}

lemma nodup_Icc : (Icc a b).nodup := finset.nodup _

lemma nodup_Ioc : (Ioc a b).nodup := finset.nodup _

lemma nodup_Ioo : (Ioo a b).nodup := finset.nodup _

@[simp] lemma Icc_eq_zero_iff : Icc a b = 0 ↔ ¬a ≤ b :=
by rw [Icc, finset.val_eq_zero, finset.Icc_eq_empty_iff]

@[simp] lemma Ioc_eq_zero_iff : Ioc a b = 0 ↔ ¬a < b :=
by rw [Ioc, finset.val_eq_zero, finset.Ioc_eq_empty_iff]

@[simp] lemma Ioo_eq_zero_iff [densely_ordered α] : Ioo a b = 0 ↔ ¬a < b :=
by rw [Ioo, finset.val_eq_zero, finset.Ioo_eq_empty_iff]

alias Icc_eq_zero_iff ↔ _ multiset.Icc_eq_zero
alias Ioc_eq_zero_iff ↔ _ multiset.Ioc_eq_zero

@[simp] lemma Ioo_eq_zero (h : ¬a < b) : Ioo a b = 0 :=
eq_zero_iff_forall_not_mem.2 $ λ x hx, h ((mem_Ioo.1 hx).1.trans (mem_Ioo.1 hx).2)

@[simp] lemma Icc_eq_zero_of_lt (h : b < a) : Icc a b = 0 :=
Icc_eq_zero h.not_le

@[simp] lemma Ioc_eq_zero_of_le (h : b ≤ a) : Ioc a b = 0 :=
Ioc_eq_zero h.not_lt

@[simp] lemma Ioo_eq_zero_of_le (h : b ≤ a) : Ioo a b = 0 :=
Ioo_eq_zero h.not_lt

variables (a)

@[simp] lemma Ioc_self : Ioc a a = 0 :=
by rw [Ioc, finset.Ioc_self, finset.empty_val]

@[simp] lemma Ioo_self : Ioo a a = 0 :=
by rw [Ioo, finset.Ioo_self, finset.empty_val]

end preorder

section partial_order
variables [partial_order α] [locally_finite_order α] {a b : α}

@[simp] lemma Icc_self (a : α) : Icc a a = {a} :=
by rw [Icc, finset.Icc_self, finset.singleton_val]

end partial_order

section ordered_cancel_add_comm_monoid
variables [ordered_cancel_add_comm_monoid α] [has_exists_add_of_le α]
  [locally_finite_order α]

lemma map_add_left_Icc (a b c : α) : (Icc a b).map ((+) c) = Icc (c + a) (c + b) :=
by { classical, rw [Icc, Icc, ←finset.image_add_left_Icc, finset.image_val,
    (multiset.nodup_map (add_right_injective c) $ finset.nodup _).erase_dup] }

lemma map_add_left_Ioc (a b c : α) : (Ioc a b).map ((+) c) = Ioc (c + a) (c + b) :=
by { classical, rw [Ioc, Ioc, ←finset.image_add_left_Ioc, finset.image_val,
    (multiset.nodup_map (add_right_injective c) $ finset.nodup _).erase_dup] }

lemma map_add_left_Ioo (a b c : α) : (Ioo a b).map ((+) c) = Ioo (c + a) (c + b) :=
by { classical, rw [Ioo, Ioo, ←finset.image_add_left_Ioo, finset.image_val,
    (multiset.nodup_map (add_right_injective c) $ finset.nodup _).erase_dup] }

lemma map_add_right_Icc (a b c : α) : (Icc a b).map (λ x, x + c) = Icc (a + c) (b + c) :=
by { simp_rw add_comm _ c, exact map_add_left_Icc _ _ _ }

lemma map_add_right_Ioc (a b c : α) : (Ioc a b).map (λ x, x + c) = Ioc (a + c) (b + c) :=
by { simp_rw add_comm _ c, exact map_add_left_Ioc _ _ _ }

lemma map_add_right_Ioo (a b c : α) : (Ioo a b).map (λ x, x + c) = Ioo (a + c) (b + c) :=
by { simp_rw add_comm _ c, exact map_add_left_Ioo _ _ _ }

end ordered_cancel_add_comm_monoid
end multiset
