/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.locally_finite

/-!
# Intervals as finsets

This file provides basic results about all the `finset.Ixx`, which are defined in
`order.locally_finite`.

## TODO

Bring the lemmas about `finset.Ico` in `data.finset.intervals` here and in `data.nat.intervals`.
-/

namespace finset
variables {α : Type*}
section preorder
variables [preorder α] [locally_finite_order α] {a b : α}

@[simp] lemma nonempty_Icc : (Icc a b).nonempty ↔ a ≤ b :=
by rw [←coe_nonempty, coe_Icc, set.nonempty_Icc]

@[simp] lemma nonempty_Ioc : (Ioc a b).nonempty ↔ a < b :=
by rw [←coe_nonempty, coe_Ioc, set.nonempty_Ioc]

@[simp] lemma nonempty_Ioo [densely_ordered α] : (Ioo a b).nonempty ↔ a < b :=
by rw [←coe_nonempty, coe_Ioo, set.nonempty_Ioo]

@[simp] lemma Icc_eq_empty_iff : Icc a b = ∅ ↔ ¬a ≤ b :=
by rw [←coe_eq_empty, coe_Icc, set.Icc_eq_empty_iff]

@[simp] lemma Ioc_eq_empty_iff : Ioc a b = ∅ ↔ ¬a < b :=
by rw [←coe_eq_empty, coe_Ioc, set.Ioc_eq_empty_iff]

@[simp] lemma Ioo_eq_empty_iff [densely_ordered α] : Ioo a b = ∅ ↔ ¬a < b :=
by rw [←coe_eq_empty, coe_Ioo, set.Ioo_eq_empty_iff]

alias Icc_eq_empty_iff ↔ _ finset.Icc_eq_empty
alias Ioc_eq_empty_iff ↔ _ finset.Ioc_eq_empty

@[simp] lemma Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅ :=
eq_empty_iff_forall_not_mem.2 $ λ x hx, h ((mem_Ioo.1 hx).1.trans (mem_Ioo.1 hx).2)

@[simp] lemma Icc_eq_empty_of_lt (h : b < a) : Icc a b = ∅ :=
Icc_eq_empty h.not_le

@[simp] lemma Ioc_eq_empty_of_le (h : b ≤ a) : Ioc a b = ∅ :=
Ioc_eq_empty h.not_lt

@[simp] lemma Ioo_eq_empty_of_le (h : b ≤ a) : Ioo a b = ∅ :=
Ioo_eq_empty h.not_lt

variables (a)

@[simp] lemma Ioc_self : Ioc a a = ∅ :=
by rw [←coe_eq_empty, coe_Ioc, set.Ioc_self]

@[simp] lemma Ioo_self : Ioo a a = ∅ :=
by rw [←coe_eq_empty, coe_Ioo, set.Ioo_self]

end preorder

section partial_order
variables [partial_order α] [locally_finite_order α] {a b : α}

@[simp] lemma Icc_self (a : α) : Icc a a = {a} :=
by rw [←coe_eq_singleton, coe_Icc, set.Icc_self]

end partial_order

section ordered_cancel_add_comm_monoid
variables [ordered_cancel_add_comm_monoid α] [has_exists_add_of_le α] [decidable_eq α]
  [locally_finite_order α]

lemma image_add_const_Icc (a b c : α) : (Icc a b).image ((+) c) = Icc (a + c) (b + c) :=
begin
  ext x,
  rw [mem_image, mem_Icc],
  split,
  { rintro ⟨y, hy, rfl⟩,
    rw mem_Icc at hy,
    rw add_comm c,
    exact ⟨add_le_add_right hy.1 c, add_le_add_right hy.2 c⟩ },
  { intro hx,
    obtain ⟨y, hy⟩ := exists_add_of_le hx.1,
    rw [hy, add_right_comm] at hx,
    rw [eq_comm, add_right_comm, add_comm] at hy,
    exact ⟨a + y, mem_Icc.2 ⟨le_of_add_le_add_right hx.1, le_of_add_le_add_right hx.2⟩, hy⟩ }
end

lemma image_add_const_Ioc (a b c : α) : (Ioc a b).image ((+) c) = Ioc (a + c) (b + c) :=
begin
  ext x,
  rw [mem_image, mem_Ioc],
  split,
  { rintro ⟨y, hy, rfl⟩,
    rw mem_Ioc at hy,
    rw add_comm c,
    exact ⟨add_lt_add_right hy.1 c, add_le_add_right hy.2 c⟩ },
  { intro hx,
    obtain ⟨y, hy⟩ := exists_add_of_le hx.1.le,
    rw [hy, add_right_comm] at hx,
    rw [eq_comm, add_right_comm, add_comm] at hy,
    exact ⟨a + y, mem_Ioc.2 ⟨lt_of_add_lt_add_right hx.1, le_of_add_le_add_right hx.2⟩, hy⟩ }
end

lemma image_add_const_Ioo (a b c : α) : (Ioo a b).image ((+) c) = Ioo (a + c) (b + c) :=
begin
  ext x,
  rw [mem_image, mem_Ioo],
  split,
  { rintro ⟨y, hy, rfl⟩,
    rw mem_Ioo at hy,
    rw add_comm c,
    exact ⟨add_lt_add_right hy.1 c, add_lt_add_right hy.2 c⟩ },
  { intro hx,
    obtain ⟨y, hy⟩ := exists_add_of_le hx.1.le,
    rw [hy, add_right_comm] at hx,
    rw [eq_comm, add_right_comm, add_comm] at hy,
    exact ⟨a + y, mem_Ioo.2 ⟨lt_of_add_lt_add_right hx.1, lt_of_add_lt_add_right hx.2⟩, hy⟩ }
end

end ordered_cancel_add_comm_monoid
end finset
