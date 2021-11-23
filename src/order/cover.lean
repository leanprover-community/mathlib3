/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.set.intervals.basic

/-!
# Ranked -/

open set

variables {α : Type*}

section has_lt
variables [has_lt α] {a b : α}

/-- `covers a b` means that `b` covers `a`: `a < b` and there is no element in between. -/
def covers [has_lt α] (a b : α) : Prop := a < b ∧ ∀ ⦃c⦄, a < c → ¬ c < b

lemma covers.lt (h : covers a b) : a < b := h.1

end has_lt

section preorder
variables [preorder α] {a b : α}

lemma covers.le (h : covers a b) : a ≤ b := h.1.le

lemma covers.Ioo_eq (h : covers a b) : Ioo a b = ∅ :=
eq_empty_iff_forall_not_mem.2 $ λ x hx, h.2 hx.1 hx.2

end preorder

section partial_order
variables [partial_order α] {a b : α}

lemma covers.Ico_eq (h : covers a b) : Ico a b = {a} :=
by rw [←set.Ioo_union_left h.lt, h.Ioo_eq, empty_union]

lemma covers.Ioc_eq (h : covers a b) : Ioc a b = {b} :=
by rw [←set.Ioo_union_right h.lt, h.Ioo_eq, empty_union]

lemma covers.Icc_eq (h : covers a b) : Icc a b = {a, b} :=
by { rw [←set.Ico_union_right h.le, h.Ico_eq], refl }

end partial_order
