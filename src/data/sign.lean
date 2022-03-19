/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import order.basic

/-!
# Sign function

This file defines the sign function for types with zero and a decidable less-than relation, and
proves some basic theorems about it.
-/


variables {α : Type*} [has_zero α]

/-- The sign of an element - 1 if it's positive, -1 if negative, 0 otherwise. -/
def sign [has_lt α] [decidable_rel ((<) : α → α → Prop)] (a : α) :=
if 0 < a then (1 : ℤ) else if a < 0 then -1 else 0

section preorder

variables [preorder α] [decidable_rel ((<) : α → α → Prop)] {a b : α}

@[simp] lemma sign_zero : sign (0 : α) = 0 := by simp [sign]

end preorder

section linear_order

variables [linear_order α] {a b : α}

lemma sign_ne_zero (h : a ≠ 0) : sign a ≠ 0 :=
begin
  contrapose! h,
  rw sign at h,
  split_ifs at h,
  { cases h },
  { cases h },
  exact ((lt_trichotomy a 0).resolve_left h_2).resolve_right h_1
end

end linear_order
