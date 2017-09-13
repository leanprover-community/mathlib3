/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Ordered (non-cancellative) monoids
-/
import data.set order.galois_connection
open set lattice function

section old_structure_cmd

set_option old_structure_cmd true

class ordered_comm_monoid (α : Type*) extends add_comm_monoid α, partial_order α :=
(add_le_add_left       : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)
(lt_of_add_lt_add_left : ∀ a b c : α, a + b < a + c → b < c)

class canonically_ordered_monoid (α : Type*) extends ordered_comm_monoid α :=
(le_iff_exists_add : ∀a b:α, a ≤ b ↔ ∃c, b = a + c)

end old_structure_cmd

section ordered_comm_monoid
variables {α : Type*} [ordered_comm_monoid α] {a b c d : α}

lemma add_le_add_left' (h : a ≤ b) : c + a ≤ c + b :=
ordered_comm_monoid.add_le_add_left a b h c

lemma add_le_add_right' (h : a ≤ b) : a + c ≤ b + c :=
add_comm c a ▸ add_comm c b ▸ add_le_add_left' h

lemma lt_of_add_lt_add_left' : a + b < a + c → b < c :=
ordered_comm_monoid.lt_of_add_lt_add_left a b c

lemma add_le_add' (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d :=
le_trans (add_le_add_right' h₁) (add_le_add_left' h₂)

lemma le_add_of_nonneg_right' (h : b ≥ 0) : a ≤ a + b :=
have a + b ≥ a + 0, from add_le_add_left' h,
by rwa add_zero at this

lemma le_add_of_nonneg_left' (h : b ≥ 0) : a ≤ b + a :=
have 0 + a ≤ b + a, from add_le_add_right' h,
by rwa zero_add at this

lemma lt_of_add_lt_add_right' (h : a + b < c + b) : a < c :=
lt_of_add_lt_add_left'
  (show b + a < b + c, begin rw [add_comm b a, add_comm b c], assumption end)

-- here we start using properties of zero.
lemma le_add_of_nonneg_of_le' (ha : 0 ≤ a) (hbc : b ≤ c) : b ≤ a + c :=
zero_add b ▸ add_le_add' ha hbc

lemma le_add_of_le_of_nonneg' (hbc : b ≤ c) (ha : 0 ≤ a) : b ≤ c + a :=
add_zero b ▸ add_le_add' hbc ha

lemma add_nonneg' (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b :=
le_add_of_nonneg_of_le' ha hb

lemma add_pos_of_pos_of_nonneg' (ha : 0 < a) (hb : 0 ≤ b) : 0 < a + b :=
lt_of_lt_of_le ha $ le_add_of_nonneg_right' hb

lemma add_pos' (ha : 0 < a) (hb : 0 < b) : 0 < a + b :=
add_pos_of_pos_of_nonneg' ha $ le_of_lt hb

lemma add_pos_of_nonneg_of_pos' (ha : 0 ≤ a) (hb : 0 < b) : 0 < a + b :=
lt_of_lt_of_le hb $ le_add_of_nonneg_left' ha

lemma add_nonpos' (ha : a ≤ 0) (hb : b ≤ 0) : a + b ≤ 0 :=
zero_add (0:α) ▸ (add_le_add' ha hb)

lemma add_le_of_nonpos_of_le' (ha : a ≤ 0) (hbc : b ≤ c) : a + b ≤ c :=
zero_add c ▸ add_le_add' ha hbc

lemma add_le_of_le_of_nonpos' (hbc : b ≤ c) (ha : a ≤ 0) : b + a ≤ c :=
add_zero c ▸ add_le_add' hbc ha

lemma add_neg_of_neg_of_nonpos' (ha : a < 0) (hb : b ≤ 0) : a + b < 0 :=
lt_of_le_of_lt (add_le_of_le_of_nonpos' (le_refl _) hb) ha

lemma add_neg_of_nonpos_of_neg' (ha : a ≤ 0) (hb : b < 0) : a + b < 0 :=
lt_of_le_of_lt (add_le_of_nonpos_of_le' ha (le_refl _)) hb

lemma add_neg' (ha : a < 0) (hb : b < 0) : a + b < 0 :=
add_neg_of_nonpos_of_neg' (le_of_lt ha) hb

lemma lt_add_of_nonneg_of_lt' (ha : 0 ≤ a) (hbc : b < c) : b < a + c :=
lt_of_lt_of_le hbc $ le_add_of_nonneg_left' ha

lemma lt_add_of_lt_of_nonneg' (hbc : b < c) (ha : 0 ≤ a) : b < c + a :=
lt_of_lt_of_le hbc $ le_add_of_nonneg_right' ha

lemma lt_add_of_pos_of_lt' (ha : 0 < a) (hbc : b < c) : b < a + c :=
lt_add_of_nonneg_of_lt' (le_of_lt ha) hbc

lemma lt_add_of_lt_of_pos' (hbc : b < c) (ha : 0 < a) : b < c + a :=
lt_add_of_lt_of_nonneg' hbc (le_of_lt ha)

lemma add_lt_of_nonpos_of_lt' (ha : a ≤ 0) (hbc : b < c) : a + b < c :=
lt_of_le_of_lt (add_le_of_nonpos_of_le' ha (le_refl _)) hbc

lemma add_lt_of_lt_of_nonpos' (hbc : b < c) (ha : a ≤ 0)  : b + a < c :=
lt_of_le_of_lt (add_le_of_le_of_nonpos' (le_refl _) ha) hbc

lemma add_lt_of_neg_of_lt' (ha : a < 0) (hbc : b < c) : a + b < c :=
add_lt_of_nonpos_of_lt' (le_of_lt ha) hbc

lemma add_lt_of_lt_of_neg' (hbc : b < c) (ha : a < 0) : b + a < c :=
add_lt_of_lt_of_nonpos' hbc (le_of_lt ha)

lemma add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg'
  (ha : 0 ≤ a) (hb : 0 ≤ b) : a + b = 0 ↔ a = 0 ∧ b = 0 :=
iff.intro
  (assume hab : a + b = 0,
   have a ≤ 0, from hab ▸ le_add_of_le_of_nonneg' (le_refl _) hb,
   have a = 0, from le_antisymm this ha,
   have b ≤ 0, from hab ▸ le_add_of_nonneg_of_le' ha (le_refl _),
   have b = 0, from le_antisymm this hb,
   and.intro ‹a = 0› ‹b = 0›)
  (assume ⟨ha', hb'⟩, by rw [ha', hb', add_zero])

end ordered_comm_monoid

section canonically_ordered_monoid
variables {α : Type*} [canonically_ordered_monoid α] {a b c d : α}

lemma le_iff_exists_add : a ≤ b ↔ ∃c, b = a + c :=
canonically_ordered_monoid.le_iff_exists_add a b

@[simp] lemma zero_le : 0 ≤ a := le_iff_exists_add.mpr ⟨a, by simp⟩

@[simp] lemma add_eq_zero_iff : a + b = 0 ↔ a = 0 ∧ b = 0 :=
add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg' zero_le zero_le

end canonically_ordered_monoid
