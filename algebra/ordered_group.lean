/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import algebra.group tactic

universe u
variable {α : Type u}

section ordered_cancel_comm_monoid
variables [ordered_cancel_comm_monoid α] {a b c : α}

@[simp] lemma add_le_add_iff_left (a : α) {b c : α} : a + b ≤ a + c ↔ b ≤ c :=
⟨le_of_add_le_add_left, λ h, add_le_add_left h _⟩

@[simp] lemma add_le_add_iff_right (c : α) : a + c ≤ b + c ↔ a ≤ b :=
add_comm c a ▸ add_comm c b ▸ add_le_add_iff_left c

@[simp] lemma add_lt_add_iff_left (a : α) {b c : α} : a + b < a + c ↔ b < c :=
⟨lt_of_add_lt_add_left, λ h, add_lt_add_left h _⟩

@[simp] lemma add_lt_add_iff_right (c : α) : a + c < b + c ↔ a < b :=
add_comm c a ▸ add_comm c b ▸ add_lt_add_iff_left c

@[simp] lemma le_add_iff_nonneg_right (a : α) {b : α} : a ≤ a + b ↔ 0 ≤ b :=
have a + 0 ≤ a + b ↔ 0 ≤ b, from add_le_add_iff_left a,
by rwa add_zero at this

@[simp] lemma le_add_iff_nonneg_left (a : α) {b : α} : a ≤ b + a ↔ 0 ≤ b :=
by rw [add_comm, le_add_iff_nonneg_right]

@[simp] lemma lt_add_iff_pos_right (a : α) {b : α} : a < a + b ↔ 0 < b :=
have a + 0 < a + b ↔ 0 < b, from add_lt_add_iff_left a,
by rwa add_zero at this

@[simp] lemma lt_add_iff_pos_left (a : α) {b : α} : a < b + a ↔ 0 < b :=
by rw [add_comm, lt_add_iff_pos_right]

lemma add_eq_zero_iff_eq_zero_of_nonneg
  (ha : 0 ≤ a) (hb : 0 ≤ b) : a + b = 0 ↔ a = 0 ∧ b = 0 :=
⟨λ hab : a + b = 0,
by split; apply le_antisymm; try {assumption};
   rw ← hab; simp [ha, hb],
λ ⟨ha', hb'⟩, by rw [ha', hb', add_zero]⟩

end ordered_cancel_comm_monoid

section ordered_comm_group
variables [ordered_comm_group α] {a b c : α}

@[simp] lemma neg_le_neg_iff : -a ≤ -b ↔ b ≤ a :=
have a + b + -a ≤ a + b + -b ↔ -a ≤ -b, from add_le_add_iff_left _,
by simp at this; simp [this]

lemma neg_le : -a ≤ b ↔ -b ≤ a :=
have -a ≤ -(-b) ↔ -b ≤ a, from neg_le_neg_iff,
by rwa neg_neg at this

lemma le_neg : a ≤ -b ↔ b ≤ -a :=
have -(-a) ≤ -b ↔ b ≤ -a, from neg_le_neg_iff,
by rwa neg_neg at this

@[simp] lemma neg_nonpos : -a ≤ 0 ↔ 0 ≤ a :=
have -a ≤ -0 ↔ 0 ≤ a, from neg_le_neg_iff,
by rwa neg_zero at this

@[simp] lemma neg_nonneg : 0 ≤ -a ↔ a ≤ 0 :=
have -0 ≤ -a ↔ a ≤ 0, from neg_le_neg_iff,
by rwa neg_zero at this

@[simp] lemma neg_lt_neg_iff : -a < -b ↔ b < a :=
have a + b + -a < a + b + -b ↔ -a < -b, from add_lt_add_iff_left _,
by simp at this; simp [this]

lemma neg_lt_zero : -a < 0 ↔ 0 < a :=
have -a < -0 ↔ 0 < a, from neg_lt_neg_iff,
by rwa neg_zero at this

lemma neg_pos : 0 < -a ↔ a < 0 :=
have -0 < -a ↔ a < 0, from neg_lt_neg_iff,
by rwa neg_zero at this

lemma neg_lt : -a < b ↔ -b < a :=
have -a < -(-b) ↔ -b < a, from neg_lt_neg_iff,
by rwa neg_neg at this

lemma lt_neg : a < -b ↔ b < -a :=
have -(-a) < -b ↔ b < -a, from neg_lt_neg_iff,
by rwa neg_neg at this

lemma sub_le_sub_iff_left (a : α) {b c : α} : a - b ≤ a - c ↔ c ≤ b :=
(add_le_add_iff_left _).trans neg_le_neg_iff

lemma sub_le_sub_iff_right (c : α) : a - c ≤ b - c ↔ a ≤ b :=
add_le_add_iff_right _

lemma sub_lt_sub_iff_left (a : α) {b c : α} : a - b < a - c ↔ c < b :=
(add_lt_add_iff_left _).trans neg_lt_neg_iff

lemma sub_lt_sub_iff_right (c : α) : a - c < b - c ↔ a < b :=
add_lt_add_iff_right _

lemma sub_lt_iff {a b c : α} : (a - b < c) ↔ (a < c + b) :=
iff.intro
  lt_add_of_sub_right_lt
  (assume h,
    have a + - b < (c + b) + - b, from add_lt_add_right h _,
    by simp * at *)

lemma lt_sub_iff {a b c : α} : (a < b - c) ↔ (a + c < b) :=
iff.intro
  (assume h,
    have a + c < (b - c) + c, from add_lt_add_right h _,
    by simp * at *)
  lt_sub_right_of_add_lt

@[simp] lemma sub_nonneg : 0 ≤ a - b ↔ b ≤ a :=
have a - a ≤ a - b ↔ b ≤ a, from sub_le_sub_iff_left a,
by rwa sub_self at this

@[simp] lemma sub_nonpos : a - b ≤ 0 ↔ a ≤ b :=
have a - b ≤ b - b ↔ a ≤ b, from sub_le_sub_iff_right b,
by rwa sub_self at this

@[simp] lemma sub_pos : 0 < a - b ↔ b < a :=
have a - a < a - b ↔ b < a, from sub_lt_sub_iff_left a,
by rwa sub_self at this

@[simp] lemma sub_lt_zero : a - b < 0 ↔ a < b :=
have a - b < b - b ↔ a < b, from sub_lt_sub_iff_right b,
by rwa sub_self at this

@[simp] lemma le_neg_add_iff_add_le : b ≤ -a + c ↔ a + b ≤ c :=
have -a + (a + b) ≤ -a + c ↔ a + b ≤ c, from add_le_add_iff_left _,
by rwa neg_add_cancel_left at this

lemma le_sub_left_iff_add_le : b ≤ c - a ↔ a + b ≤ c :=
by rw [sub_eq_add_neg, add_comm, le_neg_add_iff_add_le]

@[simp] lemma le_sub_right_iff_add_le : a ≤ c - b ↔ a + b ≤ c :=
by rw [le_sub_left_iff_add_le, add_comm]

@[simp] lemma neg_add_le_iff_le_add : -b + a ≤ c ↔ a ≤ b + c :=
have -b + a ≤ -b + (b + c) ↔ a ≤ b + c, from add_le_add_iff_left _,
by rwa neg_add_cancel_left at this

lemma sub_left_le_iff_le_add : a - b ≤ c ↔ a ≤ b + c :=
by rw [sub_eq_add_neg, add_comm, neg_add_le_iff_le_add]

@[simp] lemma sub_right_le_iff_le_add : a - c ≤ b ↔ a ≤ b + c :=
by rw [sub_left_le_iff_le_add, add_comm]

lemma neg_add_le_iff_le_add_right : -c + a ≤ b ↔ a ≤ b + c :=
by rw [neg_add_le_iff_le_add, add_comm]

@[simp] lemma neg_le_sub_iff_le_add : -b ≤ a - c ↔ c ≤ a + b :=
le_sub_right_iff_add_le.trans neg_add_le_iff_le_add_right

lemma neg_le_sub_iff_le_add_left : -a ≤ b - c ↔ c ≤ a + b :=
by rw [neg_le_sub_iff_le_add, add_comm]

lemma sub_le : a - b ≤ c ↔ a - c ≤ b :=
sub_left_le_iff_le_add.trans sub_right_le_iff_le_add.symm

@[simp] lemma lt_neg_add_iff_add_lt : b < -a + c ↔ a + b < c :=
have -a + (a + b) < -a + c ↔ a + b < c, from add_lt_add_iff_left _,
by rwa neg_add_cancel_left at this

lemma lt_sub_left_iff_add_lt : b < c - a ↔ a + b < c :=
by rw [sub_eq_add_neg, add_comm, lt_neg_add_iff_add_lt]

@[simp] lemma lt_sub_right_iff_add_lt : a < c - b ↔ a + b < c :=
by rw [lt_sub_left_iff_add_lt, add_comm]

@[simp] lemma neg_add_lt_iff_lt_add : -b + a < c ↔ a < b + c :=
have -b + a < -b + (b + c) ↔ a < b + c, from add_lt_add_iff_left _,
by rwa neg_add_cancel_left at this

lemma sub_left_lt_iff_lt_add : a - b < c ↔ a < b + c :=
by rw [sub_eq_add_neg, add_comm, neg_add_lt_iff_lt_add]

@[simp] lemma sub_right_lt_iff_lt_add : a - c < b ↔ a < b + c :=
by rw [sub_left_lt_iff_lt_add, add_comm]

lemma neg_add_lt_iff_lt_add_right : -c + a < b ↔ a < b + c :=
by rw [neg_add_lt_iff_lt_add, add_comm]

@[simp] lemma neg_lt_sub_iff_lt_add : -b < a - c ↔ c < a + b :=
lt_sub_right_iff_add_lt.trans neg_add_lt_iff_lt_add_right

lemma neg_lt_sub_iff_lt_add_left : -a < b - c ↔ c < a + b :=
by rw [neg_lt_sub_iff_lt_add, add_comm]

lemma sub_lt : a - b < c ↔ a - c < b :=
sub_left_lt_iff_lt_add.trans sub_right_lt_iff_lt_add.symm

lemma sub_le_self_iff (a : α) {b : α} : a - b ≤ a ↔ 0 ≤ b :=
sub_left_le_iff_le_add.trans (le_add_iff_nonneg_left _)

lemma sub_lt_self_iff (a : α) {b : α} : a - b < a ↔ 0 < b :=
sub_left_lt_iff_lt_add.trans (lt_add_iff_pos_left _)

end ordered_comm_group

-- This is not so much a new structure as a construction mechanism
-- for ordered groups
set_option old_structure_cmd true
class nonneg_comm_group (α : Type*) extends add_comm_group α :=
(nonneg : α → Prop)
(pos : α → Prop := λ a, nonneg a ∧ ¬ nonneg (neg a))
(pos_iff : ∀ a, pos a ↔ nonneg a ∧ ¬ nonneg (-a) . order_laws_tac)
(zero_nonneg : nonneg 0)
(add_nonneg : ∀ {a b}, nonneg a → nonneg b → nonneg (a + b))
(nonneg_antisymm : ∀ {a}, nonneg a → nonneg (-a) → a = 0)

namespace nonneg_comm_group
variable [s : nonneg_comm_group α]
include s

@[reducible] instance to_ordered_comm_group : ordered_comm_group α :=
{ s with
  le := λ a b, nonneg (b - a),
  lt := λ a b, pos (b - a),
  lt_iff_le_not_le := λ a b, by simp; rw [pos_iff]; simp,
  le_refl := λ a, by simp [zero_nonneg],
  le_trans := λ a b c nab nbc, by simp [-sub_eq_add_neg];
    rw ← sub_add_sub_cancel; exact add_nonneg nbc nab,
  le_antisymm := λ a b nab nba, eq_of_sub_eq_zero $
    nonneg_antisymm nba (by rw neg_sub; exact nab),
  add_le_add_left := λ a b nab c, by simpa [(≤), preorder.le] using nab,
  add_lt_add_left := λ a b nab c, by simpa [(<), preorder.lt] using nab }

theorem nonneg_def {a : α} : nonneg a ↔ 0 ≤ a :=
show _ ↔ nonneg _, by simp

theorem pos_def {a : α} : pos a ↔ 0 < a :=
show _ ↔ pos _, by simp

theorem not_zero_pos : ¬ pos (0 : α) :=
mt pos_def.1 (lt_irrefl _)

theorem zero_lt_iff_nonneg_nonneg {a : α} :
  0 < a ↔ nonneg a ∧ ¬ nonneg (-a) :=
pos_def.symm.trans (pos_iff α _)

theorem nonneg_total_iff :
  (∀ a : α, nonneg a ∨ nonneg (-a)) ↔
  (∀ a b : α, a ≤ b ∨ b ≤ a) :=
⟨λ h a b, by have := h (b - a); rwa [neg_sub] at this,
 λ h a, by rw [nonneg_def, nonneg_def, neg_nonneg]; apply h⟩

def to_decidable_linear_ordered_comm_group
  [decidable_pred (@nonneg α _)]
  (nonneg_total : ∀ a : α, nonneg a ∨ nonneg (-a))
  : decidable_linear_ordered_comm_group α :=
{ @nonneg_comm_group.to_ordered_comm_group _ s with
  le := (≤),
  lt := (<),
  lt_iff_le_not_le := @lt_iff_le_not_le _ _,
  le_refl := @le_refl _ _,
  le_trans := @le_trans _ _,
  le_antisymm := @le_antisymm _ _,
  le_total := nonneg_total_iff.1 nonneg_total,
  decidable_le := by apply_instance,
  decidable_eq := by apply_instance,
  decidable_lt := by apply_instance }

end nonneg_comm_group
