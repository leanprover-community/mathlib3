/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Yury Kudryashov, Rémy Degenne
-/
import data.set.intervals.basic
import algebra.order.group.abs

/-! ### Lemmas about arithmetic operations and intervals. -/

variables {α : Type*}

namespace set

section ordered_comm_group

variables [ordered_comm_group α] {a b c d : α}

/-! `inv_mem_Ixx_iff`, `sub_mem_Ixx_iff` -/
@[to_additive] lemma inv_mem_Icc_iff : a⁻¹ ∈ set.Icc c d ↔ a ∈ set.Icc (d⁻¹) (c⁻¹) :=
(and_comm _ _).trans $ and_congr inv_le' le_inv'
@[to_additive] lemma inv_mem_Ico_iff : a⁻¹ ∈ set.Ico c d ↔ a ∈ set.Ioc (d⁻¹) (c⁻¹) :=
(and_comm _ _).trans $ and_congr inv_lt' le_inv'
@[to_additive] lemma inv_mem_Ioc_iff : a⁻¹ ∈ set.Ioc c d ↔ a ∈ set.Ico (d⁻¹) (c⁻¹) :=
(and_comm _ _).trans $ and_congr inv_le' lt_inv'
@[to_additive] lemma inv_mem_Ioo_iff : a⁻¹ ∈ set.Ioo c d ↔ a ∈ set.Ioo (d⁻¹) (c⁻¹) :=
(and_comm _ _).trans $ and_congr inv_lt' lt_inv'

end ordered_comm_group

section ordered_add_comm_group

variables [ordered_add_comm_group α] {a b c d : α}

/-! `add_mem_Ixx_iff_left` -/
lemma add_mem_Icc_iff_left : a + b ∈ set.Icc c d ↔ a ∈ set.Icc (c - b) (d - b) :=
(and_congr sub_le_iff_le_add le_sub_iff_add_le).symm
lemma add_mem_Ico_iff_left : a + b ∈ set.Ico c d ↔ a ∈ set.Ico (c - b) (d - b) :=
(and_congr sub_le_iff_le_add lt_sub_iff_add_lt).symm
lemma add_mem_Ioc_iff_left : a + b ∈ set.Ioc c d ↔ a ∈ set.Ioc (c - b) (d - b) :=
(and_congr sub_lt_iff_lt_add le_sub_iff_add_le).symm
lemma add_mem_Ioo_iff_left : a + b ∈ set.Ioo c d ↔ a ∈ set.Ioo (c - b) (d - b) :=
(and_congr sub_lt_iff_lt_add lt_sub_iff_add_lt).symm

/-! `add_mem_Ixx_iff_right` -/
lemma add_mem_Icc_iff_right : a + b ∈ set.Icc c d ↔ b ∈ set.Icc (c - a) (d - a) :=
(and_congr sub_le_iff_le_add' le_sub_iff_add_le').symm
lemma add_mem_Ico_iff_right : a + b ∈ set.Ico c d ↔ b ∈ set.Ico (c - a) (d - a) :=
(and_congr sub_le_iff_le_add' lt_sub_iff_add_lt').symm
lemma add_mem_Ioc_iff_right : a + b ∈ set.Ioc c d ↔ b ∈ set.Ioc (c - a) (d - a) :=
(and_congr sub_lt_iff_lt_add' le_sub_iff_add_le').symm
lemma add_mem_Ioo_iff_right : a + b ∈ set.Ioo c d ↔ b ∈ set.Ioo (c - a) (d - a) :=
(and_congr sub_lt_iff_lt_add' lt_sub_iff_add_lt').symm

/-! `sub_mem_Ixx_iff_left` -/
lemma sub_mem_Icc_iff_left : a - b ∈ set.Icc c d ↔ a ∈ set.Icc (c + b) (d + b) :=
and_congr le_sub_iff_add_le sub_le_iff_le_add
lemma sub_mem_Ico_iff_left : a - b ∈ set.Ico c d ↔ a ∈ set.Ico (c + b) (d + b) :=
and_congr le_sub_iff_add_le sub_lt_iff_lt_add
lemma sub_mem_Ioc_iff_left : a - b ∈ set.Ioc c d ↔ a ∈ set.Ioc (c + b) (d + b) :=
and_congr lt_sub_iff_add_lt sub_le_iff_le_add
lemma sub_mem_Ioo_iff_left : a - b ∈ set.Ioo c d ↔ a ∈ set.Ioo (c + b) (d + b) :=
and_congr lt_sub_iff_add_lt sub_lt_iff_lt_add

/-! `sub_mem_Ixx_iff_right` -/
lemma sub_mem_Icc_iff_right : a - b ∈ set.Icc c d ↔ b ∈ set.Icc (a - d) (a - c) :=
(and_comm _ _).trans $ and_congr sub_le_comm le_sub_comm
lemma sub_mem_Ico_iff_right : a - b ∈ set.Ico c d ↔ b ∈ set.Ioc (a - d) (a - c) :=
(and_comm _ _).trans $ and_congr sub_lt_comm le_sub_comm
lemma sub_mem_Ioc_iff_right : a - b ∈ set.Ioc c d ↔ b ∈ set.Ico (a - d) (a - c) :=
(and_comm _ _).trans $ and_congr sub_le_comm lt_sub_comm
lemma sub_mem_Ioo_iff_right : a - b ∈ set.Ioo c d ↔ b ∈ set.Ioo (a - d) (a - c) :=
(and_comm _ _).trans $ and_congr sub_lt_comm lt_sub_comm

-- I think that symmetric intervals deserve attention and API: they arise all the time,
-- for instance when considering metric balls in `ℝ`.
lemma mem_Icc_iff_abs_le {R : Type*} [linear_ordered_add_comm_group R] {x y z : R} :
  |x - y| ≤ z ↔ y ∈ Icc (x - z) (x + z) :=
abs_le.trans $ (and_comm _ _).trans $ and_congr sub_le_comm neg_le_sub_iff_le_add

end ordered_add_comm_group

section linear_ordered_add_comm_group

variables [linear_ordered_add_comm_group α]

/-- If we remove a smaller interval from a larger, the result is nonempty -/
lemma nonempty_Ico_sdiff {x dx y dy : α} (h : dy < dx) (hx : 0 < dx) :
  nonempty ↥(Ico x (x + dx) \ Ico y (y + dy)) :=
begin
  cases lt_or_le x y with h' h',
  { use x, simp [*, not_le.2 h'] },
  { use max x (x + dy), simp [*, le_refl] }
end

end linear_ordered_add_comm_group

end set
