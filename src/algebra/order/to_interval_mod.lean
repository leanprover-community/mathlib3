/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import algebra.module.basic
import algebra.order.archimedean
import algebra.periodic
import data.int.succ_pred
import group_theory.quotient_group
import order.circular
/-!
# Reducing to an interval modulo its length

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines operations that reduce a number (in an `archimedean`
`linear_ordered_add_comm_group`) to a number in a given interval, modulo the length of that
interval.

## Main definitions

* `to_Ico_div a hb x` (where `hb : 0 < b`): The unique integer such that this multiple of `b`,
  subtracted from `x`, is in `Ico a (a + b)`.
* `to_Ico_mod a hb x` (where `hb : 0 < b`): Reduce `x` to the interval `Ico a (a + b)`.
* `to_Ioc_div a hb x` (where `hb : 0 < b`): The unique integer such that this multiple of `b`,
  subtracted from `x`, is in `Ioc a (a + b)`.
* `to_Ioc_mod a hb x` (where `hb : 0 < b`): Reduce `x` to the interval `Ioc a (a + b)`.

-/

noncomputable theory

section linear_ordered_add_comm_group

variables {α : Type*} [linear_ordered_add_comm_group α] [hα : archimedean α]
include hα

/--
The unique integer such that this multiple of `b`, subtracted from `x`, is in `Ico a (a + b)`. -/
def to_Ico_div (a : α) {b : α} (hb : 0 < b) (x : α) : ℤ :=
(exists_unique_sub_zsmul_mem_Ico hb x a).some

lemma sub_to_Ico_div_zsmul_mem_Ico (a : α) {b : α} (hb : 0 < b) (x : α) :
  x - to_Ico_div a hb x • b ∈ set.Ico a (a + b) :=
(exists_unique_sub_zsmul_mem_Ico hb x a).some_spec.1

lemma eq_to_Ico_div_of_sub_zsmul_mem_Ico {a b x : α} (hb : 0 < b) {y : ℤ}
  (hy : x - y • b ∈ set.Ico a (a + b)) : y = to_Ico_div a hb x :=
(exists_unique_sub_zsmul_mem_Ico hb x a).some_spec.2 y hy

/--
The unique integer such that this multiple of `b`, subtracted from `x`, is in `Ioc a (a + b)`. -/
def to_Ioc_div (a : α) {b : α} (hb : 0 < b) (x : α) : ℤ :=
(exists_unique_sub_zsmul_mem_Ioc hb x a).some

lemma sub_to_Ioc_div_zsmul_mem_Ioc (a : α) {b : α} (hb : 0 < b) (x : α) :
  x - to_Ioc_div a hb x • b ∈ set.Ioc a (a + b) :=
(exists_unique_sub_zsmul_mem_Ioc hb x a).some_spec.1

lemma eq_to_Ioc_div_of_sub_zsmul_mem_Ioc {a b x : α} (hb : 0 < b) {y : ℤ}
  (hy : x - y • b ∈ set.Ioc a (a + b)) : y = to_Ioc_div a hb x :=
(exists_unique_sub_zsmul_mem_Ioc hb x a).some_spec.2 y hy

/-- Reduce `x` to the interval `Ico a (a + b)`. -/
def to_Ico_mod (a : α) {b : α} (hb : 0 < b) (x : α) : α := x - to_Ico_div a hb x • b

/-- Reduce `x` to the interval `Ioc a (a + b)`. -/
def to_Ioc_mod (a : α) {b : α} (hb : 0 < b) (x : α) : α := x - to_Ioc_div a hb x • b

lemma to_Ico_mod_mem_Ico (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_mod a hb x ∈ set.Ico a (a + b) :=
sub_to_Ico_div_zsmul_mem_Ico a hb x

lemma to_Ico_mod_mem_Ico' {b : α} (hb : 0 < b) (x : α) :
  to_Ico_mod 0 hb x ∈ set.Ico 0 b :=
by { convert to_Ico_mod_mem_Ico 0 hb x, exact (zero_add b).symm, }

lemma to_Ioc_mod_mem_Ioc (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_mod a hb x ∈ set.Ioc a (a + b) :=
sub_to_Ioc_div_zsmul_mem_Ioc a hb x

lemma left_le_to_Ico_mod (a : α) {b : α} (hb : 0 < b) (x : α) : a ≤ to_Ico_mod a hb x :=
(set.mem_Ico.1 (to_Ico_mod_mem_Ico a hb x)).1

lemma left_lt_to_Ioc_mod (a : α) {b : α} (hb : 0 < b) (x : α) : a < to_Ioc_mod a hb x :=
(set.mem_Ioc.1 (to_Ioc_mod_mem_Ioc a hb x)).1

lemma to_Ico_mod_lt_right (a : α) {b : α} (hb : 0 < b) (x : α) : to_Ico_mod a hb x < a + b :=
(set.mem_Ico.1 (to_Ico_mod_mem_Ico a hb x)).2

lemma to_Ioc_mod_le_right (a : α) {b : α} (hb : 0 < b) (x : α) : to_Ioc_mod a hb x ≤ a + b :=
(set.mem_Ioc.1 (to_Ioc_mod_mem_Ioc a hb x)).2

@[simp] lemma self_sub_to_Ico_div_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) :
  x - to_Ico_div a hb x • b = to_Ico_mod a hb x :=
rfl

@[simp] lemma self_sub_to_Ioc_div_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) :
  x - to_Ioc_div a hb x • b = to_Ioc_mod a hb x :=
rfl

@[simp] lemma to_Ico_div_zsmul_sub_self (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_div a hb x • b - x = -to_Ico_mod a hb x :=
by rw [to_Ico_mod, neg_sub]

@[simp] lemma to_Ioc_div_zsmul_sub_self (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_div a hb x • b - x = -to_Ioc_mod a hb x :=
by rw [to_Ioc_mod, neg_sub]

@[simp] lemma to_Ico_mod_sub_self (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_mod a hb x - x = -to_Ico_div a hb x • b :=
by rw [to_Ico_mod, sub_sub_cancel_left, neg_smul]

@[simp] lemma to_Ioc_mod_sub_self (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_mod a hb x - x = -to_Ioc_div a hb x • b :=
by rw [to_Ioc_mod, sub_sub_cancel_left, neg_smul]

@[simp] lemma self_sub_to_Ico_mod (a : α) {b : α} (hb : 0 < b) (x : α) :
  x - to_Ico_mod a hb x = to_Ico_div a hb x • b :=
by rw [to_Ico_mod, sub_sub_cancel]

@[simp] lemma self_sub_to_Ioc_mod (a : α) {b : α} (hb : 0 < b) (x : α) :
  x - to_Ioc_mod a hb x = to_Ioc_div a hb x • b :=
by rw [to_Ioc_mod, sub_sub_cancel]

@[simp] lemma to_Ico_mod_add_to_Ico_div_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_mod a hb x + to_Ico_div a hb x • b = x :=
by rw [to_Ico_mod, sub_add_cancel]

@[simp] lemma to_Ioc_mod_add_to_Ioc_div_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_mod a hb x + to_Ioc_div a hb x • b = x :=
by rw [to_Ioc_mod, sub_add_cancel]

@[simp] lemma to_Ico_div_zsmul_sub_to_Ico_mod (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_div a hb x • b + to_Ico_mod a hb x = x :=
by rw [add_comm, to_Ico_mod_add_to_Ico_div_zsmul]

@[simp] lemma to_Ioc_div_zsmul_sub_to_Ioc_mod (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_div a hb x • b + to_Ioc_mod a hb x = x :=
by rw [add_comm, to_Ioc_mod_add_to_Ioc_div_zsmul]

lemma to_Ico_mod_eq_iff {a b x y : α} (hb : 0 < b) :
  to_Ico_mod a hb x = y ↔ y ∈ set.Ico a (a + b) ∧ ∃ z : ℤ, x = y + z • b :=
begin
  refine ⟨λ h, ⟨h ▸ to_Ico_mod_mem_Ico a hb x,
                to_Ico_div a hb x,
                h ▸ (to_Ico_mod_add_to_Ico_div_zsmul _ _ _).symm⟩,
          λ h, _⟩,
  rcases h with ⟨hy, z, hz⟩,
  rw ←sub_eq_iff_eq_add at hz,
  subst hz,
  rw eq_to_Ico_div_of_sub_zsmul_mem_Ico hb hy,
  refl
end

lemma to_Ioc_mod_eq_iff {a b x y : α} (hb : 0 < b) :
  to_Ioc_mod a hb x = y ↔ y ∈ set.Ioc a (a + b) ∧ ∃ z : ℤ, x = y + z • b :=
begin
  refine ⟨λ h, ⟨h ▸ to_Ioc_mod_mem_Ioc a hb x,
                to_Ioc_div a hb x,
                h ▸ (to_Ioc_mod_add_to_Ioc_div_zsmul _ hb _).symm⟩,
          λ h, _⟩,
  rcases h with ⟨hy, z, hz⟩,
  rw ←sub_eq_iff_eq_add at hz,
  subst hz,
  rw eq_to_Ioc_div_of_sub_zsmul_mem_Ioc hb hy,
  refl
end

@[simp] lemma to_Ico_div_apply_left (a : α) {b : α} (hb : 0 < b) : to_Ico_div a hb a = 0 :=
begin
  refine (eq_to_Ico_div_of_sub_zsmul_mem_Ico hb _).symm,
  simp [hb]
end

@[simp] lemma to_Ioc_div_apply_left (a : α) {b : α} (hb : 0 < b) : to_Ioc_div a hb a = -1 :=
begin
  refine (eq_to_Ioc_div_of_sub_zsmul_mem_Ioc hb _).symm,
  simp [hb],
end

@[simp] lemma to_Ico_mod_apply_left (a : α) {b : α} (hb : 0 < b) : to_Ico_mod a hb a = a :=
begin
  rw [to_Ico_mod_eq_iff hb, set.left_mem_Ico],
  refine ⟨lt_add_of_pos_right _ hb, 0, _⟩,
  simp
end

@[simp] lemma to_Ioc_mod_apply_left (a : α) {b : α} (hb : 0 < b) : to_Ioc_mod a hb a = a + b :=
begin
  rw [to_Ioc_mod_eq_iff hb, set.right_mem_Ioc],
  refine ⟨lt_add_of_pos_right _ hb, -1, _⟩,
  simp
end

lemma to_Ico_div_apply_right (a : α) {b : α} (hb : 0 < b) :
  to_Ico_div a hb (a + b) = 1 :=
begin
  refine (eq_to_Ico_div_of_sub_zsmul_mem_Ico hb _).symm,
  simp [hb]
end

lemma to_Ioc_div_apply_right (a : α) {b : α} (hb : 0 < b) :
  to_Ioc_div a hb (a + b) = 0 :=
begin
  refine (eq_to_Ioc_div_of_sub_zsmul_mem_Ioc hb _).symm,
  simp [hb]
end

lemma to_Ico_mod_apply_right (a : α) {b : α} (hb : 0 < b) : to_Ico_mod a hb (a + b) = a :=
begin
  rw [to_Ico_mod_eq_iff hb, set.left_mem_Ico],
  refine ⟨lt_add_of_pos_right _ hb, 1, _⟩,
  simp
end

lemma to_Ioc_mod_apply_right (a : α) {b : α} (hb : 0 < b) :
  to_Ioc_mod a hb (a + b) = a + b :=
begin
  rw [to_Ioc_mod_eq_iff hb, set.right_mem_Ioc],
  refine ⟨lt_add_of_pos_right _ hb, 0, _⟩,
  simp
end

@[simp] lemma to_Ico_div_add_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
  to_Ico_div a hb (x + m • b) = to_Ico_div a hb x + m :=
begin
  refine (eq_to_Ico_div_of_sub_zsmul_mem_Ico hb _).symm,
  convert sub_to_Ico_div_zsmul_mem_Ico a hb x using 1,
  simp [add_smul],
end

@[simp] lemma to_Ico_div_add_zsmul' (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
  to_Ico_div (a + m • b) hb x = to_Ico_div a hb x - m :=
begin
  refine (eq_to_Ico_div_of_sub_zsmul_mem_Ico hb _).symm,
  rw [sub_smul, (sub_add _ _ _).symm, add_right_comm],
  simpa using (sub_to_Ico_div_zsmul_mem_Ico a hb x),
end

@[simp] lemma to_Ioc_div_add_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
  to_Ioc_div a hb (x + m • b) = to_Ioc_div a hb x + m :=
begin
  refine (eq_to_Ioc_div_of_sub_zsmul_mem_Ioc hb _).symm,
  convert sub_to_Ioc_div_zsmul_mem_Ioc a hb x using 1,
  simp [add_smul]
end

@[simp] lemma to_Ioc_div_add_zsmul' (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
  to_Ioc_div (a + m • b) hb x = to_Ioc_div a hb x - m :=
begin
  refine (eq_to_Ioc_div_of_sub_zsmul_mem_Ioc hb _).symm,
  rw [sub_smul, (sub_add _ _ _).symm, add_right_comm],
  simpa using (sub_to_Ioc_div_zsmul_mem_Ioc a hb x),
end

@[simp] lemma to_Ico_div_zsmul_add (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
  to_Ico_div a hb (m • b + x) = m + to_Ico_div a hb x :=
by rw [add_comm, to_Ico_div_add_zsmul, add_comm]

@[simp] lemma to_Ioc_div_zsmul_add (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
  to_Ioc_div a hb (m • b + x) = to_Ioc_div a hb x + m :=
by rw [add_comm, to_Ioc_div_add_zsmul, add_comm]

@[simp] lemma to_Ico_div_sub_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
  to_Ico_div a hb (x - m • b) = to_Ico_div a hb x - m :=
by rw [sub_eq_add_neg, ←neg_smul, to_Ico_div_add_zsmul, sub_eq_add_neg]

@[simp] lemma to_Ioc_div_sub_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
  to_Ioc_div a hb (x - m • b) = to_Ioc_div a hb x - m :=
by rw [sub_eq_add_neg, ←neg_smul, to_Ioc_div_add_zsmul, sub_eq_add_neg]

@[simp] lemma to_Ico_div_add_right (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_div a hb (x + b) = to_Ico_div a hb x + 1 :=
begin
  convert to_Ico_div_add_zsmul a hb x 1,
  exact (one_zsmul _).symm
end

@[simp] lemma to_Ioc_div_add_right (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_div a hb (x + b) = to_Ioc_div a hb x + 1 :=
begin
  convert to_Ioc_div_add_zsmul a hb x 1,
  exact (one_zsmul _).symm
end

@[simp] lemma to_Ico_div_add_left (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_div a hb (b + x) = to_Ico_div a hb x + 1 :=
by rw [add_comm, to_Ico_div_add_right]

@[simp] lemma to_Ioc_div_add_left (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_div a hb (b + x) = to_Ioc_div a hb x + 1 :=
by rw [add_comm, to_Ioc_div_add_right]

@[simp] lemma to_Ico_div_sub (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_div a hb (x - b) = to_Ico_div a hb x - 1 :=
begin
  convert to_Ico_div_sub_zsmul a hb x 1,
  exact (one_zsmul _).symm
end

@[simp] lemma to_Ioc_div_sub (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_div a hb (x - b) = to_Ioc_div a hb x - 1 :=
begin
  convert to_Ioc_div_sub_zsmul a hb x 1,
  exact (one_zsmul _).symm
end

lemma to_Ico_div_sub' (a : α) {b : α} (hb : 0 < b) (x y : α) :
  to_Ico_div a hb (x - y) = to_Ico_div (a + y) hb x :=
begin
  rw eq_comm,
  apply eq_to_Ico_div_of_sub_zsmul_mem_Ico,
  rw [←sub_right_comm, set.sub_mem_Ico_iff_left, add_right_comm],
  exact sub_to_Ico_div_zsmul_mem_Ico (a + y) hb x,
end

lemma to_Ioc_div_sub' (a : α) {b : α} (hb : 0 < b) (x y : α) :
  to_Ioc_div a hb (x - y) = to_Ioc_div (a + y) hb x :=
begin
  rw eq_comm,
  apply eq_to_Ioc_div_of_sub_zsmul_mem_Ioc,
  rw [←sub_right_comm, set.sub_mem_Ioc_iff_left, add_right_comm],
  exact sub_to_Ioc_div_zsmul_mem_Ioc (a + y) hb x,
end

lemma to_Ico_div_eq_to_Ico_div_zero (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_div a hb x = to_Ico_div 0 hb (x - a) :=
by rw [to_Ico_div_sub', zero_add]

lemma to_Ioc_div_eq_to_Ioc_div_zero (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_div a hb x = to_Ioc_div 0 hb (x - a) :=
by rw [to_Ioc_div_sub', zero_add]

lemma to_Ico_div_add_right' (a : α) {b : α} (hb : 0 < b) (x y : α) :
  to_Ico_div a hb (x + y) = to_Ico_div (a - y) hb x :=
by rw [←sub_neg_eq_add, to_Ico_div_sub', sub_eq_add_neg]

lemma to_Ioc_div_add_right' (a : α) {b : α} (hb : 0 < b) (x y : α) :
  to_Ioc_div a hb (x + y) = to_Ioc_div (a - y) hb x :=
by rw [←sub_neg_eq_add, to_Ioc_div_sub', sub_eq_add_neg]

lemma to_Ico_div_neg (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_div a hb (-x) = -(to_Ioc_div (-a) hb x + 1) :=
begin
  suffices : to_Ico_div a hb (-x) = -(to_Ioc_div (-(a + b)) hb x),
  { rwa [neg_add, ←sub_eq_add_neg, ←to_Ioc_div_add_right', to_Ioc_div_add_right] at this },
  rw [← neg_eq_iff_eq_neg],
  apply eq_to_Ioc_div_of_sub_zsmul_mem_Ioc,
  obtain ⟨hc, ho⟩ := sub_to_Ico_div_zsmul_mem_Ico a hb (-x),
  rw [←neg_lt_neg_iff, neg_sub' (-x), neg_neg, ←neg_smul] at ho,
  rw [←neg_le_neg_iff, neg_sub' (-x), neg_neg, ←neg_smul] at hc,
  refine ⟨ho, hc.trans_eq _⟩,
  rw [neg_add, neg_add_cancel_right],
end

lemma to_Ioc_div_neg (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_div a hb (-x) = -(to_Ico_div (-a) hb x + 1) :=
by rw [←neg_neg x, to_Ico_div_neg, neg_neg, neg_neg, neg_add', neg_neg, add_sub_cancel]

@[simp] lemma to_Ico_mod_add_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
  to_Ico_mod a hb (x + m • b) = to_Ico_mod a hb x :=
begin
  rw [to_Ico_mod, to_Ico_div_add_zsmul, to_Ico_mod, add_smul],
  abel
end

@[simp] lemma to_Ioc_mod_add_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
  to_Ioc_mod a hb (x + m • b) = to_Ioc_mod a hb x :=
begin
  rw [to_Ioc_mod, to_Ioc_div_add_zsmul, to_Ioc_mod, add_smul],
  abel
end

@[simp] lemma to_Ico_mod_zsmul_add (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
  to_Ico_mod a hb (m • b + x) = to_Ico_mod a hb x :=
by rw [add_comm, to_Ico_mod_add_zsmul]

@[simp] lemma to_Ioc_mod_zsmul_add (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
  to_Ioc_mod a hb (m • b + x) = to_Ioc_mod a hb x :=
by rw [add_comm, to_Ioc_mod_add_zsmul]

@[simp] lemma to_Ico_mod_sub_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
  to_Ico_mod a hb (x - m • b) = to_Ico_mod a hb x :=
by rw [sub_eq_add_neg, ←neg_smul, to_Ico_mod_add_zsmul]

@[simp] lemma to_Ioc_mod_sub_zsmul (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
  to_Ioc_mod a hb (x - m • b) = to_Ioc_mod a hb x :=
by rw [sub_eq_add_neg, ←neg_smul, to_Ioc_mod_add_zsmul]

@[simp] lemma to_Ico_mod_add_right (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_mod a hb (x + b) = to_Ico_mod a hb x :=
begin
  convert to_Ico_mod_add_zsmul a hb x 1,
  exact (one_zsmul _).symm
end

@[simp] lemma to_Ioc_mod_add_right (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_mod a hb (x + b) = to_Ioc_mod a hb x :=
begin
  convert to_Ioc_mod_add_zsmul a hb x 1,
  exact (one_zsmul _).symm
end

@[simp] lemma to_Ico_mod_add_left (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_mod a hb (b + x) = to_Ico_mod a hb x :=
by rw [add_comm, to_Ico_mod_add_right]

@[simp] lemma to_Ioc_mod_add_left (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_mod a hb (b + x) = to_Ioc_mod a hb x :=
by rw [add_comm, to_Ioc_mod_add_right]

@[simp] lemma to_Ico_mod_sub (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_mod a hb (x - b) = to_Ico_mod a hb x :=
begin
  convert to_Ico_mod_sub_zsmul a hb x 1,
  exact (one_zsmul _).symm
end

@[simp] lemma to_Ioc_mod_sub (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_mod a hb (x - b) = to_Ioc_mod a hb x :=
begin
  convert to_Ioc_mod_sub_zsmul a hb x 1,
  exact (one_zsmul _).symm
end

lemma to_Ico_mod_sub' (a : α) {b : α} (hb : 0 < b) (x y : α) :
  to_Ico_mod a hb (x - y) = to_Ico_mod (a + y) hb x - y :=
by simp_rw [to_Ico_mod, to_Ico_div_sub', sub_right_comm]

lemma to_Ioc_mod_sub' (a : α) {b : α} (hb : 0 < b) (x y : α) :
  to_Ioc_mod a hb (x - y) = to_Ioc_mod (a + y) hb x - y :=
by simp_rw [to_Ioc_mod, to_Ioc_div_sub', sub_right_comm]

lemma to_Ico_mod_add_right' (a : α) {b : α} (hb : 0 < b) (x y : α) :
  to_Ico_mod a hb (x + y) = to_Ico_mod (a - y) hb x + y :=
by simp_rw [to_Ico_mod, to_Ico_div_add_right', sub_add_eq_add_sub]

lemma to_Ioc_mod_add_right' (a : α) {b : α} (hb : 0 < b) (x y : α) :
  to_Ioc_mod a hb (x + y) = to_Ioc_mod (a - y) hb x + y :=
by simp_rw [to_Ioc_mod, to_Ioc_div_add_right', sub_add_eq_add_sub]

lemma to_Ico_mod_neg (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_mod a hb (-x) = b - to_Ioc_mod (-a) hb x :=
begin
  simp_rw [to_Ico_mod, to_Ioc_mod, to_Ico_div_neg, neg_smul, add_smul],
  abel,
end

lemma to_Ioc_mod_neg (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_mod a hb (-x) = b - to_Ico_mod (-a) hb x :=
begin
  simp_rw [to_Ioc_mod, to_Ico_mod, to_Ioc_div_neg, neg_smul, add_smul],
  abel,
end

lemma to_Ico_mod_eq_to_Ico_mod (a : α) {b x y : α} (hb : 0 < b) :
  to_Ico_mod a hb x = to_Ico_mod a hb y ↔ ∃ z : ℤ, y - x = z • b :=
begin
  refine ⟨λ h, ⟨to_Ico_div a hb y - to_Ico_div a hb x, _⟩, λ h, _⟩,
  { conv_lhs { rw [←to_Ico_mod_add_to_Ico_div_zsmul a hb x,
                   ←to_Ico_mod_add_to_Ico_div_zsmul a hb y] },
    rw [h, sub_smul],
    abel },
  { rcases h with ⟨z, hz⟩,
    rw sub_eq_iff_eq_add at hz,
    rw [hz, to_Ico_mod_zsmul_add] }
end

lemma to_Ioc_mod_eq_to_Ioc_mod (a : α) {b x y : α} (hb : 0 < b) :
  to_Ioc_mod a hb x = to_Ioc_mod a hb y ↔ ∃ z : ℤ, y - x = z • b :=
begin
  refine ⟨λ h, ⟨to_Ioc_div a hb y - to_Ioc_div a hb x, _⟩, λ h, _⟩,
  { conv_lhs { rw [←to_Ioc_mod_add_to_Ioc_div_zsmul a hb x,
                   ←to_Ioc_mod_add_to_Ioc_div_zsmul a hb y] },
    rw [h, sub_smul],
    abel },
  { rcases h with ⟨z, hz⟩,
    rw sub_eq_iff_eq_add at hz,
    rw [hz, to_Ioc_mod_zsmul_add] }
end

/-! ### Links between the `Ico` and `Ioc` variants applied to the same element -/

section Ico_Ioc

variables (a : α) {b c p : α} (hb : 0 < b) (hp : 0 < p) (x : α)

omit hα

-- TODO: The argument order to `mem_Ioo_mod` is terrible. `a` and `x` play analogous roles, but `b`
-- has nothing to do with `a`
/-- `mem_Ioo_mod a b x` means that `x` lies in the open interval `(a, a + b)` modulo `b`.
Equivalently (as shown below), `x` is not congruent to `a` modulo `b`, or `to_Ico_mod a hb` agrees
with `to_Ioc_mod a hb` at `x`, or `to_Ico_div a hb` agrees with `to_Ioc_div a hb` at `x`. -/
def mem_Ioo_mod (b x : α) : Prop := ∃ z : ℤ, x - z • b ∈ set.Ioo a (a + b)
include hα

lemma tfae_mem_Ioo_mod :
  tfae [mem_Ioo_mod a b x,
    to_Ico_mod a hb x = to_Ioc_mod a hb x,
    to_Ico_mod a hb x + b ≠ to_Ioc_mod a hb x,
    to_Ico_mod a hb x ≠ a] :=
begin
  tfae_have : 1 → 2,
  { exact λ ⟨i, hi⟩,
      ((to_Ico_mod_eq_iff hb).2 ⟨set.Ioo_subset_Ico_self hi, i, (sub_add_cancel x _).symm⟩).trans
      ((to_Ioc_mod_eq_iff hb).2 ⟨set.Ioo_subset_Ioc_self hi, i, (sub_add_cancel x _).symm⟩).symm },
  tfae_have : 2 → 3,
  { intro h, rw [h, ne, add_right_eq_self], exact hb.ne' },
  tfae_have : 3 → 4,
  { refine mt (λ h, _),
    rw [h, eq_comm, to_Ioc_mod_eq_iff, set.right_mem_Ioc],
    refine ⟨lt_add_of_pos_right a hb, to_Ico_div a hb x - 1, _⟩,
    rw [sub_one_zsmul, add_add_add_comm, add_right_neg, add_zero],
    conv_lhs { rw [← to_Ico_mod_add_to_Ico_div_zsmul a hb x, h] } },
  tfae_have : 4 → 1,
  { have h' := to_Ico_mod_mem_Ico a hb x, exact λ h, ⟨_, h'.1.lt_of_ne' h, h'.2⟩ },
  tfae_finish,
end

variables {a x}

lemma mem_Ioo_mod_iff_to_Ico_mod_eq_to_Ioc_mod :
  mem_Ioo_mod a b x ↔ to_Ico_mod a hb x = to_Ioc_mod a hb x := (tfae_mem_Ioo_mod a hb x).out 0 1
lemma mem_Ioo_mod_iff_to_Ico_mod_add_period_ne_to_Ioc_mod :
  mem_Ioo_mod a b x ↔ to_Ico_mod a hb x + b ≠ to_Ioc_mod a hb x := (tfae_mem_Ioo_mod a hb x).out 0 2
lemma mem_Ioo_mod_iff_to_Ico_mod_ne_left :
  mem_Ioo_mod a b x ↔ to_Ico_mod a hb x ≠ a := (tfae_mem_Ioo_mod a hb x).out 0 3

alias mem_Ioo_mod_iff_to_Ico_mod_eq_to_Ioc_mod ↔ mem_Ioo_mod.to_Ico_mod_eq_to_Ioc_mod _

lemma not_mem_Ioo_mod_iff_to_Ico_mod_add_period_eq_to_Ioc_mod :
  ¬mem_Ioo_mod a b x ↔ to_Ico_mod a hb x + b = to_Ioc_mod a hb x :=
(mem_Ioo_mod_iff_to_Ico_mod_add_period_ne_to_Ioc_mod hb).not_left

lemma not_mem_Ioo_mod_iff_to_Ico_mod_eq_left : ¬mem_Ioo_mod a b x ↔ to_Ico_mod a hb x = a :=
(mem_Ioo_mod_iff_to_Ico_mod_ne_left hb).not_left

lemma mem_Ioo_mod_iff_to_Ioc_mod_ne_right : mem_Ioo_mod a b x ↔ to_Ioc_mod a hb x ≠ a + b :=
begin
  rw [mem_Ioo_mod_iff_to_Ico_mod_eq_to_Ioc_mod, to_Ico_mod_eq_iff hb],
  obtain ⟨h₁, h₂⟩ := to_Ioc_mod_mem_Ioc a hb x,
  exact ⟨λ h, h.1.2.ne, λ h, ⟨⟨h₁.le, h₂.lt_of_ne h⟩, _,
    (to_Ioc_mod_add_to_Ioc_div_zsmul _ _ _).symm⟩⟩,
end

lemma not_mem_Ioo_mod_iff_to_Ioc_eq_right : ¬mem_Ioo_mod a b x ↔ to_Ioc_mod a hb x = a + b :=
(mem_Ioo_mod_iff_to_Ioc_mod_ne_right hb).not_left

lemma mem_Ioo_mod_iff_to_Ico_div_eq_to_Ioc_div :
  mem_Ioo_mod a b x ↔ to_Ico_div a hb x = to_Ioc_div a hb x :=
by rw [mem_Ioo_mod_iff_to_Ico_mod_eq_to_Ioc_mod hb,
       to_Ico_mod, to_Ioc_mod, sub_right_inj, (zsmul_strict_mono_left hb).injective.eq_iff]

lemma mem_Ioo_mod_iff_to_Ico_div_ne_to_Ioc_div_add_one :
  mem_Ioo_mod a b x ↔ to_Ico_div a hb x ≠ to_Ioc_div a hb x + 1 :=
by rw [mem_Ioo_mod_iff_to_Ico_mod_add_period_ne_to_Ioc_mod hb, ne, ne, to_Ico_mod, to_Ioc_mod,
       ← eq_sub_iff_add_eq, sub_sub, sub_right_inj, ← add_one_zsmul,
       (zsmul_strict_mono_left hb).injective.eq_iff]

lemma not_mem_Ioo_mod_iff_to_Ico_div_eq_to_Ioc_div_add_one :
  ¬mem_Ioo_mod a b x ↔ to_Ico_div a hb x = to_Ioc_div a hb x + 1 :=
(mem_Ioo_mod_iff_to_Ico_div_ne_to_Ioc_div_add_one hb).not_left

section
include hb

lemma mem_Ioo_mod_iff_ne_add_zsmul : mem_Ioo_mod a b x ↔ ∀ z : ℤ, x ≠ a + z • b :=
begin
  rw [mem_Ioo_mod_iff_to_Ico_mod_ne_left hb, ← not_iff_not],
  push_neg, split; intro h,
  { rw ← h,
    exact ⟨_, (to_Ico_mod_add_to_Ico_div_zsmul _ _ _).symm⟩ },
  { rw [to_Ico_mod_eq_iff, set.left_mem_Ico],
    exact ⟨lt_add_of_pos_right a hb, h⟩, },
end

lemma not_mem_Ioo_mod_iff_eq_add_zsmul : ¬mem_Ioo_mod a b x ↔ ∃ z : ℤ, x = a + z • b :=
by simpa only [not_forall, not_ne_iff] using (mem_Ioo_mod_iff_ne_add_zsmul hb).not

lemma not_mem_Ioo_mod_iff_eq_mod_zmultiples :
  ¬mem_Ioo_mod a b x ↔ (x : α ⧸ add_subgroup.zmultiples b) = a :=
by simp_rw [not_mem_Ioo_mod_iff_eq_add_zsmul hb, quotient_add_group.eq_iff_sub_mem,
    add_subgroup.mem_zmultiples_iff, eq_sub_iff_add_eq', eq_comm]

lemma mem_Ioo_mod_iff_ne_mod_zmultiples :
  mem_Ioo_mod a b x ↔ (x : α ⧸ add_subgroup.zmultiples b) ≠ a :=
(not_mem_Ioo_mod_iff_eq_mod_zmultiples hb).not_right

lemma Ico_eq_locus_Ioc_eq_Union_Ioo :
  {x | to_Ico_mod a hb x = to_Ioc_mod a hb x} = ⋃ z : ℤ, set.Ioo (a + z • b) (a + b + z • b) :=
begin
  ext1, simp_rw [set.mem_set_of, set.mem_Union, ← set.sub_mem_Ioo_iff_left],
  exact (mem_Ioo_mod_iff_to_Ico_mod_eq_to_Ioc_mod hb).symm,
end

lemma to_Ioc_div_wcovby_to_Ico_div (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_div a hb x ⩿ to_Ico_div a hb x :=
begin
  suffices : to_Ioc_div a hb x = to_Ico_div a hb x ∨ to_Ioc_div a hb x + 1 = to_Ico_div a hb x,
  { rwa [wcovby_iff_eq_or_covby, ←order.succ_eq_iff_covby] },
  rw [eq_comm, ←mem_Ioo_mod_iff_to_Ico_div_eq_to_Ioc_div,
    eq_comm, ←not_mem_Ioo_mod_iff_to_Ico_div_eq_to_Ioc_div_add_one],
  exact em _,
end

lemma to_Ico_mod_le_to_Ioc_mod (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_mod a hb x ≤ to_Ioc_mod a hb x :=
begin
  rw [to_Ico_mod, to_Ioc_mod, sub_le_sub_iff_left],
  exact zsmul_mono_left hb.le (to_Ioc_div_wcovby_to_Ico_div _ _ _).le
end

lemma to_Ioc_mod_le_to_Ico_mod_add (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_mod a hb x ≤ to_Ico_mod a hb x + b :=
begin
  rw [to_Ico_mod, to_Ioc_mod, sub_add, sub_le_sub_iff_left, sub_le_iff_le_add, ←add_one_zsmul,
    (zsmul_strict_mono_left hb).le_iff_le],
  apply (to_Ioc_div_wcovby_to_Ico_div _ _ _).le_succ,
end

end

/-- If `a` and `b` fall within the same cycle WRT `c`, then they are not within `p` of one another.
-/
@[simp] lemma to_Ico_mod_inj :
  to_Ico_mod c hp a = to_Ico_mod c hp b ↔ ¬ mem_Ioo_mod a p b :=
begin
  rw [to_Ico_mod_eq_to_Ico_mod, not_mem_Ioo_mod_iff_eq_add_zsmul hp],
  simp_rw sub_eq_iff_eq_add',
end

lemma to_Ico_mod_ne_to_Ico_mod :
  to_Ico_mod c hp a ≠ to_Ico_mod c hp b ↔ mem_Ioo_mod a p b :=
(to_Ico_mod_inj hp).not_left

alias to_Ico_mod_ne_to_Ico_mod ↔ _ mem_Ioo_mod.to_Ico_mod_ne_to_Ico_mod

lemma mem_Ioo_mod_comm (hp : 0 < p) : mem_Ioo_mod a p b ↔ mem_Ioo_mod b p a :=
by rw [←to_Ico_mod_ne_to_Ico_mod hp, ne_comm, to_Ico_mod_ne_to_Ico_mod]; assumption

alias mem_Ioo_mod_comm ↔ mem_Ioo_mod.symm _

end Ico_Ioc

lemma to_Ico_mod_eq_self {a b x : α} (hb : 0 < b) : to_Ico_mod a hb x = x ↔ x ∈ set.Ico a (a + b) :=
begin
  rw [to_Ico_mod_eq_iff, and_iff_left],
  refine ⟨0, _⟩,
  simp
end

lemma to_Ioc_mod_eq_self {a b x : α} (hb : 0 < b) : to_Ioc_mod a hb x = x ↔ x ∈ set.Ioc a (a + b) :=
begin
  rw [to_Ioc_mod_eq_iff, and_iff_left],
  refine ⟨0, _⟩,
  simp
end

@[simp] lemma to_Ico_mod_to_Ico_mod (a₁ a₂ : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_mod a₁ hb (to_Ico_mod a₂ hb x) = to_Ico_mod a₁ hb x :=
begin
  rw to_Ico_mod_eq_to_Ico_mod,
  exact ⟨to_Ico_div a₂ hb x, self_sub_to_Ico_mod a₂ hb x⟩
end

@[simp] lemma to_Ico_mod_to_Ioc_mod (a₁ a₂ : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_mod a₁ hb (to_Ioc_mod a₂ hb x) = to_Ico_mod a₁ hb x :=
begin
  rw to_Ico_mod_eq_to_Ico_mod,
  exact ⟨to_Ioc_div a₂ hb x, self_sub_to_Ioc_mod a₂ hb x⟩
end

@[simp] lemma to_Ioc_mod_to_Ioc_mod (a₁ a₂ : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_mod a₁ hb (to_Ioc_mod a₂ hb x) = to_Ioc_mod a₁ hb x :=
begin
  rw to_Ioc_mod_eq_to_Ioc_mod,
  exact ⟨to_Ioc_div a₂ hb x, self_sub_to_Ioc_mod a₂ hb x⟩
end

@[simp] lemma to_Ioc_mod_to_Ico_mod (a₁ a₂ : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_mod a₁ hb (to_Ico_mod a₂ hb x) = to_Ioc_mod a₁ hb x :=
begin
  rw to_Ioc_mod_eq_to_Ioc_mod,
  exact ⟨to_Ico_div a₂ hb x, self_sub_to_Ico_mod a₂ hb x⟩
end

lemma to_Ico_mod_zero_sub_comm {b : α} (hb : 0 < b) (x y : α) :
  to_Ico_mod 0 hb (x - y) = b - to_Ioc_mod 0 hb (y - x) :=
by rw [←neg_sub, to_Ico_mod_neg, neg_zero]

lemma to_Ioc_mod_zero_sub_comm {b : α} (hb : 0 < b) (x y : α) :
  to_Ioc_mod 0 hb (x - y) = b - to_Ico_mod 0 hb (y - x) :=
by rw [←neg_sub, to_Ioc_mod_neg, neg_zero]

private lemma to_Ixx_mod_add_eq {b : α} (hb : 0 < b) (x₁ x₂ : α) :
  to_Ico_mod 0 hb (x₁ - x₂) + to_Ioc_mod 0 hb (x₂ - x₁) = b :=
by rw [to_Ico_mod_zero_sub_comm, sub_add_cancel]

lemma to_Ico_mod_periodic (a : α) {b : α} (hb : 0 < b) : function.periodic (to_Ico_mod a hb) b :=
to_Ico_mod_add_right a hb

lemma to_Ioc_mod_periodic (a : α) {b : α} (hb : 0 < b) : function.periodic (to_Ioc_mod a hb) b :=
to_Ioc_mod_add_right a hb

/-- `to_Ico_mod` as an equiv from the quotient. -/
@[simps symm_apply]
def quotient_add_group.equiv_Ico_mod (a : α) {b : α} (hb : 0 < b) :
  (α ⧸ add_subgroup.zmultiples b) ≃ set.Ico a (a + b) :=
{ to_fun := λ x, ⟨(to_Ico_mod_periodic a hb).lift x,
    quotient_add_group.induction_on' x $ to_Ico_mod_mem_Ico a hb⟩,
  inv_fun := coe,
  right_inv := λ x, subtype.ext $ (to_Ico_mod_eq_self hb).mpr x.prop,
  left_inv := λ x, begin
    induction x using quotient_add_group.induction_on',
    dsimp,
    rw [quotient_add_group.eq_iff_sub_mem, to_Ico_mod_sub_self],
    apply add_subgroup.zsmul_mem_zmultiples,
  end }

@[simp]
lemma quotient_add_group.equiv_Ico_mod_coe (a : α) {b : α} (hb : 0 < b) (x : α) :
  quotient_add_group.equiv_Ico_mod a hb ↑x = ⟨to_Ico_mod a hb x, to_Ico_mod_mem_Ico a hb _⟩ :=
rfl

@[simp]
lemma quotient_add_group.equiv_Ico_mod_zero (a : α) {b : α} (hb : 0 < b) :
  quotient_add_group.equiv_Ico_mod a hb 0 = ⟨to_Ico_mod a hb 0, to_Ico_mod_mem_Ico a hb _⟩ :=
rfl

/-- `to_Ioc_mod` as an equiv from the quotient. -/
@[simps symm_apply]
def quotient_add_group.equiv_Ioc_mod (a : α) {b : α} (hb : 0 < b) :
  (α ⧸ add_subgroup.zmultiples b) ≃ set.Ioc a (a + b) :=
{ to_fun := λ x, ⟨(to_Ioc_mod_periodic a hb).lift x,
    quotient_add_group.induction_on' x $ to_Ioc_mod_mem_Ioc a hb⟩,
  inv_fun := coe,
  right_inv := λ x, subtype.ext $ (to_Ioc_mod_eq_self hb).mpr x.prop,
  left_inv := λ x, begin
    induction x using quotient_add_group.induction_on',
    dsimp,
    rw [quotient_add_group.eq_iff_sub_mem, to_Ioc_mod_sub_self],
    apply add_subgroup.zsmul_mem_zmultiples,
  end }

@[simp]
lemma quotient_add_group.equiv_Ioc_mod_coe (a : α) {b : α} (hb : 0 < b) (x : α) :
  quotient_add_group.equiv_Ioc_mod a hb ↑x = ⟨to_Ioc_mod a hb x, to_Ioc_mod_mem_Ioc a hb _⟩ :=
rfl

@[simp]
lemma quotient_add_group.equiv_Ioc_mod_zero (a : α) {b : α} (hb : 0 < b) :
  quotient_add_group.equiv_Ioc_mod a hb 0 = ⟨to_Ioc_mod a hb 0, to_Ioc_mod_mem_Ioc a hb _⟩ :=
rfl

namespace quotient_add_group
variables {b : α} [hb : fact (0 < b)]
include hb

instance : has_btw (α ⧸ add_subgroup.zmultiples b) :=
{ btw := λ x₁ x₂ x₃, (equiv_Ico_mod 0 hb.out (x₂ - x₁) : α) ≤ equiv_Ioc_mod 0 hb.out (x₃ - x₁) }

lemma btw_coe_iff' (x₁ x₂ x₃ : α) :
  has_btw.btw (x₁ : α ⧸ add_subgroup.zmultiples b) x₂ x₃ ↔
    to_Ico_mod 0 hb.out (x₂ - x₁) ≤ to_Ioc_mod 0 hb.out (x₃ - x₁) :=
iff.rfl

-- maybe harder to prove with than the primed one?
lemma btw_coe_iff (x₁ x₂ x₃ : α) :
  has_btw.btw (x₁ : α ⧸ add_subgroup.zmultiples b) x₂ x₃ ↔
    to_Ico_mod x₁ hb.out x₂ ≤ to_Ioc_mod x₁ hb.out x₃ :=
by rw [btw_coe_iff', to_Ioc_mod_sub', to_Ico_mod_sub', zero_add, sub_le_sub_iff_right]

lemma to_Ico_mod_eq_sub (hb : 0 < b) (x₁ x₂ : α) :
  to_Ico_mod x₁ hb x₂ = to_Ico_mod 0 hb (x₂ - x₁) + x₁ :=
by rw [to_Ico_mod_sub', zero_add, sub_add_cancel]

lemma to_Ioc_mod_eq_sub (hb : 0 < b) (x₁ x₂ : α) :
  to_Ioc_mod x₁ hb x₂ = to_Ioc_mod 0 hb (x₂ - x₁) + x₁ :=
by rw [to_Ioc_mod_sub', zero_add, sub_add_cancel]

private lemma to_Ixx_mod_iff (hb : 0 < b) (x₁ x₂ x₃ : α) :
  to_Ico_mod x₁ hb x₂ ≤ to_Ioc_mod x₁ hb x₃ ↔
  to_Ico_mod 0 hb (x₂ - x₁) + to_Ico_mod 0 hb (x₁ - x₃) ≤ b :=
by rw [to_Ico_mod_eq_sub, to_Ioc_mod_eq_sub _ x₁, add_le_add_iff_right, ←neg_sub x₁ x₃,
    to_Ioc_mod_neg, neg_zero, le_sub_iff_add_le]

@[simp] lemma to_Ico_mod_zsmul_add' (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
  to_Ico_mod (a + m • b) hb x = to_Ico_mod a hb x + m • b :=
by simp only [to_Ico_mod, to_Ico_div_add_zsmul', sub_smul, sub_add]

@[simp] lemma to_Ioc_mod_zsmul_add' (a : α) {b : α} (hb : 0 < b) (x : α) (m : ℤ) :
  to_Ioc_mod (a + m • b) hb x = to_Ioc_mod a hb x + m • b :=
by simp only [to_Ioc_mod, to_Ioc_div_add_zsmul', sub_smul, sub_add]

private lemma to_Ixx_mod_cyclic_left (x₁ x₂ x₃ : α)
  (h : to_Ico_mod x₁ hb.out x₂ ≤ to_Ioc_mod x₁ hb.out x₃) :
  to_Ico_mod x₂ hb.out x₃ ≤ to_Ioc_mod x₂ hb.out x₁ :=
begin
  let x₁' := to_Ico_mod 0 hb.out x₁,
  let x₂' := to_Ico_mod x₁' hb.out x₂,
  let x₃' := to_Ico_mod x₂' hb.out x₃,

  suffices hequiv : x₃' ≤ to_Ioc_mod x₂' hb.out x₁',
  { have hd : ∃ (z : ℤ), x₂ = x₂' + z • b := ((to_Ico_mod_eq_iff hb.out).1 rfl).2,
    clear_value x₂',
    obtain ⟨m₂, rfl⟩ := hd,
    simpa using hequiv },

  have h : x₂' ≤ to_Ioc_mod x₁' hb.out x₃',
  { have hd : ∃ (z : ℤ), x₁ = x₁' + z • b := ((to_Ico_mod_eq_iff hb.out).1 rfl).2,
    clear_value x₁',
    obtain ⟨m, rfl⟩ := hd,
    simpa using h },

  have hIoc₂₁ : to_Ioc_mod x₂' hb.out x₁' = x₁' + b,
  { apply (to_Ioc_mod_eq_iff hb.out).2,
    refine ⟨_, -1, _⟩,
    { simp only [set.mem_Ioc, add_le_add_iff_right],
      exact ⟨to_Ico_mod_lt_right _ _ _, left_le_to_Ico_mod _ _ _⟩ },
    simp only [add_neg_cancel_right, one_smul, neg_smul] },

  by_cases hc : x₃' ≤ x₁' + b,
  { exact hIoc₂₁.symm.trans_ge hc },

  rw [not_le] at hc,
  have hIoc₁₃ : to_Ioc_mod x₁' hb.out x₃' = x₃' - b,
  { apply (to_Ioc_mod_eq_iff hb.out).2,
    refine ⟨_, 1, _⟩, swap,
    { simp only [sub_add_cancel, one_smul] },
    simp only [set.mem_Ioc, add_le_add_iff_right],
    split,
    { exact lt_sub_iff_add_lt.2 hc },
      have w₁ : x₃' - b < x₂' := (sub_lt_iff_lt_add.2 (to_Ico_mod_lt_right _ _ _)),
      have w₂ : x₂' < x₁' + b := to_Ico_mod_lt_right _ _ _,
      exact (le_of_lt w₁).trans (le_of_lt w₂) },

  have h₃ : x₃' - b < x₂' := sub_lt_iff_lt_add.2 (to_Ico_mod_lt_right x₂' _ x₃),
  have not_h₃ := not_lt.2 (h.trans hIoc₁₃.symm.ge),
  contradiction,
end

private lemma to_Ixx_mod_antisymm {x₁ x₂ x₃ : α}
  (h₁₂₃ : to_Ico_mod x₁ hb.out x₂ ≤ to_Ioc_mod x₁ hb.out x₃)
  (h₁₃₂ : to_Ico_mod x₁ hb.out x₃ ≤ to_Ioc_mod x₁ hb.out x₂) :
  ¬mem_Ioo_mod x₂ b x₁ ∨ ¬mem_Ioo_mod x₃ b x₂ ∨ ¬mem_Ioo_mod x₁ b x₃ :=
begin
  by_contra' h,
  rw ←h.2.2.to_Ico_mod_eq_to_Ioc_mod hb.out at h₁₂₃,
  rw ←(h.1.symm hb.out).to_Ico_mod_eq_to_Ioc_mod hb.out at h₁₃₂,
  exact h.2.1.to_Ico_mod_ne_to_Ico_mod hb.out (h₁₃₂.antisymm h₁₂₃),
end

/--
 From this I think it's a lot easier to verify the axioms; another essential ingredient is the lemma
 saying {x-y} + {y-x} = period if x ≠ y (and = 0 if x = y). Thus if x ≠ y and y ≠ z then
 ({x-y} + {y-z}) + ({z-y} + {y-x}) = 2 * period, so one of {x-y} + {y-z} and {z-y} + {y-x} must be
 `≤ period`, proving btw_total;
-/
private lemma to_Ixx_mod_total' (x y z : α) :
  to_Ico_mod y hb.out x ≤ to_Ioc_mod y hb.out z ∨
  to_Ico_mod y hb.out z ≤ to_Ioc_mod y hb.out x :=
begin
  have := congr_arg2 (+) (to_Ixx_mod_add_eq hb.out x y) (to_Ixx_mod_add_eq hb.out z y),
  rw [add_add_add_comm, add_comm (to_Ioc_mod _ _ _), add_add_add_comm, ←two_nsmul] at this,
  replace := min_le_of_add_le_two_nsmul this.le,
  rw min_le_iff at this,
  rw [to_Ixx_mod_iff, to_Ixx_mod_iff],
  refine this.imp
    (le_trans (add_le_add_left _ _))
    (le_trans (add_le_add_left _ _)),
  { apply to_Ico_mod_le_to_Ioc_mod },
  { apply to_Ico_mod_le_to_Ioc_mod },
end

private lemma to_Ixx_mod_total (x y z : α) :
  to_Ico_mod x hb.out y ≤ to_Ioc_mod x hb.out z ∨
  to_Ico_mod z hb.out y ≤ to_Ioc_mod z hb.out x :=
begin
  refine ( to_Ixx_mod_total' _ _ _).imp_right _,
  apply to_Ixx_mod_cyclic_left,
end

private lemma to_Ixx_mod_trans {x₁ x₂ x₃ x₄ : α}
  (h₁₂₃ : to_Ico_mod x₁ hb.out x₂ ≤ to_Ioc_mod x₁ hb.out x₃
    ∧ ¬to_Ico_mod x₃ hb.out x₂ ≤ to_Ioc_mod x₃ hb.out x₁)
  (h₂₃₄ : to_Ico_mod x₂ hb.out x₄ ≤ to_Ioc_mod x₂ hb.out x₃
    ∧ ¬to_Ico_mod x₃ hb.out x₄ ≤ to_Ioc_mod x₃ hb.out x₂) :
  to_Ico_mod x₁ hb.out x₄ ≤ to_Ioc_mod x₁ hb.out x₃
    ∧ ¬to_Ico_mod x₃ hb.out x₄ ≤ to_Ioc_mod x₃ hb.out x₁ :=
begin
  have h₁₂₃' := to_Ixx_mod_cyclic_left _ _ _ (to_Ixx_mod_cyclic_left _ _ _ h₁₂₃.1),
  have h₂₃₄' := to_Ixx_mod_cyclic_left _ _ _ (to_Ixx_mod_cyclic_left _ _ _ h₂₃₄.1),

  split, swap,
  { rw not_le,
    have := to_Ico_mod_le_to_Ioc_mod x₃ hb.out x₂,
    exact ((not_le.1 h₁₂₃.2).trans_le this).trans (not_le.1 h₂₃₄.2) },

  suffices h : to_Ico_mod x₃ hb.out x₂ = to_Ioc_mod x₃ hb.out x₂,
  { exact to_Ixx_mod_cyclic_left _ _ _ ((h₁₂₃'.trans $ ge_of_eq h).trans h₂₃₄') },

  by_contra,
  have hIco₃₂ : to_Ico_mod x₃ hb.out x₂ = x₃ :=
    ((tfae_mem_Ioo_mod x₃ hb.out x₂).out 3 1).not_right.2 h,
  have hIco₃₁ : x₃ < to_Ioc_mod x₃ hb.out x₁ := left_lt_to_Ioc_mod x₃ _ x₁,
  exact (h₁₂₃.2 $ (le_of_eq hIco₃₂).trans hIco₃₁.le),
end

instance circular_preorder : circular_preorder (α ⧸ add_subgroup.zmultiples b) :=
{ btw_refl := λ x, show _ ≤ _, by simp [sub_self, hb.out.le],
  btw_cyclic_left := λ x₁ x₂ x₃ h, begin
    induction x₁ using quotient_add_group.induction_on',
    induction x₂ using quotient_add_group.induction_on',
    induction x₃ using quotient_add_group.induction_on',
    simp_rw [btw_coe_iff] at h ⊢,
    apply to_Ixx_mod_cyclic_left _ _ _ h,
  end,
  sbtw := _,
  sbtw_iff_btw_not_btw := λ _ _ _, iff.rfl,
  sbtw_trans_left := λ x₁ x₂ x₃ x₄ (h₁₂₃ : _ ∧ _) (h₂₃₄ : _ ∧ _), show _ ∧ _, begin
    induction x₁ using quotient_add_group.induction_on',
    induction x₂ using quotient_add_group.induction_on',
    induction x₃ using quotient_add_group.induction_on',
    induction x₄ using quotient_add_group.induction_on',
    simp_rw [btw_coe_iff] at h₁₂₃ h₂₃₄ ⊢,
    apply to_Ixx_mod_trans h₁₂₃ h₂₃₄,
  end }

instance circular_order : circular_order (α ⧸ add_subgroup.zmultiples b) :=
{ btw_antisymm := λ x₁ x₂ x₃ h₁₂₃ h₃₂₁, begin
    induction x₁ using quotient_add_group.induction_on',
    induction x₂ using quotient_add_group.induction_on',
    induction x₃ using quotient_add_group.induction_on',
    rw btw_cyclic at h₃₂₁,
    simp_rw [btw_coe_iff] at h₁₂₃ h₃₂₁,
    simp_rw ←not_mem_Ioo_mod_iff_eq_mod_zmultiples hb.out,
    exact to_Ixx_mod_antisymm h₁₂₃ h₃₂₁,
  end,
  btw_total := λ x₁ x₂ x₃, begin
    induction x₁ using quotient_add_group.induction_on',
    induction x₂ using quotient_add_group.induction_on',
    induction x₃ using quotient_add_group.induction_on',
    simp_rw [btw_coe_iff] at ⊢,
    apply to_Ixx_mod_total,
  end,
  ..quotient_add_group.circular_preorder }

end quotient_add_group

end linear_ordered_add_comm_group

section linear_ordered_field

variables {α : Type*} [linear_ordered_field α] [floor_ring α]

lemma to_Ico_div_eq_floor (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_div a hb x = ⌊(x - a) / b⌋ :=
begin
  refine (eq_to_Ico_div_of_sub_zsmul_mem_Ico hb _).symm,
  rw [set.mem_Ico, zsmul_eq_mul, ←sub_nonneg, add_comm, sub_right_comm, ←sub_lt_iff_lt_add,
    sub_right_comm _ _ a],
  exact ⟨int.sub_floor_div_mul_nonneg _ hb, int.sub_floor_div_mul_lt _ hb⟩,
end

lemma to_Ioc_div_eq_neg_floor (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_div a hb x = -⌊(a + b - x) / b⌋ :=
begin
  refine (eq_to_Ioc_div_of_sub_zsmul_mem_Ioc hb _).symm,
  rw [set.mem_Ioc, zsmul_eq_mul, int.cast_neg, neg_mul, sub_neg_eq_add, ←sub_nonneg,
    sub_add_eq_sub_sub],
  refine ⟨_, int.sub_floor_div_mul_nonneg _ hb⟩,
  rw [←add_lt_add_iff_right b, add_assoc, add_comm x, ←sub_lt_iff_lt_add, add_comm (_ * _),
      ←sub_lt_iff_lt_add],
  exact int.sub_floor_div_mul_lt _ hb
end

lemma to_Ico_div_zero_one (x : α) : to_Ico_div (0 : α) zero_lt_one x = ⌊x⌋ :=
by simp [to_Ico_div_eq_floor]

lemma to_Ico_mod_eq_add_fract_mul (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ico_mod a hb x = a + int.fract ((x - a) / b) * b :=
begin
  rw [to_Ico_mod, to_Ico_div_eq_floor, int.fract],
  field_simp [hb.ne.symm],
  ring
end

lemma to_Ico_mod_eq_fract_mul {b : α} (hb : 0 < b) (x : α) :
  to_Ico_mod 0 hb x = int.fract (x / b) * b :=
by simp [to_Ico_mod_eq_add_fract_mul]

lemma to_Ioc_mod_eq_sub_fract_mul (a : α) {b : α} (hb : 0 < b) (x : α) :
  to_Ioc_mod a hb x = a + b - int.fract ((a + b - x) / b) * b :=
begin
  rw [to_Ioc_mod, to_Ioc_div_eq_neg_floor, int.fract],
  field_simp [hb.ne.symm],
  ring
end

lemma to_Ico_mod_zero_one (x : α) : to_Ico_mod (0 : α) zero_lt_one x = int.fract x :=
by simp [to_Ico_mod_eq_add_fract_mul]

end linear_ordered_field

/-! ### Lemmas about unions of translates of intervals -/
section union

open set int

section linear_ordered_add_comm_group

variables {α : Type*} [linear_ordered_add_comm_group α] [archimedean α] (a : α) {b : α} (hb : 0 < b)
include hb

lemma Union_Ioc_add_zsmul : (⋃ (n : ℤ), Ioc (a + n • b) (a + (n + 1) • b)) = univ :=
begin
  refine eq_univ_iff_forall.mpr (λ x, mem_Union.mpr _),
  rcases sub_to_Ioc_div_zsmul_mem_Ioc a hb x with ⟨hl, hr⟩,
  refine ⟨to_Ioc_div a hb x, ⟨lt_sub_iff_add_lt.mp hl, _⟩⟩,
  rw [add_smul, one_smul, ←add_assoc],
  convert sub_le_iff_le_add.mp hr using 1, abel,
end

lemma Union_Ico_add_zsmul : (⋃ (n : ℤ), Ico (a + n • b) (a + (n + 1) • b)) = univ :=
begin
  refine eq_univ_iff_forall.mpr (λ x, mem_Union.mpr _),
  rcases sub_to_Ico_div_zsmul_mem_Ico a hb x with ⟨hl, hr⟩,
  refine ⟨to_Ico_div a hb x, ⟨le_sub_iff_add_le.mp hl, _⟩⟩,
  rw [add_smul, one_smul, ←add_assoc],
  convert sub_lt_iff_lt_add.mp hr using 1, abel,
end

lemma Union_Icc_add_zsmul : (⋃ (n : ℤ), Icc (a + n • b) (a + (n + 1) • b)) = univ :=
by simpa only [Union_Ioc_add_zsmul a hb, univ_subset_iff] using
  Union_mono (λ n : ℤ, (Ioc_subset_Icc_self : Ioc (a + n • b) (a + (n + 1) • b) ⊆ Icc _ _))

lemma Union_Ioc_zsmul : (⋃ (n : ℤ), Ioc (n • b) ((n + 1) • b)) = univ :=
by simpa only [zero_add] using Union_Ioc_add_zsmul 0 hb

lemma Union_Ico_zsmul : (⋃ (n : ℤ), Ico (n • b) ((n + 1) • b)) = univ :=
by simpa only [zero_add] using Union_Ico_add_zsmul 0 hb

lemma Union_Icc_zsmul : (⋃ (n : ℤ), Icc (n • b) ((n + 1) • b)) = univ :=
by simpa only [zero_add] using Union_Icc_add_zsmul 0 hb

end linear_ordered_add_comm_group

section linear_ordered_ring

variables {α : Type*} [linear_ordered_ring α] [archimedean α] (a : α)

lemma Union_Ioc_add_int_cast : (⋃ (n : ℤ), Ioc (a + n) (a + n + 1)) = set.univ :=
by simpa only [zsmul_one, int.cast_add, int.cast_one, ←add_assoc]
  using Union_Ioc_add_zsmul a zero_lt_one

lemma Union_Ico_add_int_cast : (⋃ (n : ℤ), Ico (a + n) (a + n + 1)) = set.univ :=
by simpa only [zsmul_one, int.cast_add, int.cast_one, ←add_assoc]
  using Union_Ico_add_zsmul a zero_lt_one

lemma Union_Icc_add_int_cast : (⋃ (n : ℤ), Icc (a + n) (a + n + 1)) = set.univ :=
by simpa only [zsmul_one, int.cast_add, int.cast_one, ←add_assoc]
  using Union_Icc_add_zsmul a (zero_lt_one' α)

variables (α)

lemma Union_Ioc_int_cast : (⋃ (n : ℤ), Ioc (n : α) (n + 1)) = set.univ :=
by simpa only [zero_add] using Union_Ioc_add_int_cast (0 : α)

lemma Union_Ico_int_cast : (⋃ (n : ℤ), Ico (n : α) (n + 1)) = set.univ :=
by simpa only [zero_add] using Union_Ico_add_int_cast (0 : α)

lemma Union_Icc_int_cast : (⋃ (n : ℤ), Icc (n : α) (n + 1)) = set.univ :=
by simpa only [zero_add] using Union_Icc_add_int_cast (0 : α)

end linear_ordered_ring

end union
