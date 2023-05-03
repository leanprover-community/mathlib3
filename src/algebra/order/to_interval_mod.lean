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

* `to_Ico_div hp a b` (where `hp : 0 < p`): The unique integer such that this multiple of `p`,
  subtracted from `b`, is in `Ico a (a + p)`.
* `to_Ico_mod hp a b` (where `hp : 0 < p`): Reduce `b` to the interval `Ico a (a + p)`.
* `to_Ioc_div hp a b` (where `hp : 0 < p`): The unique integer such that this multiple of `p`,
  subtracted from `b`, is in `Ioc a (a + p)`.
* `to_Ioc_mod hp a b` (where `hp : 0 < p`): Reduce `b` to the interval `Ioc a (a + p)`.
* `add_comm_group.modeq p a b`: `a` and `b` are congruent modulo a multiple of `p`. See also
  `smodeq` which is a more general version in arbitrary submodules.

## TODO

Unify `smodeq` and `add_comm_group.modeq`, which were originally developed independently.
-/

noncomputable theory

section linear_ordered_add_comm_group

variables {α : Type*} [linear_ordered_add_comm_group α] [hα : archimedean α] {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}
include hα

/--
The unique integer such that this multiple of `p`, subtracted from `b`, is in `Ico a (a + p)`. -/
def to_Ico_div (a b : α) : ℤ := (exists_unique_sub_zsmul_mem_Ico hp b a).some

lemma sub_to_Ico_div_zsmul_mem_Ico (a b : α) : b - to_Ico_div hp a b • p ∈ set.Ico a (a + p) :=
(exists_unique_sub_zsmul_mem_Ico hp b a).some_spec.1

lemma to_Ico_div_eq_of_sub_zsmul_mem_Ico (h : b - n • p ∈ set.Ico a (a + p)) :
  to_Ico_div hp a b = n :=
((exists_unique_sub_zsmul_mem_Ico hp b a).some_spec.2 _ h).symm

/--
The unique integer such that this multiple of `p`, subtracted from `b`, is in `Ioc a (a + p)`. -/
def to_Ioc_div (a b : α) : ℤ := (exists_unique_sub_zsmul_mem_Ioc hp b a).some

lemma sub_to_Ioc_div_zsmul_mem_Ioc (a b : α) : b - to_Ioc_div hp a b • p ∈ set.Ioc a (a + p) :=
(exists_unique_sub_zsmul_mem_Ioc hp b a).some_spec.1

lemma to_Ioc_div_eq_of_sub_zsmul_mem_Ioc (h : b - n • p ∈ set.Ioc a (a + p)) :
  to_Ioc_div hp a b = n :=
((exists_unique_sub_zsmul_mem_Ioc hp b a).some_spec.2 _ h).symm

/-- Reduce `b` to the interval `Ico a (a + p)`. -/
def to_Ico_mod (a b : α) : α := b - to_Ico_div hp a b • p

/-- Reduce `b` to the interval `Ioc a (a + p)`. -/
def to_Ioc_mod (a b : α) : α := b - to_Ioc_div hp a b • p

lemma to_Ico_mod_mem_Ico (a b : α) : to_Ico_mod hp a b ∈ set.Ico a (a + p) :=
sub_to_Ico_div_zsmul_mem_Ico hp a b

lemma to_Ico_mod_mem_Ico' (b : α) : to_Ico_mod hp 0 b ∈ set.Ico 0 p :=
by { convert to_Ico_mod_mem_Ico hp 0 b, exact (zero_add p).symm, }

lemma to_Ioc_mod_mem_Ioc (a b : α) : to_Ioc_mod hp a b ∈ set.Ioc a (a + p) :=
sub_to_Ioc_div_zsmul_mem_Ioc hp a b

lemma left_le_to_Ico_mod (a b : α) : a ≤ to_Ico_mod hp a b :=
(set.mem_Ico.1 (to_Ico_mod_mem_Ico hp a b)).1

lemma left_lt_to_Ioc_mod (a b : α) : a < to_Ioc_mod hp a b :=
(set.mem_Ioc.1 (to_Ioc_mod_mem_Ioc hp a b)).1

lemma to_Ico_mod_lt_right (a b : α) : to_Ico_mod hp a b < a + p :=
(set.mem_Ico.1 (to_Ico_mod_mem_Ico hp a b)).2

lemma to_Ioc_mod_le_right (a b : α) : to_Ioc_mod hp a b ≤ a + p :=
(set.mem_Ioc.1 (to_Ioc_mod_mem_Ioc hp a b)).2

@[simp] lemma self_sub_to_Ico_div_zsmul (a b : α) : b - to_Ico_div hp a b • p = to_Ico_mod hp a b :=
rfl

@[simp] lemma self_sub_to_Ioc_div_zsmul (a b : α) : b - to_Ioc_div hp a b • p = to_Ioc_mod hp a b :=
rfl

@[simp] lemma to_Ico_div_zsmul_sub_self (a b : α) :
  to_Ico_div hp a b • p - b = -to_Ico_mod hp a b :=
by rw [to_Ico_mod, neg_sub]

@[simp] lemma to_Ioc_div_zsmul_sub_self (a b : α) :
  to_Ioc_div hp a b • p - b = -to_Ioc_mod hp a b :=
by rw [to_Ioc_mod, neg_sub]

@[simp] lemma to_Ico_mod_sub_self (a b : α) : to_Ico_mod hp a b - b = -to_Ico_div hp a b • p :=
by rw [to_Ico_mod, sub_sub_cancel_left, neg_smul]

@[simp] lemma to_Ioc_mod_sub_self (a b : α) : to_Ioc_mod hp a b - b = -to_Ioc_div hp a b • p :=
by rw [to_Ioc_mod, sub_sub_cancel_left, neg_smul]

@[simp] lemma self_sub_to_Ico_mod (a b : α) : b - to_Ico_mod hp a b = to_Ico_div hp a b • p :=
by rw [to_Ico_mod, sub_sub_cancel]

@[simp] lemma self_sub_to_Ioc_mod (a b : α) : b - to_Ioc_mod hp a b = to_Ioc_div hp a b • p :=
by rw [to_Ioc_mod, sub_sub_cancel]

@[simp] lemma to_Ico_mod_add_to_Ico_div_zsmul (a b : α) :
  to_Ico_mod hp a b + to_Ico_div hp a b • p = b :=
by rw [to_Ico_mod, sub_add_cancel]

@[simp] lemma to_Ioc_mod_add_to_Ioc_div_zsmul (a b : α) :
  to_Ioc_mod hp a b + to_Ioc_div hp a b • p = b :=
by rw [to_Ioc_mod, sub_add_cancel]

@[simp] lemma to_Ico_div_zsmul_sub_to_Ico_mod (a b : α) :
  to_Ico_div hp a b • p + to_Ico_mod hp a b = b :=
by rw [add_comm, to_Ico_mod_add_to_Ico_div_zsmul]

@[simp] lemma to_Ioc_div_zsmul_sub_to_Ioc_mod (a b : α) :
  to_Ioc_div hp a b • p + to_Ioc_mod hp a b = b :=
by rw [add_comm, to_Ioc_mod_add_to_Ioc_div_zsmul]

lemma to_Ico_mod_eq_iff : to_Ico_mod hp a b = c ↔ c ∈ set.Ico a (a + p) ∧ ∃ z : ℤ, b = c + z • p :=
begin
  refine ⟨λ h, ⟨h ▸ to_Ico_mod_mem_Ico hp a b, to_Ico_div hp a b,
                h ▸ (to_Ico_mod_add_to_Ico_div_zsmul _ _ _).symm⟩, _⟩,
  simp_rw ←@sub_eq_iff_eq_add,
  rintro ⟨hc, n, rfl⟩,
  rw [←to_Ico_div_eq_of_sub_zsmul_mem_Ico hp hc, to_Ico_mod],
end

lemma to_Ioc_mod_eq_iff : to_Ioc_mod hp a b = c ↔ c ∈ set.Ioc a (a + p) ∧ ∃ z : ℤ, b = c + z • p :=
begin
  refine ⟨λ h, ⟨h ▸ to_Ioc_mod_mem_Ioc hp a b, to_Ioc_div hp a b,
                h ▸ (to_Ioc_mod_add_to_Ioc_div_zsmul hp _ _).symm⟩, _⟩,
  simp_rw ←@sub_eq_iff_eq_add,
  rintro ⟨hc, n, rfl⟩,
  rw [←to_Ioc_div_eq_of_sub_zsmul_mem_Ioc hp hc, to_Ioc_mod],
end

@[simp] lemma to_Ico_div_apply_left (a : α) : to_Ico_div hp a a = 0 :=
to_Ico_div_eq_of_sub_zsmul_mem_Ico hp $ by simp [hp]

@[simp] lemma to_Ioc_div_apply_left (a : α) : to_Ioc_div hp a a = -1 :=
to_Ioc_div_eq_of_sub_zsmul_mem_Ioc hp $ by simp [hp]

@[simp] lemma to_Ico_mod_apply_left (a : α) : to_Ico_mod hp a a = a :=
by { rw [to_Ico_mod_eq_iff hp, set.left_mem_Ico], exact ⟨lt_add_of_pos_right _ hp, 0, by simp⟩ }

@[simp] lemma to_Ioc_mod_apply_left (a : α) : to_Ioc_mod hp a a = a + p :=
by { rw [to_Ioc_mod_eq_iff hp, set.right_mem_Ioc], exact ⟨lt_add_of_pos_right _ hp, -1, by simp⟩ }

lemma to_Ico_div_apply_right (a : α) : to_Ico_div hp a (a + p) = 1 :=
to_Ico_div_eq_of_sub_zsmul_mem_Ico hp $ by simp [hp]

lemma to_Ioc_div_apply_right (a : α) : to_Ioc_div hp a (a + p) = 0 :=
to_Ioc_div_eq_of_sub_zsmul_mem_Ioc hp $ by simp [hp]

lemma to_Ico_mod_apply_right (a : α) : to_Ico_mod hp a (a + p) = a :=
by { rw [to_Ico_mod_eq_iff hp, set.left_mem_Ico], exact ⟨lt_add_of_pos_right _ hp, 1, by simp⟩ }

lemma to_Ioc_mod_apply_right (a : α) : to_Ioc_mod hp a (a + p) = a + p :=
by { rw [to_Ioc_mod_eq_iff hp, set.right_mem_Ioc], exact ⟨lt_add_of_pos_right _ hp, 0, by simp⟩ }

@[simp] lemma to_Ico_div_add_zsmul (a b : α) (m : ℤ) :
  to_Ico_div hp a (b + m • p) = to_Ico_div hp a b + m :=
to_Ico_div_eq_of_sub_zsmul_mem_Ico hp $
  by simpa only [add_smul, add_sub_add_right_eq_sub] using sub_to_Ico_div_zsmul_mem_Ico hp a b

@[simp] lemma to_Ico_div_add_zsmul' (a b: α) (m : ℤ) :
  to_Ico_div hp (a + m • p) b = to_Ico_div hp a b - m :=
begin
  refine to_Ico_div_eq_of_sub_zsmul_mem_Ico _ _,
  rw [sub_smul, ←sub_add, add_right_comm],
  simpa using sub_to_Ico_div_zsmul_mem_Ico hp a b,
end

@[simp] lemma to_Ioc_div_add_zsmul (a b : α) (m : ℤ) :
  to_Ioc_div hp a (b + m • p) = to_Ioc_div hp a b + m :=
to_Ioc_div_eq_of_sub_zsmul_mem_Ioc hp $
  by simpa only [add_smul, add_sub_add_right_eq_sub] using sub_to_Ioc_div_zsmul_mem_Ioc hp a b

@[simp] lemma to_Ioc_div_add_zsmul' (a b : α) (m : ℤ) :
  to_Ioc_div hp (a + m • p) b = to_Ioc_div hp a b - m :=
begin
  refine to_Ioc_div_eq_of_sub_zsmul_mem_Ioc _ _,
  rw [sub_smul, ←sub_add, add_right_comm],
  simpa using sub_to_Ioc_div_zsmul_mem_Ioc hp a b,
end

@[simp] lemma to_Ico_div_zsmul_add (a b : α) (m : ℤ) :
  to_Ico_div hp a (m • p + b) = m + to_Ico_div hp a b :=
by rw [add_comm, to_Ico_div_add_zsmul, add_comm]

@[simp] lemma to_Ioc_div_zsmul_add (a b : α) (m : ℤ) :
  to_Ioc_div hp a (m • p + b) = to_Ioc_div hp a b + m :=
by rw [add_comm, to_Ioc_div_add_zsmul, add_comm]

@[simp] lemma to_Ico_div_sub_zsmul (a b : α) (m : ℤ) :
  to_Ico_div hp a (b - m • p) = to_Ico_div hp a b - m :=
by rw [sub_eq_add_neg, ←neg_smul, to_Ico_div_add_zsmul, sub_eq_add_neg]

@[simp] lemma to_Ioc_div_sub_zsmul (a b : α) (m : ℤ) :
  to_Ioc_div hp a (b - m • p) = to_Ioc_div hp a b - m :=
by rw [sub_eq_add_neg, ←neg_smul, to_Ioc_div_add_zsmul, sub_eq_add_neg]

@[simp] lemma to_Ico_div_add_right (a b : α) : to_Ico_div hp a (b + p) = to_Ico_div hp a b + 1 :=
by simpa only [one_zsmul] using to_Ico_div_add_zsmul hp a b 1

@[simp] lemma to_Ioc_div_add_right (a b : α) : to_Ioc_div hp a (b + p) = to_Ioc_div hp a b + 1 :=
by simpa only [one_zsmul] using to_Ioc_div_add_zsmul hp a b 1

@[simp] lemma to_Ico_div_add_left (a b : α) : to_Ico_div hp a (p + b) = to_Ico_div hp a b + 1 :=
by rw [add_comm, to_Ico_div_add_right]

@[simp] lemma to_Ioc_div_add_left (a b : α) : to_Ioc_div hp a (p + b) = to_Ioc_div hp a b + 1 :=
by rw [add_comm, to_Ioc_div_add_right]

@[simp] lemma to_Ico_div_sub (a b : α) : to_Ico_div hp a (b - p) = to_Ico_div hp a b - 1 :=
by simpa only [one_zsmul] using to_Ico_div_sub_zsmul hp a b 1

@[simp] lemma to_Ioc_div_sub (a b : α) : to_Ioc_div hp a (b - p) = to_Ioc_div hp a b - 1 :=
by simpa only [one_zsmul] using to_Ioc_div_sub_zsmul hp a b 1

lemma to_Ico_div_sub' (a b c : α) : to_Ico_div hp a (b - c) = to_Ico_div hp (a + c) b :=
begin
  apply to_Ico_div_eq_of_sub_zsmul_mem_Ico,
  rw [←sub_right_comm, set.sub_mem_Ico_iff_left, add_right_comm],
  exact sub_to_Ico_div_zsmul_mem_Ico hp (a + c) b,
end

lemma to_Ioc_div_sub' (a b c : α) : to_Ioc_div hp a (b - c) = to_Ioc_div hp (a + c) b :=
begin
  apply to_Ioc_div_eq_of_sub_zsmul_mem_Ioc,
  rw [←sub_right_comm, set.sub_mem_Ioc_iff_left, add_right_comm],
  exact sub_to_Ioc_div_zsmul_mem_Ioc hp (a + c) b,
end

lemma to_Ico_div_eq_to_Ico_div_zero (a b : α) : to_Ico_div hp a b = to_Ico_div hp 0 (b - a) :=
by rw [to_Ico_div_sub', zero_add]

lemma to_Ioc_div_eq_to_Ioc_div_zero (a b : α) : to_Ioc_div hp a b = to_Ioc_div hp 0 (b - a) :=
by rw [to_Ioc_div_sub', zero_add]

lemma to_Ico_div_add_right' (a b c : α) : to_Ico_div hp a (b + c) = to_Ico_div hp (a - c) b :=
by rw [←sub_neg_eq_add, to_Ico_div_sub', sub_eq_add_neg]

lemma to_Ioc_div_add_right' (a b c : α) : to_Ioc_div hp a (b + c) = to_Ioc_div hp (a - c) b :=
by rw [←sub_neg_eq_add, to_Ioc_div_sub', sub_eq_add_neg]

lemma to_Ico_div_neg (a b : α) : to_Ico_div hp a (-b) = -(to_Ioc_div hp (-a) b + 1) :=
begin
  suffices : to_Ico_div hp a (-b) = -(to_Ioc_div hp (-(a + p)) b),
  { rwa [neg_add, ←sub_eq_add_neg, ←to_Ioc_div_add_right', to_Ioc_div_add_right] at this },
  rw [← neg_eq_iff_eq_neg, eq_comm],
  apply to_Ioc_div_eq_of_sub_zsmul_mem_Ioc,
  obtain ⟨hc, ho⟩ := sub_to_Ico_div_zsmul_mem_Ico hp a (-b),
  rw [←neg_lt_neg_iff, neg_sub' (-b), neg_neg, ←neg_smul] at ho,
  rw [←neg_le_neg_iff, neg_sub' (-b), neg_neg, ←neg_smul] at hc,
  refine ⟨ho, hc.trans_eq _⟩,
  rw [neg_add, neg_add_cancel_right],
end

lemma to_Ioc_div_neg (a b : α) : to_Ioc_div hp a (-b) = -(to_Ico_div hp (-a) b + 1) :=
by rw [←neg_neg b, to_Ico_div_neg, neg_neg, neg_neg, neg_add', neg_neg, add_sub_cancel]

@[simp] lemma to_Ico_mod_add_zsmul (a b : α) (m : ℤ) :
  to_Ico_mod hp a (b + m • p) = to_Ico_mod hp a b :=
by { rw [to_Ico_mod, to_Ico_div_add_zsmul, to_Ico_mod, add_smul], abel }

@[simp] lemma to_Ioc_mod_add_zsmul (a b : α) (m : ℤ) :
  to_Ioc_mod hp a (b + m • p) = to_Ioc_mod hp a b :=
by { rw [to_Ioc_mod, to_Ioc_div_add_zsmul, to_Ioc_mod, add_smul], abel }

@[simp] lemma to_Ico_mod_zsmul_add (a b : α) (m : ℤ) :
  to_Ico_mod hp a (m • p + b) = to_Ico_mod hp a b :=
by rw [add_comm, to_Ico_mod_add_zsmul]

@[simp] lemma to_Ioc_mod_zsmul_add (a b : α) (m : ℤ) :
  to_Ioc_mod hp a (m • p + b) = to_Ioc_mod hp a b :=
by rw [add_comm, to_Ioc_mod_add_zsmul]

@[simp] lemma to_Ico_mod_sub_zsmul (a b : α) (m : ℤ) :
  to_Ico_mod hp a (b - m • p) = to_Ico_mod hp a b :=
by rw [sub_eq_add_neg, ←neg_smul, to_Ico_mod_add_zsmul]

@[simp] lemma to_Ioc_mod_sub_zsmul (a b : α) (m : ℤ) :
  to_Ioc_mod hp a (b - m • p) = to_Ioc_mod hp a b :=
by rw [sub_eq_add_neg, ←neg_smul, to_Ioc_mod_add_zsmul]

@[simp] lemma to_Ico_mod_add_right (a b : α) : to_Ico_mod hp a (b + p) = to_Ico_mod hp a b :=
by simpa only [one_zsmul] using to_Ico_mod_add_zsmul hp a b 1

@[simp] lemma to_Ioc_mod_add_right (a b : α) : to_Ioc_mod hp a (b + p) = to_Ioc_mod hp a b :=
by simpa only [one_zsmul] using to_Ioc_mod_add_zsmul hp a b 1

@[simp] lemma to_Ico_mod_add_left (a b : α) : to_Ico_mod hp a (p + b) = to_Ico_mod hp a b :=
by rw [add_comm, to_Ico_mod_add_right]

@[simp] lemma to_Ioc_mod_add_left (a b : α) : to_Ioc_mod hp a (p + b) = to_Ioc_mod hp a b :=
by rw [add_comm, to_Ioc_mod_add_right]

@[simp] lemma to_Ico_mod_sub (a b : α) : to_Ico_mod hp a (b - p) = to_Ico_mod hp a b :=
by simpa only [one_zsmul] using to_Ico_mod_sub_zsmul hp a b 1

@[simp] lemma to_Ioc_mod_sub (a b : α) : to_Ioc_mod hp a (b - p) = to_Ioc_mod hp a b :=
by simpa only [one_zsmul] using to_Ioc_mod_sub_zsmul hp a b 1

lemma to_Ico_mod_sub' (a b c : α) : to_Ico_mod hp a (b - c) = to_Ico_mod hp (a + c) b - c :=
by simp_rw [to_Ico_mod, to_Ico_div_sub', sub_right_comm]

lemma to_Ioc_mod_sub' (a b c : α) : to_Ioc_mod hp a (b - c) = to_Ioc_mod hp (a + c) b - c :=
by simp_rw [to_Ioc_mod, to_Ioc_div_sub', sub_right_comm]

lemma to_Ico_mod_add_right' (a b c : α) : to_Ico_mod hp a (b + c) = to_Ico_mod hp (a - c) b + c :=
by simp_rw [to_Ico_mod, to_Ico_div_add_right', sub_add_eq_add_sub]

lemma to_Ioc_mod_add_right' (a b c : α) : to_Ioc_mod hp a (b + c) = to_Ioc_mod hp (a - c) b + c :=
by simp_rw [to_Ioc_mod, to_Ioc_div_add_right', sub_add_eq_add_sub]

lemma to_Ico_mod_neg (a b : α) : to_Ico_mod hp a (-b) = p - to_Ioc_mod hp (-a) b :=
by { simp_rw [to_Ico_mod, to_Ioc_mod, to_Ico_div_neg, neg_smul, add_smul], abel }

lemma to_Ioc_mod_neg (a b : α) : to_Ioc_mod hp a (-b) = p - to_Ico_mod hp (-a) b :=
by { simp_rw [to_Ioc_mod, to_Ico_mod, to_Ioc_div_neg, neg_smul, add_smul], abel }

lemma to_Ico_mod_eq_to_Ico_mod : to_Ico_mod hp a b = to_Ico_mod hp a c ↔ ∃ n : ℤ, c - b = n • p :=
begin
  refine ⟨λ h, ⟨to_Ico_div hp a c - to_Ico_div hp a b, _⟩, λ h, _⟩,
  { conv_lhs { rw [←to_Ico_mod_add_to_Ico_div_zsmul hp a b,
                   ←to_Ico_mod_add_to_Ico_div_zsmul hp a c] },
    rw [h, sub_smul],
    abel },
  { rcases h with ⟨z, hz⟩,
    rw sub_eq_iff_eq_add at hz,
    rw [hz, to_Ico_mod_zsmul_add] }
end

lemma to_Ioc_mod_eq_to_Ioc_mod : to_Ioc_mod hp a b = to_Ioc_mod hp a c ↔ ∃ n : ℤ, c - b = n • p :=
begin
  refine ⟨λ h, ⟨to_Ioc_div hp a c - to_Ioc_div hp a b, _⟩, λ h, _⟩,
  { conv_lhs { rw [←to_Ioc_mod_add_to_Ioc_div_zsmul hp a b,
                   ←to_Ioc_mod_add_to_Ioc_div_zsmul hp a c] },
    rw [h, sub_smul],
    abel },
  { rcases h with ⟨z, hz⟩,
    rw sub_eq_iff_eq_add at hz,
    rw [hz, to_Ioc_mod_zsmul_add] }
end

/-! ### Links between the `Ico` and `Ioc` variants applied to the same element -/

section Ico_Ioc

namespace add_comm_group
variables (a b)
omit hα
/-- `add_comm_group.modeq p a b` means that `b` does not lie in the open interval `(a, a + p)`
modulo `p`.

Equivalently (as shown below), `b` is congruent to `a` modulo `p`, or `to_Ico_mod hp a` disagrees
with `to_Ioc_mod hp a` at `b`, or `to_Ico_div hp a` disagrees with `to_Ioc_div hp a` at `b`. -/
def modeq (p a b : α) : Prop := ∀ z : ℤ, b - z • p ∉ set.Ioo a (a + p)
include hα

lemma tfae_modeq :
  tfae [modeq p a b,
    to_Ico_mod hp a b ≠ to_Ioc_mod hp a b,
    to_Ico_mod hp a b + p = to_Ioc_mod hp a b,
    to_Ico_mod hp a b = a] :=
begin
  rw modeq,
  tfae_have : 2 → 1,
  { rw [←not_exists, not_imp_not],
    exact λ ⟨i, hi⟩,
      ((to_Ico_mod_eq_iff hp).2 ⟨set.Ioo_subset_Ico_self hi, i, (sub_add_cancel b _).symm⟩).trans
      ((to_Ioc_mod_eq_iff hp).2 ⟨set.Ioo_subset_Ioc_self hi, i, (sub_add_cancel b _).symm⟩).symm },
  tfae_have : 3 → 2,
  { intro h, rw [←h, ne, eq_comm, add_right_eq_self], exact hp.ne' },
  tfae_have : 4 → 3,
  { intro h,
    rw [h, eq_comm, to_Ioc_mod_eq_iff, set.right_mem_Ioc],
    refine ⟨lt_add_of_pos_right a hp, to_Ico_div hp a b - 1, _⟩,
    rw [sub_one_zsmul, add_add_add_comm, add_right_neg, add_zero],
    conv_lhs { rw [← to_Ico_mod_add_to_Ico_div_zsmul hp a b, h] } },
  tfae_have : 1 → 4,
  { rw [←not_exists, not_imp_comm],
    have h' := to_Ico_mod_mem_Ico hp a b,
    exact λ h, ⟨_, h'.1.lt_of_ne' h, h'.2⟩ },
  tfae_finish,
end

variables {a b}

lemma modeq_iff_to_Ico_mod_ne_to_Ioc_mod :
  modeq p a b ↔ to_Ico_mod hp a b ≠ to_Ioc_mod hp a b := (tfae_modeq hp a b).out 0 1
lemma modeq_iff_to_Ico_mod_add_period_eq_to_Ioc_mod :
  modeq p a b ↔ to_Ico_mod hp a b + p = to_Ioc_mod hp a b := (tfae_modeq hp a b).out 0 2
lemma modeq_iff_to_Ico_mod_eq_left :
  modeq p a b ↔ to_Ico_mod hp a b = a := (tfae_modeq hp a b).out 0 3

lemma not_modeq_iff_to_Ico_mod_eq_to_Ioc_mod :
  ¬modeq p a b ↔ to_Ico_mod hp a b = to_Ioc_mod hp a b :=
(modeq_iff_to_Ico_mod_ne_to_Ioc_mod _).not_left

lemma modeq_iff_to_Ioc_mod_eq_right : modeq p a b ↔ to_Ioc_mod hp a b = a + p :=
begin
  rw [modeq_iff_to_Ico_mod_ne_to_Ioc_mod hp, ne, to_Ico_mod_eq_iff hp, not_iff_comm],
  obtain ⟨h₁, h₂⟩ := to_Ioc_mod_mem_Ioc hp a b,
  exact ⟨λ h, ⟨⟨h₁.le, h₂.lt_of_ne h⟩, _, (to_Ioc_mod_add_to_Ioc_div_zsmul _ _ _).symm⟩,
    λ h, h.1.2.ne⟩,
end

lemma not_modeq_iff_to_Ico_div_eq_to_Ioc_div :
  ¬modeq p a b ↔ to_Ico_div hp a b = to_Ioc_div hp a b :=
by rw [not_modeq_iff_to_Ico_mod_eq_to_Ioc_mod hp,
       to_Ico_mod, to_Ioc_mod, sub_right_inj, (zsmul_strict_mono_left hp).injective.eq_iff]

lemma modeq_iff_to_Ico_div_eq_to_Ioc_div_add_one :
  modeq p a b ↔ to_Ico_div hp a b = to_Ioc_div hp a b + 1 :=
by rw [modeq_iff_to_Ico_mod_add_period_eq_to_Ioc_mod hp, to_Ico_mod, to_Ioc_mod,
       ← eq_sub_iff_add_eq, sub_sub, sub_right_inj, ← add_one_zsmul,
       (zsmul_strict_mono_left hp).injective.eq_iff]

include hp

lemma modeq_iff_eq_add_zsmul : modeq p a b ↔ ∃ z : ℤ, b = a + z • p :=
begin
  rw [modeq_iff_to_Ico_mod_eq_left hp],
  split; intro h,
  { rw ← h,
    exact ⟨_, (to_Ico_mod_add_to_Ico_div_zsmul _ _ _).symm⟩ },
  { rw [to_Ico_mod_eq_iff, set.left_mem_Ico],
    exact ⟨lt_add_of_pos_right a hp, h⟩, },
end

lemma not_modeq_iff_ne_add_zsmul : ¬modeq p a b ↔ ∀ z : ℤ, b ≠ a + z • p :=
by rw [modeq_iff_eq_add_zsmul hp, not_exists]

lemma modeq_iff_eq_mod_zmultiples :
  modeq p a b ↔ (b : α ⧸ add_subgroup.zmultiples p) = a :=
by simp_rw [modeq_iff_eq_add_zsmul hp, quotient_add_group.eq_iff_sub_mem,
    add_subgroup.mem_zmultiples_iff, eq_sub_iff_add_eq', eq_comm]

lemma not_modeq_iff_ne_mod_zmultiples :
  ¬modeq p a b ↔ (b : α ⧸ add_subgroup.zmultiples p) ≠ a :=
(modeq_iff_eq_mod_zmultiples hp).not

end add_comm_group

lemma Ico_eq_locus_Ioc_eq_Union_Ioo :
  {b | to_Ico_mod hp a b = to_Ioc_mod hp a b} = ⋃ z : ℤ, set.Ioo (a + z • p) (a + p + z • p) :=
begin
  ext1, simp_rw [set.mem_set_of, set.mem_Union, ← set.sub_mem_Ioo_iff_left,
    ←add_comm_group.not_modeq_iff_to_Ico_mod_eq_to_Ioc_mod, add_comm_group.modeq, not_forall,
    not_not],
end

lemma to_Ioc_div_wcovby_to_Ico_div (a b : α) : to_Ioc_div hp a b ⩿ to_Ico_div hp a b :=
begin
  suffices : to_Ioc_div hp a b = to_Ico_div hp a b ∨ to_Ioc_div hp a b + 1 = to_Ico_div hp a b,
  { rwa [wcovby_iff_eq_or_covby, ←order.succ_eq_iff_covby] },
  rw [eq_comm, ←add_comm_group.not_modeq_iff_to_Ico_div_eq_to_Ioc_div,
    eq_comm, ←add_comm_group.modeq_iff_to_Ico_div_eq_to_Ioc_div_add_one],
  exact em' _,
end

lemma to_Ico_mod_le_to_Ioc_mod (a b : α) : to_Ico_mod hp a b ≤ to_Ioc_mod hp a b :=
begin
  rw [to_Ico_mod, to_Ioc_mod, sub_le_sub_iff_left],
  exact zsmul_mono_left hp.le (to_Ioc_div_wcovby_to_Ico_div _ _ _).le
end

lemma to_Ioc_mod_le_to_Ico_mod_add (a b : α) : to_Ioc_mod hp a b ≤ to_Ico_mod hp a b + p :=
begin
  rw [to_Ico_mod, to_Ioc_mod, sub_add, sub_le_sub_iff_left, sub_le_iff_le_add, ←add_one_zsmul,
    (zsmul_strict_mono_left hp).le_iff_le],
  apply (to_Ioc_div_wcovby_to_Ico_div _ _ _).le_succ,
end

/-- If `a` and `b` fall within the same cycle WRT `c`, then they are congruent modulo `p`. -/
@[simp] lemma to_Ico_mod_inj (c : α) :
  to_Ico_mod hp c a = to_Ico_mod hp c b ↔ add_comm_group.modeq p a b :=
begin
  rw [to_Ico_mod_eq_to_Ico_mod, add_comm_group.modeq_iff_eq_add_zsmul hp],
  simp_rw sub_eq_iff_eq_add',
end

alias to_Ico_mod_inj ↔ _ add_comm_group.modeq.to_Ico_mod_eq_to_Ico_mod

lemma add_comm_group.modeq_comm (hp : 0 < p) :
  add_comm_group.modeq p a b ↔ add_comm_group.modeq p b a :=
by rw [←to_Ico_mod_inj hp, eq_comm, to_Ico_mod_inj]; assumption

alias add_comm_group.modeq_comm ↔ add_comm_group.modeq.symm _

end Ico_Ioc

lemma to_Ico_mod_eq_self : to_Ico_mod hp a b = b ↔ b ∈ set.Ico a (a + p) :=
by { rw [to_Ico_mod_eq_iff, and_iff_left], exact ⟨0, by simp⟩ }

lemma to_Ioc_mod_eq_self : to_Ioc_mod hp a b = b ↔ b ∈ set.Ioc a (a + p) :=
by { rw [to_Ioc_mod_eq_iff, and_iff_left], exact ⟨0, by simp⟩ }

@[simp] lemma to_Ico_mod_to_Ico_mod (a₁ a₂ b : α) :
  to_Ico_mod hp a₁ (to_Ico_mod hp a₂ b) = to_Ico_mod hp a₁ b :=
(to_Ico_mod_eq_to_Ico_mod _).2 ⟨to_Ico_div hp a₂ b, self_sub_to_Ico_mod hp a₂ b⟩

@[simp] lemma to_Ico_mod_to_Ioc_mod (a₁ a₂ b : α) :
  to_Ico_mod hp a₁ (to_Ioc_mod hp a₂ b) = to_Ico_mod hp a₁ b :=
(to_Ico_mod_eq_to_Ico_mod _).2 ⟨to_Ioc_div hp a₂ b, self_sub_to_Ioc_mod hp a₂ b⟩

@[simp] lemma to_Ioc_mod_to_Ioc_mod (a₁ a₂ b : α) :
  to_Ioc_mod hp a₁ (to_Ioc_mod hp a₂ b) = to_Ioc_mod hp a₁ b :=
(to_Ioc_mod_eq_to_Ioc_mod _).2 ⟨to_Ioc_div hp a₂ b, self_sub_to_Ioc_mod hp a₂ b⟩

@[simp] lemma to_Ioc_mod_to_Ico_mod (a₁ a₂ b : α) :
  to_Ioc_mod hp a₁ (to_Ico_mod hp a₂ b) = to_Ioc_mod hp a₁ b :=
(to_Ioc_mod_eq_to_Ioc_mod _).2 ⟨to_Ico_div hp a₂ b, self_sub_to_Ico_mod hp a₂ b⟩

lemma to_Ico_mod_zero_sub_comm (a b : α) : to_Ico_mod hp 0 (a - b) = p - to_Ioc_mod hp 0 (b - a) :=
by rw [←neg_sub, to_Ico_mod_neg, neg_zero]

lemma to_Ioc_mod_zero_sub_comm (a b : α) : to_Ioc_mod hp 0 (a - b) = p - to_Ico_mod hp 0 (b - a) :=
by rw [←neg_sub, to_Ioc_mod_neg, neg_zero]

private lemma to_Ixx_mod_add_eq (a b : α) : to_Ico_mod hp 0 (a - b) + to_Ioc_mod hp 0 (b - a) = p :=
by rw [to_Ico_mod_zero_sub_comm, sub_add_cancel]

lemma to_Ico_mod_periodic (a : α) : function.periodic (to_Ico_mod hp a) p :=
to_Ico_mod_add_right hp a

lemma to_Ioc_mod_periodic (a : α) : function.periodic (to_Ioc_mod hp a) p :=
to_Ioc_mod_add_right hp a

section to_move

lemma to_Ico_mod_eq_sub (x₁ x₂ : α) : to_Ico_mod hp x₁ x₂ = to_Ico_mod hp 0 (x₂ - x₁) + x₁ :=
by rw [to_Ico_mod_sub', zero_add, sub_add_cancel]

lemma to_Ioc_mod_eq_sub (x₁ x₂ : α) : to_Ioc_mod hp x₁ x₂ = to_Ioc_mod hp 0 (x₂ - x₁) + x₁ :=
by rw [to_Ioc_mod_sub', zero_add, sub_add_cancel]

private lemma to_Ixx_mod_iff (x₁ x₂ x₃ : α) :
  to_Ico_mod hp x₁ x₂ ≤ to_Ioc_mod hp x₁ x₃ ↔
  to_Ico_mod hp 0 (x₂ - x₁) + to_Ico_mod hp 0 (x₁ - x₃) ≤ p :=
by rw [to_Ico_mod_eq_sub, to_Ioc_mod_eq_sub _ x₁, add_le_add_iff_right, ←neg_sub x₁ x₃,
    to_Ioc_mod_neg, neg_zero, le_sub_iff_add_le]

@[simp] lemma to_Ico_mod_zsmul_add' (a b : α) (m : ℤ) :
  to_Ico_mod hp (a + m • p) b = to_Ico_mod hp a b + m • p :=
by simp only [to_Ico_mod, to_Ico_div_add_zsmul', sub_smul, sub_add]

@[simp] lemma to_Ioc_mod_zsmul_add' (a b : α) (m : ℤ) :
  to_Ioc_mod hp (a + m • p) b = to_Ioc_mod hp a b + m • p :=
by simp only [to_Ioc_mod, to_Ioc_div_add_zsmul', sub_smul, sub_add]

private lemma to_Ixx_mod_cyclic_left (x₁ x₂ x₃ : α)
  (h : to_Ico_mod hp x₁ x₂ ≤ to_Ioc_mod hp x₁ x₃) :
  to_Ico_mod hp x₂ x₃ ≤ to_Ioc_mod hp x₂ x₁ :=
begin
  let x₂' := to_Ico_mod hp x₁ x₂,
  let x₃' := to_Ico_mod hp x₂' x₃,

  suffices hequiv : x₃' ≤ to_Ioc_mod hp x₂' x₁,
  { have hd : ∃ (z : ℤ), x₂ = x₂' + z • p := ((to_Ico_mod_eq_iff hp).1 rfl).2,
    clear_value x₂',
    obtain ⟨m₂, rfl⟩ := hd,
    simpa using hequiv },

  have h : x₂' ≤ to_Ioc_mod hp x₁ x₃' := by simpa,

  have hIoc₂₁ : to_Ioc_mod hp x₂' x₁ = x₁ + p,
  { apply (to_Ioc_mod_eq_iff hp).2,
    refine ⟨_, -1, _⟩,
    { simp only [set.mem_Ioc, add_le_add_iff_right],
      exact ⟨to_Ico_mod_lt_right _ _ _, left_le_to_Ico_mod _ _ _⟩ },
    simp only [add_neg_cancel_right, one_smul, neg_smul] },

  by_cases hc : x₃' ≤ x₁ + p,
  { exact hIoc₂₁.symm.trans_ge hc },

  rw [not_le] at hc,
  have hIoc₁₃ : to_Ioc_mod hp x₁ x₃' = x₃' - p,
  { apply (to_Ioc_mod_eq_iff hp).2,
    refine ⟨_, 1, _⟩, swap,
    { simp only [sub_add_cancel, one_smul] },
    simp only [set.mem_Ioc, add_le_add_iff_right],
    split,
    { exact lt_sub_iff_add_lt.2 hc },
      have w₁ : x₃' - p < x₂' := (sub_lt_iff_lt_add.2 (to_Ico_mod_lt_right _ _ _)),
      have w₂ : x₂' < x₁ + p := to_Ico_mod_lt_right _ _ _,
      exact (le_of_lt w₁).trans (le_of_lt w₂) },

  have h₃ : x₃' - p < x₂' := sub_lt_iff_lt_add.2 (to_Ico_mod_lt_right _ _ x₃),
  have not_h₃ := not_lt.2 (h.trans hIoc₁₃.symm.ge),
  contradiction,
end

private lemma to_Ixx_mod_antisymm {x₁ x₂ x₃ : α}
  (h₁₂₃ : to_Ico_mod hp x₁ x₂ ≤ to_Ioc_mod hp x₁ x₃)
  (h₁₃₂ : to_Ico_mod hp x₁ x₃ ≤ to_Ioc_mod hp x₁ x₂) :
  add_comm_group.modeq p x₂ x₁ ∨ add_comm_group.modeq p x₃ x₂ ∨ add_comm_group.modeq p x₁ x₃ :=
begin
  by_contra' h,
  rw add_comm_group.modeq_comm hp at h,
  rw ←(add_comm_group.not_modeq_iff_to_Ico_mod_eq_to_Ioc_mod hp).mp h.2.2 at h₁₂₃,
  rw ←(add_comm_group.not_modeq_iff_to_Ico_mod_eq_to_Ioc_mod hp).mp h.1 at h₁₃₂,
  exact h.2.1 ((to_Ico_mod_inj hp _).mp (h₁₃₂.antisymm h₁₂₃)),
end

/-- From this I think it's a lot easier to verify the axioms; another essential ingredient is the
lemma saying {x-y} + {y-x} = period if x ≠ y (and = 0 if x = y). Thus if x ≠ y and y ≠ z then
({x-y} + {y-z}) + ({z-y} + {y-x}) = 2 * period, so one of {x-y} + {y-z} and {z-y} + {y-x} must be
`≤ period`, proving btw_total; -/
private lemma to_Ixx_mod_total' (x y z : α) :
  to_Ico_mod hp y x ≤ to_Ioc_mod hp y z ∨ to_Ico_mod hp y z ≤ to_Ioc_mod hp y x :=
begin
  have := congr_arg2 (+) (to_Ixx_mod_add_eq hp x y) (to_Ixx_mod_add_eq hp z y),
  rw [add_add_add_comm, add_comm (to_Ioc_mod _ _ _), add_add_add_comm, ←two_nsmul] at this,
  replace := min_le_of_add_le_two_nsmul this.le,
  rw min_le_iff at this,
  rw [to_Ixx_mod_iff, to_Ixx_mod_iff],
  refine this.imp (le_trans $ add_le_add_left _ _) (le_trans $ add_le_add_left _ _),
  { apply to_Ico_mod_le_to_Ioc_mod },
  { apply to_Ico_mod_le_to_Ioc_mod },
end

private lemma to_Ixx_mod_total (x y z : α) :
  to_Ico_mod hp x y ≤ to_Ioc_mod hp x z ∨
  to_Ico_mod hp z y ≤ to_Ioc_mod hp z x :=
(to_Ixx_mod_total' _ _ _ _).imp_right $ to_Ixx_mod_cyclic_left _ _ _ _

private lemma to_Ixx_mod_trans {x₁ x₂ x₃ x₄ : α}
  (h₁₂₃ : to_Ico_mod hp x₁ x₂ ≤ to_Ioc_mod hp x₁ x₃
    ∧ ¬to_Ico_mod hp x₃ x₂ ≤ to_Ioc_mod hp x₃ x₁)
  (h₂₃₄ : to_Ico_mod hp x₂ x₄ ≤ to_Ioc_mod hp x₂ x₃
    ∧ ¬to_Ico_mod hp x₃ x₄ ≤ to_Ioc_mod hp x₃ x₂) :
  to_Ico_mod hp x₁ x₄ ≤ to_Ioc_mod hp x₁ x₃
    ∧ ¬to_Ico_mod hp x₃ x₄ ≤ to_Ioc_mod hp x₃ x₁ :=
begin
  have h₁₂₃' := to_Ixx_mod_cyclic_left _ _ _ _ (to_Ixx_mod_cyclic_left _ _ _ _ h₁₂₃.1),
  have h₂₃₄' := to_Ixx_mod_cyclic_left _ _ _ _ (to_Ixx_mod_cyclic_left _ _ _ _ h₂₃₄.1),

  split, swap,
  { rw not_le,
    have := to_Ico_mod_le_to_Ioc_mod hp x₃ x₂,
    exact ((not_le.1 h₁₂₃.2).trans_le this).trans (not_le.1 h₂₃₄.2) },

  suffices h : to_Ico_mod hp x₃ x₂ = to_Ioc_mod hp x₃ x₂,
  { exact to_Ixx_mod_cyclic_left _ _ _ _ ((h₁₂₃'.trans $ ge_of_eq h).trans h₂₃₄') },

  by_contra,
  have hIco₃₂ : to_Ico_mod hp x₃ x₂ = x₃ := ((add_comm_group.tfae_modeq hp x₃ x₂).out 3 1).mpr h,
  have hIco₃₁ : x₃ < to_Ioc_mod hp x₃ x₁ := left_lt_to_Ioc_mod _ _ _,
  exact h₁₂₃.2 (hIco₃₂.le.trans hIco₃₁.le),
end

end to_move

/-- `to_Ico_mod` as an equiv from the quotient. -/
@[simps symm_apply]
def quotient_add_group.equiv_Ico_mod (a : α) :
  (α ⧸ add_subgroup.zmultiples p) ≃ set.Ico a (a + p) :=
{ to_fun := λ b, ⟨(to_Ico_mod_periodic hp a).lift b,
    quotient_add_group.induction_on' b $ to_Ico_mod_mem_Ico hp a⟩,
  inv_fun := coe,
  right_inv := λ b, subtype.ext $ (to_Ico_mod_eq_self hp).mpr b.prop,
  left_inv := λ b, begin
    induction b using quotient_add_group.induction_on',
    dsimp,
    rw [quotient_add_group.eq_iff_sub_mem, to_Ico_mod_sub_self],
    apply add_subgroup.zsmul_mem_zmultiples,
  end }

@[simp]
lemma quotient_add_group.equiv_Ico_mod_coe (a b : α) :
  quotient_add_group.equiv_Ico_mod hp a ↑b = ⟨to_Ico_mod hp a b, to_Ico_mod_mem_Ico hp a _⟩ :=
rfl

@[simp]
lemma quotient_add_group.equiv_Ico_mod_zero (a : α) :
  quotient_add_group.equiv_Ico_mod hp a 0 = ⟨to_Ico_mod hp a 0, to_Ico_mod_mem_Ico hp a _⟩ :=
rfl

/-- `to_Ioc_mod` as an equiv from the quotient. -/
@[simps symm_apply]
def quotient_add_group.equiv_Ioc_mod (a : α) :
  (α ⧸ add_subgroup.zmultiples p) ≃ set.Ioc a (a + p) :=
{ to_fun := λ b, ⟨(to_Ioc_mod_periodic hp a).lift b,
    quotient_add_group.induction_on' b $ to_Ioc_mod_mem_Ioc hp a⟩,
  inv_fun := coe,
  right_inv := λ b, subtype.ext $ (to_Ioc_mod_eq_self hp).mpr b.prop,
  left_inv := λ b, begin
    induction b using quotient_add_group.induction_on',
    dsimp,
    rw [quotient_add_group.eq_iff_sub_mem, to_Ioc_mod_sub_self],
    apply add_subgroup.zsmul_mem_zmultiples,
  end }

@[simp]
lemma quotient_add_group.equiv_Ioc_mod_coe (a b : α) :
  quotient_add_group.equiv_Ioc_mod hp a ↑b = ⟨to_Ioc_mod hp a b, to_Ioc_mod_mem_Ioc hp a _⟩ :=
rfl

@[simp]
lemma quotient_add_group.equiv_Ioc_mod_zero (a : α) :
  quotient_add_group.equiv_Ioc_mod hp a 0 = ⟨to_Ioc_mod hp a 0, to_Ioc_mod_mem_Ioc hp a _⟩ :=
rfl

namespace quotient_add_group
variables [hp' : fact (0 < p)]
include hp'

instance : has_btw (α ⧸ add_subgroup.zmultiples p) :=
{ btw := λ x₁ x₂ x₃, (equiv_Ico_mod hp'.out 0 (x₂ - x₁) : α) ≤ equiv_Ioc_mod hp'.out 0 (x₃ - x₁) }

lemma btw_coe_iff' (x₁ x₂ x₃ : α) : has_btw.btw (x₁ : α ⧸ add_subgroup.zmultiples p) x₂ x₃ ↔
    to_Ico_mod hp'.out 0 (x₂ - x₁) ≤ to_Ioc_mod hp'.out 0 (x₃ - x₁) :=
iff.rfl

-- maybe harder to prove with than the primed one?
lemma btw_coe_iff (x₁ x₂ x₃ : α) : has_btw.btw (x₁ : α ⧸ add_subgroup.zmultiples p) x₂ x₃ ↔
    to_Ico_mod hp'.out x₁ x₂ ≤ to_Ioc_mod hp'.out x₁ x₃ :=
by rw [btw_coe_iff', to_Ioc_mod_sub', to_Ico_mod_sub', zero_add, sub_le_sub_iff_right]

instance circular_preorder : circular_preorder (α ⧸ add_subgroup.zmultiples p) :=
{ btw_refl := λ x, show _ ≤ _, by simp [sub_self, hp'.out.le],
  btw_cyclic_left := λ x₁ x₂ x₃ h, begin
    induction x₁ using quotient_add_group.induction_on',
    induction x₂ using quotient_add_group.induction_on',
    induction x₃ using quotient_add_group.induction_on',
    simp_rw [btw_coe_iff] at h ⊢,
    apply to_Ixx_mod_cyclic_left _ _ _ _ h,
  end,
  sbtw := _,
  sbtw_iff_btw_not_btw := λ _ _ _, iff.rfl,
  sbtw_trans_left := λ x₁ x₂ x₃ x₄ (h₁₂₃ : _ ∧ _) (h₂₃₄ : _ ∧ _), show _ ∧ _, begin
    induction x₁ using quotient_add_group.induction_on',
    induction x₂ using quotient_add_group.induction_on',
    induction x₃ using quotient_add_group.induction_on',
    induction x₄ using quotient_add_group.induction_on',
    simp_rw [btw_coe_iff] at h₁₂₃ h₂₃₄ ⊢,
    apply to_Ixx_mod_trans _ h₁₂₃ h₂₃₄,
  end }

instance circular_order : circular_order (α ⧸ add_subgroup.zmultiples p) :=
{ btw_antisymm := λ x₁ x₂ x₃ h₁₂₃ h₃₂₁, begin
    induction x₁ using quotient_add_group.induction_on',
    induction x₂ using quotient_add_group.induction_on',
    induction x₃ using quotient_add_group.induction_on',
    rw btw_cyclic at h₃₂₁,
    simp_rw [btw_coe_iff] at h₁₂₃ h₃₂₁,
    simp_rw ←add_comm_group.modeq_iff_eq_mod_zmultiples hp'.out,
    exact to_Ixx_mod_antisymm _ h₁₂₃ h₃₂₁,
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

variables {α : Type*} [linear_ordered_field α] [floor_ring α] {p : α} (hp : 0 < p)

lemma to_Ico_div_eq_floor (a b : α) : to_Ico_div hp a b = ⌊(b - a) / p⌋ :=
begin
  refine to_Ico_div_eq_of_sub_zsmul_mem_Ico hp _,
  rw [set.mem_Ico, zsmul_eq_mul, ←sub_nonneg, add_comm, sub_right_comm, ←sub_lt_iff_lt_add,
    sub_right_comm _ _ a],
  exact ⟨int.sub_floor_div_mul_nonneg _ hp, int.sub_floor_div_mul_lt _ hp⟩,
end

lemma to_Ioc_div_eq_neg_floor (a b : α) : to_Ioc_div hp a b = -⌊(a + p - b) / p⌋ :=
begin
  refine to_Ioc_div_eq_of_sub_zsmul_mem_Ioc hp _,
  rw [set.mem_Ioc, zsmul_eq_mul, int.cast_neg, neg_mul, sub_neg_eq_add, ←sub_nonneg,
    sub_add_eq_sub_sub],
  refine ⟨_, int.sub_floor_div_mul_nonneg _ hp⟩,
  rw [←add_lt_add_iff_right p, add_assoc, add_comm b, ←sub_lt_iff_lt_add, add_comm (_ * _),
      ←sub_lt_iff_lt_add],
  exact int.sub_floor_div_mul_lt _ hp
end

lemma to_Ico_div_zero_one (b : α) : to_Ico_div (zero_lt_one' α) 0 b = ⌊b⌋ :=
by simp [to_Ico_div_eq_floor]

lemma to_Ico_mod_eq_add_fract_mul (a b : α) : to_Ico_mod hp a b = a + int.fract ((b - a) / p) * p :=
begin
  rw [to_Ico_mod, to_Ico_div_eq_floor, int.fract],
  field_simp [hp.ne.symm],
  ring
end

lemma to_Ico_mod_eq_fract_mul (b : α) : to_Ico_mod hp 0 b = int.fract (b / p) * p :=
by simp [to_Ico_mod_eq_add_fract_mul]

lemma to_Ioc_mod_eq_sub_fract_mul (a b : α) :
  to_Ioc_mod hp a b = a + p - int.fract ((a + p - b) / p) * p :=
begin
  rw [to_Ioc_mod, to_Ioc_div_eq_neg_floor, int.fract],
  field_simp [hp.ne.symm],
  ring
end

lemma to_Ico_mod_zero_one (b : α) : to_Ico_mod (zero_lt_one' α) 0 b = int.fract b :=
by simp [to_Ico_mod_eq_add_fract_mul]

end linear_ordered_field

/-! ### Lemmas about unions of translates of intervals -/
section union

open set int

section linear_ordered_add_comm_group

variables {α : Type*} [linear_ordered_add_comm_group α] [archimedean α] {p : α} (hp : 0 < p) (a : α)
include hp

lemma Union_Ioc_add_zsmul : (⋃ (n : ℤ), Ioc (a + n • p) (a + (n + 1) • p)) = univ :=
begin
  refine eq_univ_iff_forall.mpr (λ b, mem_Union.mpr _),
  rcases sub_to_Ioc_div_zsmul_mem_Ioc hp a b with ⟨hl, hr⟩,
  refine ⟨to_Ioc_div hp a b, ⟨lt_sub_iff_add_lt.mp hl, _⟩⟩,
  rw [add_smul, one_smul, ←add_assoc],
  convert sub_le_iff_le_add.mp hr using 1, abel,
end

lemma Union_Ico_add_zsmul : (⋃ (n : ℤ), Ico (a + n • p) (a + (n + 1) • p)) = univ :=
begin
  refine eq_univ_iff_forall.mpr (λ b, mem_Union.mpr _),
  rcases sub_to_Ico_div_zsmul_mem_Ico hp a b with ⟨hl, hr⟩,
  refine ⟨to_Ico_div hp a b, ⟨le_sub_iff_add_le.mp hl, _⟩⟩,
  rw [add_smul, one_smul, ←add_assoc],
  convert sub_lt_iff_lt_add.mp hr using 1, abel,
end

lemma Union_Icc_add_zsmul : (⋃ (n : ℤ), Icc (a + n • p) (a + (n + 1) • p)) = univ :=
by simpa only [Union_Ioc_add_zsmul hp a, univ_subset_iff] using
  Union_mono (λ n : ℤ, (Ioc_subset_Icc_self : Ioc (a + n • p) (a + (n + 1) • p) ⊆ Icc _ _))

lemma Union_Ioc_zsmul : (⋃ (n : ℤ), Ioc (n • p) ((n + 1) • p)) = univ :=
by simpa only [zero_add] using Union_Ioc_add_zsmul hp 0

lemma Union_Ico_zsmul : (⋃ (n : ℤ), Ico (n • p) ((n + 1) • p)) = univ :=
by simpa only [zero_add] using Union_Ico_add_zsmul hp 0

lemma Union_Icc_zsmul : (⋃ (n : ℤ), Icc (n • p) ((n + 1) • p)) = univ :=
by simpa only [zero_add] using Union_Icc_add_zsmul hp 0

end linear_ordered_add_comm_group

section linear_ordered_ring

variables {α : Type*} [linear_ordered_ring α] [archimedean α] (a : α)

lemma Union_Ioc_add_int_cast : (⋃ (n : ℤ), Ioc (a + n) (a + n + 1)) = set.univ :=
by simpa only [zsmul_one, int.cast_add, int.cast_one, ←add_assoc]
  using Union_Ioc_add_zsmul zero_lt_one a

lemma Union_Ico_add_int_cast : (⋃ (n : ℤ), Ico (a + n) (a + n + 1)) = set.univ :=
by simpa only [zsmul_one, int.cast_add, int.cast_one, ←add_assoc]
  using Union_Ico_add_zsmul zero_lt_one a

lemma Union_Icc_add_int_cast : (⋃ (n : ℤ), Icc (a + n) (a + n + 1)) = set.univ :=
by simpa only [zsmul_one, int.cast_add, int.cast_one, ←add_assoc]
  using Union_Icc_add_zsmul zero_lt_one a

variables (α)

lemma Union_Ioc_int_cast : (⋃ (n : ℤ), Ioc (n : α) (n + 1)) = set.univ :=
by simpa only [zero_add] using Union_Ioc_add_int_cast (0 : α)

lemma Union_Ico_int_cast : (⋃ (n : ℤ), Ico (n : α) (n + 1)) = set.univ :=
by simpa only [zero_add] using Union_Ico_add_int_cast (0 : α)

lemma Union_Icc_int_cast : (⋃ (n : ℤ), Icc (n : α) (n + 1)) = set.univ :=
by simpa only [zero_add] using Union_Icc_add_int_cast (0 : α)

end linear_ordered_ring

end union
