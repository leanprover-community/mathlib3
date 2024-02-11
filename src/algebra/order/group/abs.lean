/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import algebra.abs
import algebra.order.group.order_iso
import order.min_max

/-!
# Absolute values in ordered groups.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {α : Type*}
open function

section covariant_add_le

section has_neg

/-- `abs a` is the absolute value of `a`. -/
@[to_additive "`abs a` is the absolute value of `a`",
  priority 100] -- see Note [lower instance priority]
instance has_inv.to_has_abs [has_inv α] [has_sup α] : has_abs α := ⟨λ a, a ⊔ a⁻¹⟩

@[to_additive] lemma abs_eq_sup_inv [has_inv α] [has_sup α] (a : α) : |a| = a ⊔ a⁻¹ := rfl

variables [has_neg α] [linear_order α] {a b: α}

lemma abs_eq_max_neg : abs a = max a (-a) :=
rfl

lemma abs_choice (x : α) : |x| = x ∨ |x| = -x := max_choice _ _

lemma abs_le' : |a| ≤ b ↔ a ≤ b ∧ -a ≤ b := max_le_iff

lemma le_abs : a ≤ |b| ↔ a ≤ b ∨ a ≤ -b := le_max_iff

lemma le_abs_self (a : α) : a ≤ |a| := le_max_left _ _

lemma neg_le_abs_self (a : α) : -a ≤ |a| := le_max_right _ _

lemma lt_abs : a < |b| ↔ a < b ∨ a < -b := lt_max_iff

theorem abs_le_abs (h₀ : a ≤ b) (h₁ : -a ≤ b) : |a| ≤ |b| :=
(abs_le'.2 ⟨h₀, h₁⟩).trans (le_abs_self b)

lemma abs_by_cases (P : α → Prop) {a : α} (h1 : P a) (h2 : P (-a)) : P (|a|) :=
sup_ind _ _ h1 h2

end has_neg

section add_group
variables [add_group α] [linear_order α]

@[simp] lemma abs_neg (a : α) : | -a| = |a| :=
begin
  rw [abs_eq_max_neg, max_comm, neg_neg, abs_eq_max_neg]
end

lemma eq_or_eq_neg_of_abs_eq {a b : α} (h : |a| = b) : a = b ∨ a = -b :=
by simpa only [← h, eq_comm, neg_eq_iff_eq_neg] using abs_choice a

lemma abs_eq_abs {a b : α} : |a| = |b| ↔ a = b ∨ a = -b :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { obtain rfl | rfl := eq_or_eq_neg_of_abs_eq h;
    simpa only [neg_eq_iff_eq_neg, neg_inj, or.comm] using abs_choice b },
  { cases h; simp only [h, abs_neg] },
end

lemma abs_sub_comm (a b : α) : |a - b| = |b - a| :=
calc  |a - b| = | - (b - a)| : congr_arg _ (neg_sub b a).symm
          ... = |b - a|      : abs_neg (b - a)

variables [covariant_class α α (+) (≤)] {a b c : α}

lemma abs_of_nonneg (h : 0 ≤ a) : |a| = a :=
max_eq_left $ (neg_nonpos.2 h).trans h

lemma abs_of_pos (h : 0 < a) : |a| = a :=
abs_of_nonneg h.le

lemma abs_of_nonpos (h : a ≤ 0) : |a| = -a :=
max_eq_right $ h.trans (neg_nonneg.2 h)

lemma abs_of_neg (h : a < 0) : |a| = -a :=
abs_of_nonpos h.le

lemma abs_le_abs_of_nonneg (ha : 0 ≤ a) (hab : a ≤ b) : |a| ≤ |b| :=
by rwa [abs_of_nonneg ha, abs_of_nonneg (ha.trans hab)]

@[simp] lemma abs_zero : |0| = (0:α) :=
abs_of_nonneg le_rfl

@[simp] lemma abs_pos : 0 < |a| ↔ a ≠ 0 :=
begin
  rcases lt_trichotomy a 0 with (ha|rfl|ha),
  { simp [abs_of_neg ha, neg_pos, ha.ne, ha] },
  { simp },
  { simp [abs_of_pos ha, ha, ha.ne.symm] }
end

lemma abs_pos_of_pos (h : 0 < a) : 0 < |a| := abs_pos.2 h.ne.symm

lemma abs_pos_of_neg (h : a < 0) : 0 < |a| := abs_pos.2 h.ne

lemma neg_abs_le_self (a : α) : -|a| ≤ a :=
begin
  cases le_total 0 a with h h,
  { calc -|a| = - a   : congr_arg (has_neg.neg) (abs_of_nonneg h)
            ... ≤ 0     : neg_nonpos.mpr h
            ... ≤ a     : h },
  { calc -|a| = - - a : congr_arg (has_neg.neg) (abs_of_nonpos h)
            ... ≤ a     : (neg_neg a).le }
end

lemma add_abs_nonneg (a : α) : 0 ≤ a + |a| :=
begin
  rw ←add_right_neg a,
  apply add_le_add_left,
  exact (neg_le_abs_self a),
end

lemma neg_abs_le_neg (a : α) : -|a| ≤ -a :=
by simpa using neg_abs_le_self (-a)

@[simp] lemma abs_nonneg (a : α) : 0 ≤ |a| :=
(le_total 0 a).elim (λ h, h.trans (le_abs_self a)) (λ h, (neg_nonneg.2 h).trans $ neg_le_abs_self a)

@[simp] lemma abs_abs (a : α) : | |a| | = |a| :=
abs_of_nonneg $ abs_nonneg a

@[simp] lemma abs_eq_zero : |a| = 0 ↔ a = 0 :=
decidable.not_iff_not.1 $ ne_comm.trans $ (abs_nonneg a).lt_iff_ne.symm.trans abs_pos

@[simp] lemma abs_nonpos_iff {a : α} : |a| ≤ 0 ↔ a = 0 :=
(abs_nonneg a).le_iff_eq.trans abs_eq_zero

variable [covariant_class α α (swap (+)) (≤)]

lemma abs_le_abs_of_nonpos (ha : a ≤ 0) (hab : b ≤ a) : |a| ≤ |b| :=
by { rw [abs_of_nonpos ha, abs_of_nonpos (hab.trans ha)], exact neg_le_neg_iff.mpr hab }

lemma abs_lt : |a| < b ↔ - b < a ∧ a < b :=
max_lt_iff.trans $ and.comm.trans $ by rw [neg_lt]

lemma neg_lt_of_abs_lt (h : |a| < b) : -b < a := (abs_lt.mp h).1

lemma lt_of_abs_lt (h : |a| < b) : a < b := (abs_lt.mp h).2

lemma max_sub_min_eq_abs' (a b : α) : max a b - min a b = |a - b| :=
begin
  cases le_total a b with ab ba,
  { rw [max_eq_right ab, min_eq_left ab, abs_of_nonpos, neg_sub], rwa sub_nonpos },
  { rw [max_eq_left ba, min_eq_right ba, abs_of_nonneg], rwa sub_nonneg }
end

lemma max_sub_min_eq_abs (a b : α) : max a b - min a b = |b - a| :=
by { rw abs_sub_comm, exact max_sub_min_eq_abs' _ _ }

end add_group

end covariant_add_le

section linear_ordered_add_comm_group

variables [linear_ordered_add_comm_group α] {a b c d : α}

lemma abs_le : |a| ≤ b ↔ - b ≤ a ∧ a ≤ b := by rw [abs_le', and.comm, neg_le]

lemma le_abs' : a ≤ |b| ↔ b ≤ -a ∨ a ≤ b := by rw [le_abs, or.comm, le_neg]

lemma neg_le_of_abs_le (h : |a| ≤ b) : -b ≤ a := (abs_le.mp h).1

lemma le_of_abs_le (h : |a| ≤ b) : a ≤ b := (abs_le.mp h).2

@[to_additive] lemma apply_abs_le_mul_of_one_le' {β : Type*} [mul_one_class β] [preorder β]
  [covariant_class β β (*) (≤)] [covariant_class β β (swap (*)) (≤)] {f : α → β} {a : α}
  (h₁ : 1 ≤ f a) (h₂ : 1 ≤ f (-a)) :
  f (|a|) ≤ f a * f (-a) :=
(le_total a 0).by_cases (λ ha, (abs_of_nonpos ha).symm ▸ le_mul_of_one_le_left' h₁)
  (λ ha, (abs_of_nonneg ha).symm ▸ le_mul_of_one_le_right' h₂)

@[to_additive] lemma apply_abs_le_mul_of_one_le {β : Type*} [mul_one_class β] [preorder β]
  [covariant_class β β (*) (≤)] [covariant_class β β (swap (*)) (≤)] {f : α → β}
  (h : ∀ x, 1 ≤ f x) (a : α) :
  f (|a|) ≤ f a * f (-a) :=
apply_abs_le_mul_of_one_le' (h _) (h _)

/--
The **triangle inequality** in `linear_ordered_add_comm_group`s.
-/
lemma abs_add (a b : α) : |a + b| ≤ |a| + |b| :=
abs_le.2 ⟨(neg_add (|a|) (|b|)).symm ▸
  add_le_add (neg_le.2 $ neg_le_abs_self _) (neg_le.2 $ neg_le_abs_self _),
  add_le_add (le_abs_self _) (le_abs_self _)⟩

lemma abs_add' (a b : α) : |a| ≤ |b| + |b + a| :=
by simpa using abs_add (-b) (b + a)

theorem abs_sub (a b : α) :
  |a - b| ≤ |a| + |b| :=
by { rw [sub_eq_add_neg, ←abs_neg b], exact abs_add a _ }

lemma abs_sub_le_iff : |a - b| ≤ c ↔ a - b ≤ c ∧ b - a ≤ c :=
by rw [abs_le, neg_le_sub_iff_le_add, sub_le_iff_le_add', and_comm, sub_le_iff_le_add']

lemma abs_sub_lt_iff : |a - b| < c ↔ a - b < c ∧ b - a < c :=
by rw [abs_lt, neg_lt_sub_iff_lt_add', sub_lt_iff_lt_add', and_comm, sub_lt_iff_lt_add']

lemma sub_le_of_abs_sub_le_left (h : |a - b| ≤ c) : b - c ≤ a :=
sub_le_comm.1 $ (abs_sub_le_iff.1 h).2

lemma sub_le_of_abs_sub_le_right (h : |a - b| ≤ c) : a - c ≤ b :=
sub_le_of_abs_sub_le_left (abs_sub_comm a b ▸ h)

lemma sub_lt_of_abs_sub_lt_left (h : |a - b| < c) : b - c < a :=
sub_lt_comm.1 $ (abs_sub_lt_iff.1 h).2

lemma sub_lt_of_abs_sub_lt_right (h : |a - b| < c) : a - c < b :=
sub_lt_of_abs_sub_lt_left (abs_sub_comm a b ▸ h)

lemma abs_sub_abs_le_abs_sub (a b : α) : |a| - |b| ≤ |a - b| :=
sub_le_iff_le_add.2 $
calc |a| = |a - b + b|     : by rw [sub_add_cancel]
       ... ≤ |a - b| + |b| : abs_add _ _

lemma abs_abs_sub_abs_le_abs_sub (a b : α) : | |a| - |b| | ≤ |a - b| :=
abs_sub_le_iff.2 ⟨abs_sub_abs_le_abs_sub _ _, by rw abs_sub_comm; apply abs_sub_abs_le_abs_sub⟩

lemma abs_eq (hb : 0 ≤ b) : |a| = b ↔ a = b ∨ a = -b :=
begin
  refine ⟨eq_or_eq_neg_of_abs_eq, _⟩,
  rintro (rfl|rfl); simp only [abs_neg, abs_of_nonneg hb]
end

lemma abs_le_max_abs_abs (hab : a ≤ b) (hbc : b ≤ c) : |b| ≤ max (|a|) (|c|) :=
abs_le'.2
  ⟨by simp [hbc.trans (le_abs_self c)],
   by simp [(neg_le_neg_iff.mpr hab).trans (neg_le_abs_self a)]⟩

lemma min_abs_abs_le_abs_max : min (|a|) (|b|) ≤ |max a b| :=
(le_total a b).elim
  (λ h, (min_le_right _ _).trans_eq $ congr_arg _ (max_eq_right h).symm)
  (λ h, (min_le_left _ _).trans_eq $ congr_arg _ (max_eq_left h).symm)

lemma min_abs_abs_le_abs_min : min (|a|) (|b|) ≤ |min a b| :=
(le_total a b).elim
  (λ h, (min_le_left _ _).trans_eq $ congr_arg _ (min_eq_left h).symm)
  (λ h, (min_le_right _ _).trans_eq $ congr_arg _ (min_eq_right h).symm)

lemma abs_max_le_max_abs_abs : |max a b| ≤ max (|a|) (|b|) :=
(le_total a b).elim
  (λ h, (congr_arg _ $ max_eq_right h).trans_le $ le_max_right _ _)
  (λ h, (congr_arg _ $ max_eq_left h).trans_le $ le_max_left _ _)

lemma abs_min_le_max_abs_abs : |min a b| ≤ max (|a|) (|b|) :=
(le_total a b).elim
  (λ h, (congr_arg _ $ min_eq_left h).trans_le $ le_max_left _ _)
  (λ h, (congr_arg _ $ min_eq_right h).trans_le $ le_max_right _ _)

lemma eq_of_abs_sub_eq_zero {a b : α} (h : |a - b| = 0) : a = b :=
sub_eq_zero.1 $ abs_eq_zero.1 h

lemma abs_sub_le (a b c : α) : |a - c| ≤ |a - b| + |b - c| :=
calc
    |a - c| = |a - b + (b - c)|     : by rw [sub_add_sub_cancel]
            ... ≤ |a - b| + |b - c| : abs_add _ _

lemma abs_add_three (a b c : α) : |a + b + c| ≤ |a| + |b| + |c| :=
(abs_add _ _).trans (add_le_add_right (abs_add _ _) _)

lemma dist_bdd_within_interval {a b lb ub : α} (hal : lb ≤ a) (hau : a ≤ ub)
      (hbl : lb ≤ b) (hbu : b ≤ ub) : |a - b| ≤ ub - lb :=
abs_sub_le_iff.2 ⟨sub_le_sub hau hbl, sub_le_sub hbu hal⟩

lemma eq_of_abs_sub_nonpos (h : |a - b| ≤ 0) : a = b :=
eq_of_abs_sub_eq_zero (le_antisymm h (abs_nonneg (a - b)))

end linear_ordered_add_comm_group
