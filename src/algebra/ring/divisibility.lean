/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import algebra.divisibility.basic
import algebra.hom.equiv.basic
import algebra.ring.defs

/-!
# Lemmas about divisibility in rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {α β : Type*}

section distrib_semigroup
variables [has_add α] [semigroup α]

theorem dvd_add [left_distrib_class α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b + c :=
dvd.elim h₁ (λ d hd, dvd.elim h₂ (λ e he, dvd.intro (d + e) (by simp [left_distrib, hd, he])))

alias dvd_add ← has_dvd.dvd.add

end distrib_semigroup

@[simp] theorem two_dvd_bit0 [semiring α] {a : α} : 2 ∣ bit0 a := ⟨a, bit0_eq_two_mul _⟩

section non_unital_comm_semiring
variables [non_unital_comm_semiring α] [non_unital_comm_semiring β] {a b c : α}

lemma has_dvd.dvd.linear_comb {d x y : α} (hdx : d ∣ x) (hdy : d ∣ y) (a b : α) :
  d ∣ (a * x + b * y) :=
dvd_add (hdx.mul_left a) (hdy.mul_left b)

end non_unital_comm_semiring


section semigroup

variables [semigroup α] [has_distrib_neg α] {a b c : α}

/-- An element `a` of a semigroup with a distributive negation divides the negation of an element
`b` iff `a` divides `b`. -/
@[simp] lemma dvd_neg : a ∣ -b ↔ a ∣ b := (equiv.neg _).exists_congr_left.trans $ by simpa

/-- The negation of an element `a` of a semigroup with a distributive negation divides another
element `b` iff `a` divides `b`. -/
@[simp] lemma neg_dvd : -a ∣ b ↔ a ∣ b := (equiv.neg _).exists_congr_left.trans $ by simpa

alias neg_dvd ↔ has_dvd.dvd.of_neg_left has_dvd.dvd.neg_left
alias dvd_neg ↔ has_dvd.dvd.of_neg_right has_dvd.dvd.neg_right

end semigroup

section non_unital_ring
variables [non_unital_ring α] {a b c : α}

theorem dvd_sub (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b - c :=
by simpa only [←sub_eq_add_neg] using h₁.add h₂.neg_right

alias dvd_sub ← has_dvd.dvd.sub

/-- If an element `a` divides another element `c` in a ring, `a` divides the sum of another element
`b` with `c` iff `a` divides `b`. -/
theorem dvd_add_left (h : a ∣ c) : a ∣ b + c ↔ a ∣ b :=
⟨λ H, by simpa only [add_sub_cancel] using dvd_sub H h, λ h₂, dvd_add h₂ h⟩

/-- If an element `a` divides another element `b` in a ring, `a` divides the sum of `b` and another
element `c` iff `a` divides `c`. -/
theorem dvd_add_right (h : a ∣ b) : a ∣ b + c ↔ a ∣ c := by rw add_comm; exact dvd_add_left h

/-- If an element `a` divides another element `c` in a ring, `a` divides the difference of another
element `b` with `c` iff `a` divides `b`. -/
theorem dvd_sub_left (h : a ∣ c) : a ∣ b - c ↔ a ∣ b :=
by simpa only [←sub_eq_add_neg] using dvd_add_left (dvd_neg.2 h)

/-- If an element `a` divides another element `b` in a ring, `a` divides the difference of `b` and
another element `c` iff `a` divides `c`. -/
theorem dvd_sub_right (h : a ∣ b) : a ∣ b - c ↔ a ∣ c :=
by rw [sub_eq_add_neg, dvd_add_right h, dvd_neg]

lemma dvd_iff_dvd_of_dvd_sub (h : a ∣ b - c) : a ∣ b ↔ a ∣ c :=
by rw [←sub_add_cancel b c, dvd_add_right h]

lemma dvd_sub_comm : a ∣ b - c ↔ a ∣ c - b := by rw [←dvd_neg, neg_sub]

lemma dvd_sub_comm : a ∣ b - c ↔ a ∣ c - b := by rw [←dvd_neg, neg_sub]

end non_unital_ring

section ring
variables [ring α] {a b c : α}

theorem two_dvd_bit1 : 2 ∣ bit1 a ↔ (2 : α) ∣ 1 := dvd_add_right two_dvd_bit0

/-- An element a divides the sum a + b if and only if a divides b.-/
@[simp] lemma dvd_add_self_left {a b : α} : a ∣ a + b ↔ a ∣ b :=
dvd_add_right (dvd_refl a)

/-- An element a divides the sum b + a if and only if a divides b.-/
@[simp] lemma dvd_add_self_right {a b : α} : a ∣ b + a ↔ a ∣ b :=
dvd_add_left (dvd_refl a)

/-- An element `a` divides the difference `a - b` if and only if `a` divides `b`. -/
@[simp] lemma dvd_sub_self_left : a ∣ a - b ↔ a ∣ b := dvd_sub_right dvd_rfl

/-- An element `a` divides the difference `b - a` if and only if `a` divides `b`. -/
@[simp] lemma dvd_sub_self_right : a ∣ b - a ↔ a ∣ b := dvd_sub_left dvd_rfl

end ring

section non_unital_comm_ring
variables [non_unital_comm_ring α] {a b c : α}

lemma dvd_mul_sub_mul {k a b x y : α} (hab : k ∣ a - b) (hxy : k ∣ x - y) :
  k ∣ a * x - b * y :=
begin
  convert dvd_add (hxy.mul_left a) (hab.mul_right y),
  rw [mul_sub_left_distrib, mul_sub_right_distrib],
  simp only [sub_eq_add_neg, add_assoc, neg_add_cancel_left],
end

end non_unital_comm_ring
