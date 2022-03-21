/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.group_power.basic
import algebra.regular.basic
import algebra.iterate_hom

/-!
# Regular elements

## Implementation details

Group powers and other definitions import a lot of the algebra hierarchy.
Lemmas about them are kept separate to be able to provide `is_regular` early in the
algebra hierarchy.

-/

variables {R : Type*} {a b : R}

section monoid

variable [monoid R]

/--  Any power of a left-regular element is left-regular. -/
lemma is_left_regular.pow (n : ℕ) (rla : is_left_regular a) : is_left_regular (a ^ n) :=
by simp only [is_left_regular, ← mul_left_iterate, rla.iterate n]

/--  Any power of a right-regular element is right-regular. -/
lemma is_right_regular.pow (n : ℕ) (rra : is_right_regular a) : is_right_regular (a ^ n) :=
by { rw [is_right_regular, ← mul_right_iterate], exact rra.iterate n }

/--  Any power of a regular element is regular. -/
lemma is_regular.pow (n : ℕ) (ra : is_regular a) : is_regular (a ^ n) :=
⟨is_left_regular.pow n ra.left, is_right_regular.pow n ra.right⟩

/--  An element `a` is left-regular if and only if a positive power of `a` is left-regular. -/
lemma is_left_regular.pow_iff {n : ℕ} (n0 : 0 < n) :
  is_left_regular (a ^ n) ↔ is_left_regular a :=
begin
  refine ⟨_, is_left_regular.pow n⟩,
  rw [← nat.succ_pred_eq_of_pos n0, pow_succ'],
  exact is_left_regular.of_mul,
end

/--  An element `a` is right-regular if and only if a positive power of `a` is right-regular. -/
lemma is_right_regular.pow_iff {n : ℕ} (n0 : 0 < n) :
  is_right_regular (a ^ n) ↔ is_right_regular a :=
begin
  refine ⟨_, is_right_regular.pow n⟩,
  rw [← nat.succ_pred_eq_of_pos n0, pow_succ],
  exact is_right_regular.of_mul,
end

/--  An element `a` is regular if and only if a positive power of `a` is regular. -/
lemma is_regular.pow_iff {n : ℕ} (n0 : 0 < n) :
  is_regular (a ^ n) ↔ is_regular a :=
⟨λ h, ⟨(is_left_regular.pow_iff n0).mp h.left, (is_right_regular.pow_iff n0).mp h.right⟩,
  λ h, ⟨is_left_regular.pow n h.left, is_right_regular.pow n h.right⟩⟩

end monoid
