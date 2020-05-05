/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import algebra.module
import algebra.invertible

/-!
# Midpoint of a segment

Given two points `x` and `y` in a vector space over a ring `R` with invertible `2`,
we define `midpoint R x y` to be `(⅟2:R) • (x + y)`, where `(⅟2:R)` is the inverse of `(2:R)`
provided by `[invertible (2:R)]`.

We prove that `z` is the midpoint of `[x, y]` if and only if `x + y = z + z`, hence `midpoint R x y`
does not depend on `R`. We also prove that `midpoint x y` is linear both in `x` and `y`.

We do not mark lemmas other than `midpoint_self` as `@[simp]` because it is hard to tell which side
is simpler.

## Tags

midpoint
-/

variables (R : Type*) {E : Type*}

section monoid

variables [semiring R] [invertible (2:R)] [add_comm_monoid E] [semimodule R E]

/-- `midpoint x y` is the midpoint of the segment `[x, y]`. -/
def midpoint (x y : E) : E := (⅟2:R) • (x + y)

lemma midpoint_eq_iff {x y z : E} : midpoint R x y = z ↔ x + y = z + z :=
⟨λ h, h ▸ calc x + y = (2 * ⅟2:R) • (x + y) : by rw [mul_inv_of_self, one_smul]
 ... = midpoint R x y + midpoint R x y : by rw [two_mul, add_smul, midpoint],
 λ h, by rw [midpoint, h, ← one_smul R z, ← add_smul, smul_smul, ← bit0, inv_of_mul_self]⟩

variable {R}

lemma midpoint_def (x y : E) : midpoint R x y = (⅟2:R) • (x + y) := rfl

/-- `midpoint` does not depend on the ring `R`. -/
lemma midpoint_unique (R' : Type*) [semiring R'] [invertible (2:R')] [semimodule R' E] (x y : E) :
  midpoint R x y = midpoint R' x y :=
(midpoint_eq_iff R).2 $ (midpoint_eq_iff R').1 rfl

@[simp] lemma midpoint_self (x : E) : midpoint R x x = x :=
by rw [midpoint_def, smul_add, ← add_smul, ← mul_two, inv_of_mul_self, one_smul]

lemma midpoint_comm (x y : E) : midpoint R x y = midpoint R y x :=
by simp only [midpoint_def, add_comm]

lemma midpoint_add_add (x y x' y' : E) :
  midpoint R (x + x') (y + y') = midpoint R x y + midpoint R x' y' :=
by { simp only [midpoint_def, ← smul_add, add_assoc, add_left_comm x'] }

lemma midpoint_add_right (x y z : E) : midpoint R (x + z) (y + z) = midpoint R x y + z :=
by rw [midpoint_add_add, midpoint_self]

lemma midpoint_add_left (x y z : E) : midpoint R (x + y) (x + z) = x + midpoint R y z :=
by rw [midpoint_add_add, midpoint_self]

lemma midpoint_smul_smul (c : R) (x y : E) : midpoint R (c • x) (c • y) = c • midpoint R x y :=
(midpoint_eq_iff R).2 $ by rw [← smul_add, ← smul_add, (midpoint_eq_iff R).1 rfl]

end monoid

variables [ring R] [invertible (2:R)] [add_comm_group E] [module R E]

lemma midpoint_neg_neg (x y : E) : midpoint R (-x) (-y) = -midpoint R x y :=
by simpa only [neg_one_smul] using midpoint_smul_smul (-1:R) x y

lemma midpoint_sub_sub (x y x' y' : E) :
  midpoint R (x - x') (y - y') = midpoint R x y - midpoint R x' y' :=
by simp only [sub_eq_add_neg, midpoint_add_add, midpoint_neg_neg]

lemma midpoint_sub_right (x y z : E) : midpoint R (x - z) (y - z) = midpoint R x y - z :=
by rw [midpoint_sub_sub, midpoint_self]

lemma midpoint_sub_left (x y z : E) : midpoint R (x - y) (x - z) = x - midpoint R y z :=
by rw [midpoint_sub_sub, midpoint_self]
