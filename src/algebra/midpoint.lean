/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import algebra.module
import algebra.invertible

/-!
# Midpoint of a segment

## Main definitions

* `midpoint R x y`: midpoint of the segment `[x, y]`. We define it for `x` and `y`
  in a module over a ring `R` with invertible `2`.
* `add_monoid_hom.of_map_midpoint`: construct an `add_monoid_hom` given a map `f` such that
  `f` sends zero to zero and midpoints to midpoints.

## Main theorems

* `midpoint_eq_iff`: `z` is the midpoint of `[x, y]` if and only if `x + y = z + z`,
* `midpoint_unique`: `midpoint R x y` does not depend on `R`;
* `midpoint x y` is linear both in `x` and `y`;
* `reflection_midpoint_left`, `reflection_midpoint_right`: `equiv.reflection (midpoint R x y)`
  swaps `x` and `y`.

We do not mark most lemmas as `@[simp]` because it is hard to tell which side is simpler.

## Tags

midpoint, add_monoid_hom
-/

variables (R : Type*) {E : Type*}

section monoid

variables [semiring R] [invertible (2:R)] [add_comm_monoid E] [semimodule R E]

/-- `midpoint x y` is the midpoint of the segment `[x, y]`. -/
def midpoint (x y : E) : E := (⅟2:R) • (x + y)

lemma midpoint_eq_iff {x y z : E} : midpoint R x y = z ↔ x + y = z + z :=
⟨λ h, h ▸ calc x + y = (2 * ⅟2:R) • (x + y) : by rw [mul_inv_of_self, one_smul]
 ... = midpoint R x y + midpoint R x y : by rw [two_mul, add_smul, midpoint],
 λ h, by rw [midpoint, h, ← two_smul R z, smul_smul, inv_of_mul_self, one_smul]⟩

@[simp] lemma midpoint_add_self (x y : E) : midpoint R x y + midpoint R x y = x + y :=
((midpoint_eq_iff R).1 rfl).symm

/-- `midpoint` does not depend on the ring `R`. -/
lemma midpoint_unique (R' : Type*) [semiring R'] [invertible (2:R')] [semimodule R' E] (x y : E) :
  midpoint R x y = midpoint R' x y :=
(midpoint_eq_iff R).2 $ (midpoint_eq_iff R').1 rfl

@[simp] lemma midpoint_self (x : E) : midpoint R x x = x :=
by rw [midpoint, smul_add, ← two_smul R, smul_smul, mul_inv_of_self, one_smul]

variable {R}

lemma midpoint_def (x y : E) : midpoint R x y = (⅟2:R) • (x + y) := rfl

lemma midpoint_comm (x y : E) : midpoint R x y = midpoint R y x :=
by simp only [midpoint_def, add_comm]

lemma midpoint_zero_add (x y : E) : midpoint R 0 (x + y) = midpoint R x y :=
(midpoint_eq_iff R).2 $ (zero_add (x + y)).symm ▸ (midpoint_eq_iff R).1 rfl

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

section group

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

end group

namespace add_monoid_hom

variables (R) (R' : Type*) {F : Type*}
  [semiring R] [invertible (2:R)] [add_comm_monoid E] [semimodule R E]
  [semiring R'] [invertible (2:R')] [add_comm_monoid F] [semimodule R' F]

/-- A map `f : E → F` sending zero to zero and midpoints to midpoints is an `add_monoid_hom`. -/
def of_map_midpoint (f : E → F) (h0 : f 0 = 0)
  (hm : ∀ x y, f (midpoint R x y) = midpoint R' (f x) (f y)) :
  E →+ F :=
{ to_fun := f,
  map_zero' := h0,
  map_add' := λ x y, -- by rw [← midpoint_self R (x + y), ← midpoint_zero_add, hm, h0]
    calc f (x + y) = f 0 + f (x + y) : by rw [h0, zero_add]
    ... = midpoint R' (f 0) (f (x + y)) + midpoint R' (f 0) (f (x + y)) :
      (midpoint_add_self _ _ _).symm
    ... = f (midpoint R x y) + f (midpoint R x y) : by rw [← hm, midpoint_zero_add]
    ... = f x + f y : by rw [hm, midpoint_add_self] }

@[simp] lemma coe_of_map_midpoint (f : E → F) (h0 : f 0 = 0)
  (hm : ∀ x y, f (midpoint R x y) = midpoint R' (f x) (f y)) :
  ⇑(of_map_midpoint R R' f h0 hm) = f := rfl

end add_monoid_hom

namespace equiv

variables [ring R] [invertible (2:R)] [add_comm_group E] [module R E]

@[simp] lemma reflection_midpoint_left (x y : E) : (reflection (midpoint R x y) : E → E) x = y :=
by rw [reflection_apply, midpoint_add_self, add_sub_cancel']

@[simp] lemma reflection_midpoint_right (x y : E) : (reflection (midpoint R x y) : E → E) y = x :=
by rw [reflection_apply, midpoint_add_self, add_sub_cancel]

end equiv
