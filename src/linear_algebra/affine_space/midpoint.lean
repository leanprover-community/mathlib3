/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import algebra.invertible
import linear_algebra.affine_space.affine_equiv

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
* `point_reflection_midpoint_left`, `point_reflection_midpoint_right`:
  `equiv.point_reflection (midpoint R x y)` swaps `x` and `y`.

We do not mark most lemmas as `@[simp]` because it is hard to tell which side is simpler.

## Tags

midpoint, add_monoid_hom
-/

open affine_map affine_equiv

section

variables (R : Type*) {V V' P P' : Type*} [ring R] [invertible (2:R)]
  [add_comm_group V] [module R V] [add_torsor V P]
  [add_comm_group V'] [module R V'] [add_torsor V' P']

include V

/-- `midpoint x y` is the midpoint of the segment `[x, y]`. -/
def midpoint (x y : P) : P := line_map x y (⅟2:R)

variables {R} {x y z : P}
include V'

@[simp] lemma affine_map.map_midpoint (f : P →ᵃ[R] P') (a b : P) :
  f (midpoint R a b) = midpoint R (f a) (f b) :=
f.apply_line_map a b _

@[simp] lemma affine_equiv.map_midpoint (f : P ≃ᵃ[R] P') (a b : P) :
  f (midpoint R a b) = midpoint R (f a) (f b) :=
f.apply_line_map a b _

omit V'

@[simp] lemma affine_equiv.point_reflection_midpoint_left (x y : P) :
  point_reflection R (midpoint R x y) x = y :=
by rw [midpoint, point_reflection_apply, line_map_apply, vadd_vsub,
  vadd_vadd, ← add_smul, ← two_mul, mul_inv_of_self, one_smul, vsub_vadd]

lemma midpoint_comm (x y : P) : midpoint R x y = midpoint R y x :=
by rw [midpoint, ← line_map_apply_one_sub, one_sub_inv_of_two, midpoint]

@[simp] lemma affine_equiv.point_reflection_midpoint_right (x y : P) :
  point_reflection R (midpoint R x y) y = x :=
by rw [midpoint_comm, affine_equiv.point_reflection_midpoint_left]

lemma midpoint_vsub_midpoint (p₁ p₂ p₃ p₄ : P) :
  midpoint R p₁ p₂ -ᵥ midpoint R p₃ p₄ = midpoint R (p₁ -ᵥ p₃) (p₂ -ᵥ p₄) :=
line_map_vsub_line_map _ _ _ _ _

lemma midpoint_vadd_midpoint (v v' : V) (p p' : P) :
  midpoint R v v' +ᵥ midpoint R p p' = midpoint R (v +ᵥ p) (v' +ᵥ p') :=
line_map_vadd_line_map _ _ _ _ _

lemma midpoint_eq_iff {x y z : P} : midpoint R x y = z ↔ point_reflection R z x = y :=
eq_comm.trans ((injective_point_reflection_left_of_module R x).eq_iff'
  (affine_equiv.point_reflection_midpoint_left x y)).symm

@[simp] lemma midpoint_vsub_left (p₁ p₂ : P) : midpoint R p₁ p₂ -ᵥ p₁ = (⅟2:R) • (p₂ -ᵥ p₁) :=
line_map_vsub_left _ _ _

@[simp] lemma midpoint_vsub_right (p₁ p₂ : P) : midpoint R p₁ p₂ -ᵥ p₂ = (⅟2:R) • (p₁ -ᵥ p₂) :=
by rw [midpoint_comm, midpoint_vsub_left]

@[simp] lemma left_vsub_midpoint (p₁ p₂ : P) : p₁ -ᵥ midpoint R p₁ p₂ = (⅟2:R) • (p₁ -ᵥ p₂) :=
left_vsub_line_map _ _ _

@[simp] lemma right_vsub_midpoint (p₁ p₂ : P) : p₂ -ᵥ midpoint R p₁ p₂ = (⅟2:R) • (p₂ -ᵥ p₁) :=
by rw [midpoint_comm, left_vsub_midpoint]

lemma midpoint_vsub (p₁ p₂ p : P) :
  midpoint R p₁ p₂ -ᵥ p = (⅟2:R) • (p₁ -ᵥ p) + (⅟2:R) • (p₂ -ᵥ p) :=
by rw [←vsub_sub_vsub_cancel_right p₁ p p₂, smul_sub, sub_eq_add_neg, ←smul_neg,
       neg_vsub_eq_vsub_rev, add_assoc, inv_of_two_smul_add_inv_of_two_smul, ←vadd_vsub_assoc,
       midpoint_comm, midpoint, line_map_apply]

lemma vsub_midpoint (p₁ p₂ p : P) :
  p -ᵥ midpoint R p₁ p₂ = (⅟2:R) • (p -ᵥ p₁) + (⅟2:R) • (p -ᵥ p₂) :=
by rw [←neg_vsub_eq_vsub_rev, midpoint_vsub, neg_add, ←smul_neg, ←smul_neg,
       neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev]

@[simp] lemma midpoint_sub_left (v₁ v₂ : V) : midpoint R v₁ v₂ - v₁ = (⅟2:R) • (v₂ - v₁) :=
midpoint_vsub_left v₁ v₂

@[simp] lemma midpoint_sub_right (v₁ v₂ : V) : midpoint R v₁ v₂ - v₂ = (⅟2:R) • (v₁ - v₂) :=
midpoint_vsub_right v₁ v₂

@[simp] lemma left_sub_midpoint (v₁ v₂ : V) : v₁ - midpoint R v₁ v₂ = (⅟2:R) • (v₁ - v₂) :=
left_vsub_midpoint v₁ v₂

@[simp] lemma right_sub_midpoint (v₁ v₂ : V) : v₂ - midpoint R v₁ v₂ = (⅟2:R) • (v₂ - v₁) :=
right_vsub_midpoint v₁ v₂

variable (R)

@[simp] lemma midpoint_eq_left_iff {x y : P} : midpoint R x y = x ↔ x = y :=
by rw [midpoint_eq_iff, point_reflection_self]

@[simp] lemma left_eq_midpoint_iff {x y : P} : x = midpoint R x y ↔ x = y :=
by rw [eq_comm, midpoint_eq_left_iff]

@[simp] lemma midpoint_eq_right_iff {x y : P} : midpoint R x y = y ↔ x = y :=
by rw [midpoint_comm, midpoint_eq_left_iff, eq_comm]

@[simp] lemma right_eq_midpoint_iff {x y : P} : y = midpoint R x y ↔ x = y :=
by rw [eq_comm, midpoint_eq_right_iff]

lemma midpoint_eq_midpoint_iff_vsub_eq_vsub {x x' y y' : P} :
  midpoint R x y = midpoint R x' y' ↔ x -ᵥ x' = y' -ᵥ y :=
by rw [← @vsub_eq_zero_iff_eq V, midpoint_vsub_midpoint, midpoint_eq_iff, point_reflection_apply,
  vsub_eq_sub, zero_sub, vadd_eq_add, add_zero, neg_eq_iff_eq_neg, neg_vsub_eq_vsub_rev]

lemma midpoint_eq_iff' {x y z : P} : midpoint R x y = z ↔ equiv.point_reflection z x = y :=
midpoint_eq_iff

/-- `midpoint` does not depend on the ring `R`. -/
lemma midpoint_unique (R' : Type*) [ring R'] [invertible (2:R')] [module R' V] (x y : P) :
  midpoint R x y = midpoint R' x y :=
(midpoint_eq_iff' R).2 $ (midpoint_eq_iff' R').1 rfl

@[simp] lemma midpoint_self (x : P) : midpoint R x x = x :=
line_map_same_apply _ _

@[simp] lemma midpoint_add_self (x y : V) : midpoint R x y + midpoint R x y = x + y :=
calc midpoint R x y +ᵥ midpoint R x y = midpoint R x y +ᵥ midpoint R y x : by rw midpoint_comm
... = x + y : by rw [midpoint_vadd_midpoint, vadd_eq_add, vadd_eq_add, add_comm, midpoint_self]

lemma midpoint_zero_add (x y : V) : midpoint R 0 (x + y) = midpoint R x y :=
(midpoint_eq_midpoint_iff_vsub_eq_vsub R).2 $ by simp [sub_add_eq_sub_sub_swap]

lemma midpoint_eq_smul_add (x y : V) : midpoint R x y = (⅟2 : R) • (x + y) :=
by rw [midpoint_eq_iff, point_reflection_apply, vsub_eq_sub, vadd_eq_add, sub_add_eq_add_sub,
  ← two_smul R, smul_smul, mul_inv_of_self, one_smul, add_sub_cancel']

@[simp] lemma midpoint_self_neg (x : V) :
  midpoint R x (-x) = 0 :=
by rw [midpoint_eq_smul_add, add_neg_self, smul_zero]

@[simp] lemma midpoint_neg_self (x : V) :
  midpoint R (-x) x = 0 :=
by simpa using midpoint_self_neg R (-x)

@[simp] lemma midpoint_sub_add (x y : V) :
  midpoint R (x - y) (x + y) = x :=
by rw [sub_eq_add_neg, ← vadd_eq_add, ← vadd_eq_add, ← midpoint_vadd_midpoint]; simp

@[simp] lemma midpoint_add_sub (x y : V) :
  midpoint R (x + y) (x - y) = x :=
by rw midpoint_comm; simp

end

namespace add_monoid_hom

variables (R R' : Type*) {E F : Type*}
  [ring R] [invertible (2:R)] [add_comm_group E] [module R E]
  [ring R'] [invertible (2:R')] [add_comm_group F] [module R' F]

/-- A map `f : E → F` sending zero to zero and midpoints to midpoints is an `add_monoid_hom`. -/
def of_map_midpoint (f : E → F) (h0 : f 0 = 0)
  (hm : ∀ x y, f (midpoint R x y) = midpoint R' (f x) (f y)) :
  E →+ F :=
{ to_fun := f,
  map_zero' := h0,
  map_add' := λ x y,
    calc f (x + y) = f 0 + f (x + y) : by rw [h0, zero_add]
    ... = midpoint R' (f 0) (f (x + y)) + midpoint R' (f 0) (f (x + y)) :
      (midpoint_add_self _ _ _).symm
    ... = f (midpoint R x y) + f (midpoint R x y) : by rw [← hm, midpoint_zero_add]
    ... = f x + f y : by rw [hm, midpoint_add_self] }

@[simp] lemma coe_of_map_midpoint (f : E → F) (h0 : f 0 = 0)
  (hm : ∀ x y, f (midpoint R x y) = midpoint R' (f x) (f y)) :
  ⇑(of_map_midpoint R R' f h0 hm) = f := rfl

end add_monoid_hom
