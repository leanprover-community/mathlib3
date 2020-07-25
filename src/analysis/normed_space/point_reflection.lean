/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import algebra.midpoint
import topology.metric_space.isometry

/-!
# Point reflection in a point as an `isometric` homeomorphism

Given a `normed_group E` and `x : E`, we define `isometric.point_reflection x` to be
the point reflection in `x` interpreted as an `isometric` homeomorphism.

Point reflection is defined as an `equiv.perm` in `data.equiv.mul_add`. In this file
we restate results about `equiv.point_reflection` for an `isometric.point_reflection`, and
add a few results about `dist`.

## Tags

point reflection, isometric
-/

variables (R : Type*) {E : Type*}

lemma equiv.point_reflection_fixed_iff_of_module [ring R] [invertible (2:R)]
  [add_comm_group E] [module R E] {x y : E} :
  (equiv.point_reflection x : E → E) y = y ↔ y = x :=
equiv.point_reflection_fixed_iff_of_bit0_injective $ λ x y h,
by rw [← one_smul R x, ← one_smul R y, ← inv_of_mul_self (2:R), mul_smul, mul_smul, two_smul,
  two_smul, ← bit0, ← bit0, h]

namespace isometric

section normed_group

variables [normed_group E]

/-- Point reflection in `x` as an `isometric` homeomorphism. -/
def point_reflection (x : E) : E ≃ᵢ E :=
(isometric.neg E).trans (isometric.add_left (x + x))

lemma point_reflection_apply (x y : E) : (point_reflection x : E → E) y = x + x - y := rfl

@[simp] lemma point_reflection_to_equiv (x : E) :
  (point_reflection x).to_equiv = equiv.point_reflection x := rfl

@[simp] lemma point_reflection_self (x : E) : (point_reflection x : E → E) x = x :=
add_sub_cancel _ _

lemma point_reflection_involutive (x : E) : function.involutive (point_reflection x : E → E) :=
equiv.point_reflection_involutive x

@[simp] lemma point_reflection_symm (x : E) : (point_reflection x).symm = point_reflection x :=
to_equiv_inj $ equiv.point_reflection_symm x

@[simp] lemma point_reflection_dist_fixed (x y : E) :
  dist ((point_reflection x : E → E) y) x = dist y x :=
by rw [← (point_reflection x).dist_eq y x, point_reflection_self]

lemma point_reflection_dist_self' (x y : E) :
  dist ((point_reflection x : E → E) y) y = dist (x + x) (y + y) :=
by { simp only [point_reflection_apply, dist_eq_norm], congr' 1, abel }

end normed_group

section module

variables [ring R] [invertible (2:R)] [normed_group E] [module R E]

@[simp] lemma point_reflection_midpoint_left (x y : E) :
  (point_reflection (midpoint R x y) : E → E) x = y :=
equiv.point_reflection_midpoint_left R x y

@[simp] lemma point_reflection_midpoint_right (x y : E) :
  (point_reflection (midpoint R x y) : E → E) y = x :=
equiv.point_reflection_midpoint_right R x y

variable (R)

include R

lemma point_reflection_fixed_iff {x y : E} : (point_reflection x : E → E) y = y ↔ y = x :=
equiv.point_reflection_fixed_iff_of_module R

end module

section normed_space

variables (R) [normed_field R] [normed_group E] [normed_space R E]

lemma point_reflection_dist_self (x y : E) :
  dist ((point_reflection x : E → E) y) y = ∥(2:R)∥ * dist x y :=
by simp only [point_reflection_dist_self', ← two_smul R x, ← two_smul R y, dist_smul]

end normed_space

lemma point_reflection_dist_self_real [normed_group E] [normed_space ℝ E] (x y : E) :
  dist ((point_reflection x : E → E) y) y = 2 * dist x y :=
by simp [point_reflection_dist_self ℝ x y, real.norm_two]

end isometric
