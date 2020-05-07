/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import algebra.midpoint
import topology.metric_space.isometry

/-!
# Reflection in a point as an `isometric` homeomorphism

Given a `normed_group E` and `x : E`, we define `isometric.reflection x` to be
the reflection in `x` interpreted as an `isometric` homeomorphism.

Reflection is defined as an `equiv.perm` in `data.equiv.mul_add`. In this file
we restate results about `equiv.reflection` for an `isometric.reflection`, and
add a few results about `dist`.

## Tags

reflection, isometric
-/

variables (R : Type*) {E : Type*}

lemma equiv.reflection_fixed_iff_of_module [ring R] [invertible (2:R)]
  [add_comm_group E] [module R E] {x y : E} :
  (equiv.reflection x : E → E) y = y ↔ y = x :=
equiv.reflection_fixed_iff_of_bit0_inj $ λ x y h,
by rw [← one_smul R x, ← one_smul R y, ← inv_of_mul_self (2:R), mul_smul, mul_smul, two_smul,
  two_smul, ← bit0, ← bit0, h]

namespace isometric

section normed_group

variables [normed_group E]

/-- Reflection in `x` as an `isometric` homeomorphism. -/
def reflection (x : E) : E ≃ᵢ E :=
(isometric.neg E).trans (isometric.add_left (x + x))

lemma reflection_apply (x y : E) : (reflection x : E → E) y = x + x - y := rfl

@[simp] lemma reflection_to_equiv (x : E) : (reflection x).to_equiv = equiv.reflection x := rfl

@[simp] lemma reflection_self (x : E) : (reflection x : E → E) x = x := add_sub_cancel _ _

lemma reflection_involutive (x : E) : function.involutive (reflection x : E → E) :=
equiv.reflection_involutive x

@[simp] lemma reflection_symm (x : E) : (reflection x).symm = reflection x :=
to_equiv_inj $ equiv.reflection_symm x

@[simp] lemma reflection_dist_fixed (x y : E) :
  dist ((reflection x : E → E) y) x = dist y x :=
by rw [← (reflection x).dist_eq y x, reflection_self]

lemma reflection_dist_self' (x y : E) :
  dist ((reflection x : E → E) y) y = dist (x + x) (y + y) :=
by { simp only [reflection_apply, dist_eq_norm], congr' 1, abel }

end normed_group

section module

variables [ring R] [invertible (2:R)] [normed_group E] [module R E]

@[simp] lemma reflection_midpoint_left (x y : E) : (reflection (midpoint R x y) : E → E) x = y :=
equiv.reflection_midpoint_left R x y

@[simp] lemma reflection_midpoint_right (x y : E) : (reflection (midpoint R x y) : E → E) y = x :=
equiv.reflection_midpoint_right R x y

variable (R)

include R

lemma reflection_fixed_iff {x y : E} : (reflection x : E → E) y = y ↔ y = x :=
equiv.reflection_fixed_iff_of_module R

end module

section normed_space

variables (R) [normed_field R] [normed_group E] [normed_space R E]

lemma reflection_dist_self (x y : E) :
  dist ((reflection x : E → E) y) y = ∥(2:R)∥ * dist x y :=
by simp only [reflection_dist_self', ← two_smul R x, ← two_smul R y, dist_smul]

end normed_space

lemma reflection_dist_self_real [normed_group E] [normed_space ℝ E] (x y : E) :
  dist ((reflection x : E → E) y) y = 2 * dist x y :=
by simp [reflection_dist_self ℝ x y, real.norm_two]

end isometric
