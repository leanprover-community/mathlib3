/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import algebra.hom.equiv.units.basic
import algebra.group_with_zero.units.basic

/-!
# Multiplication by a nonzero element in a `group_with_zero` is a permutation.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {G : Type*}

namespace equiv

section group_with_zero
variables [group_with_zero G]

/-- Left multiplication by a nonzero element in a `group_with_zero` is a permutation of the
underlying type. -/
@[simps {fully_applied := ff}]
protected def mul_left₀ (a : G) (ha : a ≠ 0) : perm G :=
(units.mk0 a ha).mul_left

lemma _root_.mul_left_bijective₀ (a : G) (ha : a ≠ 0) :
  function.bijective ((*) a : G → G) :=
(equiv.mul_left₀ a ha).bijective

/-- Right multiplication by a nonzero element in a `group_with_zero` is a permutation of the
underlying type. -/
@[simps {fully_applied := ff}]
protected def mul_right₀ (a : G) (ha : a ≠ 0) : perm G :=
(units.mk0 a ha).mul_right

lemma _root_.mul_right_bijective₀ (a : G) (ha : a ≠ 0) :
  function.bijective ((* a) : G → G) :=
(equiv.mul_right₀ a ha).bijective

end group_with_zero

end equiv
