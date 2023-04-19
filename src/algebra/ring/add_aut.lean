/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import group_theory.group_action.group
import algebra.module.basic

/-!
# Multiplication on the left/right as additive automorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `add_aut.mul_left` and `add_aut.mul_right`.

See also `add_monoid_hom.mul_left`, `add_monoid_hom.mul_right`, `add_monoid.End.mul_left`, and
`add_monoid.End.mul_right` for multiplication by `R` as an endomorphism instead of multiplication by
`Rˣ` as an automorphism.
-/

namespace add_aut
variables {R : Type*} [semiring R]

/-- Left multiplication by a unit of a semiring as an additive automorphism. -/
@[simps { simp_rhs := tt }]
def mul_left : Rˣ →* add_aut R := distrib_mul_action.to_add_aut _ _

/-- Right multiplication by a unit of a semiring as an additive automorphism. -/
def mul_right (u : Rˣ) : add_aut R :=
distrib_mul_action.to_add_aut Rᵐᵒᵖˣ R (units.op_equiv.symm $ mul_opposite.op u)

@[simp] lemma mul_right_apply (u : Rˣ) (x : R) : mul_right u x = x * u := rfl
@[simp] lemma mul_right_symm_apply (u : Rˣ) (x : R) : (mul_right u).symm x = x * ↑u⁻¹ := rfl

end add_aut

