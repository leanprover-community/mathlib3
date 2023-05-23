/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import topology.locally_constant.algebra
import topology.continuous_function.basic
import topology.continuous_function.algebra

/-!
# The algebra morphism from locally constant functions to continuous functions.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/

namespace locally_constant

variables {X Y : Type*} [topological_space X] [topological_space Y] (f : locally_constant X Y)

/-- The inclusion of locally-constant functions into continuous functions as a multiplicative
monoid hom. -/
@[to_additive "The inclusion of locally-constant functions into continuous functions as an
additive monoid hom.", simps]
def to_continuous_map_monoid_hom [monoid Y] [has_continuous_mul Y] :
  locally_constant X Y →* C(X, Y) :=
{ to_fun    := coe,
  map_one' := by { ext, simp, },
  map_mul'  := λ x y, by { ext, simp, }, }

/-- The inclusion of locally-constant functions into continuous functions as a linear map. -/
@[simps] def to_continuous_map_linear_map (R : Type*) [semiring R]
  [add_comm_monoid Y] [module R Y] [has_continuous_add Y] [has_continuous_const_smul R Y] :
  locally_constant X Y →ₗ[R] C(X, Y) :=
{ to_fun    := coe,
  map_add'  := λ x y, by { ext, simp, },
  map_smul' := λ x y, by { ext, simp, }, }

/-- The inclusion of locally-constant functions into continuous functions as an algebra map. -/
@[simps] def to_continuous_map_alg_hom (R : Type*) [comm_semiring R]
  [semiring Y] [algebra R Y] [topological_semiring Y] :
  locally_constant X Y →ₐ[R] C(X, Y) :=
{ to_fun    := coe,
  map_one'  := by { ext, simp, },
  map_mul'  := λ x y, by { ext, simp, },
  map_zero' := by { ext, simp, },
  map_add'  := λ x y, by { ext, simp, },
  commutes' := λ r, by { ext x, simp [algebra.smul_def], }, }

end locally_constant
