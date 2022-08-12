/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.module.basic
import algebra.algebra.basic

/-!
# Additional facts about modules over algebras.
-/

namespace linear_map

section restrict_scalars

variables (k : Type*) [comm_semiring k] (A : Type*) [semiring A] [algebra k A]
variables (M : Type*) [add_comm_monoid M] [module k M] [module A M] [smul_assoc_class k A M]
variables (N : Type*) [add_comm_monoid N] [module k N] [module A N] [smul_assoc_class k A N]

/--
Restriction of scalars for linear maps between modules over a `k`-algebra is itself `k`-linear.
-/
@[simps]
def restrict_scalars_linear_map : (M →ₗ[A] N) →ₗ[k] (M →ₗ[k] N) :=
{ to_fun := linear_map.restrict_scalars k,
  map_add' := by tidy,
  map_smul' := by tidy, }

end restrict_scalars

end linear_map
