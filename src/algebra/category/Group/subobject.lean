/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import algebra.category.Group.Z_Module_equivalence
import algebra.category.Module.subobject

/-!
# The category of abelian groups is well-powered

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

open category_theory

universe u

namespace AddCommGroup

instance well_powered_AddCommGroup : well_powered (AddCommGroup.{u}) :=
well_powered_of_equiv (forget₂ (Module.{u} ℤ) AddCommGroup.{u}).as_equivalence

end AddCommGroup
