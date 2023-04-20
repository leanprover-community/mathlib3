/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.finite_limits
import category_theory.limits.functor_category

/-!
# If `D` has finite (co)limits, so do the functor categories `C ⥤ D`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

These are boiler-plate instances, in their own file as neither import otherwise needs the other.
-/

open category_theory

namespace category_theory.limits

universes v₁ v₂ u₁ u₂ w
variables {C : Type u₁} [category.{v₁} C]
variables {D : Type u₂} [category.{v₂} D]

instance functor_category_has_finite_limits [has_finite_limits D] : has_finite_limits (C ⥤ D) :=
{ out := λ J _ _, by exactI infer_instance, }

instance functor_category_has_finite_colimits [has_finite_colimits D] :
  has_finite_colimits (C ⥤ D) :=
{ out := λ J _ _, by exactI infer_instance, }

end category_theory.limits
