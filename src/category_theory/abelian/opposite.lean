/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.abelian.basic
import category_theory.preadditive.opposite
import category_theory.limits.opposites
import category_theory.limits.constructions.limits_of_products_and_equalizers

/-!
# The opposite of an abelian category is abelian.
-/

namespace category_theory

open category_theory.limits

variables (C : Type*) [category C] [abelian C]

local attribute [instance]
  finite_limits_from_equalizers_and_finite_products
  finite_colimits_from_coequalizers_and_finite_coproducts
  has_finite_limits_opposite has_finite_colimits_opposite has_finite_products_opposite

instance : abelian Cᵒᵖ :=
{ normal_mono := λ X Y f m, by exactI
    normal_mono_of_normal_epi_unop _ (abelian.normal_epi f.unop),
  normal_epi := λ X Y f m, by exactI
    normal_epi_of_normal_mono_unop _ (abelian.normal_mono f.unop), }

end category_theory
