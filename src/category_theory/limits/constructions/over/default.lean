/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
import category_theory.limits.constructions.over.products
import category_theory.limits.constructions.over.connected
import category_theory.limits.constructions.limits_of_products_and_equalizers
import category_theory.limits.constructions.equalizers

/-!
# Limits in the over category

Declare instances for limits in the over category: If `C` has finite wide pullbacks, `over B` has
finite limits, and if `C` has arbitrary wide pullbacks then `over B` has limits.
-/
universes v u -- morphism levels before object levels. See note [category_theory universes].

open category_theory category_theory.limits

variables {J : Type v} [small_category J]
variables {C : Type u} [category.{v} C]
variable {X : C}

namespace category_theory.over

/-- Make sure we can derive pullbacks in `over B`. -/
example {B : C} [has_pullbacks C] : has_pullbacks (over B) := by apply_instance

/-- Make sure we can derive equalizers in `over B`. -/
example {B : C} [has_equalizers C] : has_equalizers (over B) := by apply_instance

instance has_finite_limits {B : C} [has_finite_wide_pullbacks C] : has_finite_limits (over B) :=
begin
  apply @finite_limits_from_equalizers_and_finite_products _ _ _ _,
  { exact construct_products.over_finite_products_of_finite_wide_pullbacks, },
  { apply @has_equalizers_of_pullbacks_and_binary_products _ _ _ _,
    { haveI : has_pullbacks C := ⟨by apply_instance⟩,
      exact construct_products.over_binary_product_of_pullback },
    { apply_instance, } }
end

instance has_limits {B : C} [has_wide_pullbacks C] : has_limits (over B) :=
begin
  apply @limits_from_equalizers_and_products _ _ _ _,
  { exact construct_products.over_products_of_wide_pullbacks },
  { apply @has_equalizers_of_pullbacks_and_binary_products _ _ _ _,
    { haveI : has_pullbacks C := ⟨by apply_instance⟩,
      exact construct_products.over_binary_product_of_pullback },
    { apply_instance, } }
end

end category_theory.over
