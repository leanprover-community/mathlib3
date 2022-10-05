/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
import category_theory.limits.connected
import category_theory.limits.constructions.over.products
import category_theory.limits.constructions.over.connected
import category_theory.limits.constructions.limits_of_products_and_equalizers
import category_theory.limits.constructions.equalizers

/-!
# Limits in the over category

Declare instances for limits in the over category: If `C` has finite wide pullbacks, `over B` has
finite limits, and if `C` has arbitrary wide pullbacks then `over B` has limits.
-/
universes w v u -- morphism levels before object levels. See note [category_theory universes].

open category_theory category_theory.limits

variables {C : Type u} [category.{v} C]
variable {X : C}

namespace category_theory.over

/-- Make sure we can derive pullbacks in `over B`. -/
instance {B : C} [has_pullbacks C] : has_pullbacks (over B) :=
begin
  letI : has_limits_of_shape (ulift_hom.{v} (ulift.{v} walking_cospan)) C :=
    has_limits_of_shape_of_equivalence (ulift_hom_ulift_category.equiv.{v} _),
  letI : category (ulift_hom.{v} (ulift.{v} walking_cospan)) := infer_instance,
  exact has_limits_of_shape_of_equivalence (ulift_hom_ulift_category.equiv.{v v} _).symm,
end

/-- Make sure we can derive equalizers in `over B`. -/
instance {B : C} [has_equalizers C] : has_equalizers (over B) :=
begin
  letI : has_limits_of_shape (ulift_hom.{v} (ulift.{v} walking_parallel_pair)) C :=
    has_limits_of_shape_of_equivalence (ulift_hom_ulift_category.equiv.{v} _),
  letI : category (ulift_hom.{v} (ulift.{v} walking_parallel_pair)) := infer_instance,
  exact has_limits_of_shape_of_equivalence (ulift_hom_ulift_category.equiv.{v v} _).symm,
end

instance has_finite_limits {B : C} [has_finite_wide_pullbacks C] : has_finite_limits (over B) :=
begin
  apply @has_finite_limits_of_has_equalizers_and_finite_products _ _ _ _,
  { exact construct_products.over_finite_products_of_finite_wide_pullbacks, },
  { apply @has_equalizers_of_has_pullbacks_and_binary_products _ _ _ _,
    { haveI : has_pullbacks C := ⟨by apply_instance⟩,
      exact construct_products.over_binary_product_of_pullback },
    { apply_instance, } }
end

instance has_limits {B : C} [has_wide_pullbacks.{w} C] : has_limits_of_size.{w} (over B) :=
begin
  apply @has_limits_of_has_equalizers_and_products _ _ _ _,
  { exact construct_products.over_products_of_wide_pullbacks },
  { apply @has_equalizers_of_has_pullbacks_and_binary_products _ _ _ _,
    { haveI : has_pullbacks C := ⟨infer_instance⟩,
      exact construct_products.over_binary_product_of_pullback },
    { apply_instance, } }
end

end category_theory.over
