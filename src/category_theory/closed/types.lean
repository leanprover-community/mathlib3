/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.presheaf
import category_theory.limits.preserves.functor_category
import category_theory.limits.shapes.types
import category_theory.closed.cartesian

/-!
# Cartesian closure of Type

Show that `Type u₁` is cartesian closed, and `C ⥤ Type u₁` is cartesian closed for `C` a small
category in `Type u₁`.
Note this implies that the category of presheaves on a small category `C` is cartesian closed.
-/

namespace category_theory

noncomputable theory

open category limits
universes v₁ v₂ u₁ u₂

variables {C : Type v₂} [category.{v₁} C]
variables {D : Type u₂} [category.{v₂} D]

section cartesian_closed

instance (X : Type v₁) : is_left_adjoint (types.binary_product_functor.obj X) :=
{ right :=
  { obj := λ Y, X ⟶ Y,
    map := λ Y₁ Y₂ f g, g ≫ f },
  adj := adjunction.mk_of_unit_counit
  { unit := { app := λ Z (z : Z) x, ⟨x, z⟩ },
    counit := { app := λ Z xf, xf.2 xf.1 } } }

-- Why isn't this automatically inferred? I can't seem to make
-- `has_finite_products_of_has_products` an instance, not sure why.
instance : has_finite_products (Type v₁) := has_finite_products_of_has_products _

instance : cartesian_closed (Type v₁) :=
{ closed := λ X, { is_adj := adjunction.left_adjoint_of_nat_iso (types.same_prod.app X) } }

-- As above
instance {C : Type v₁} [category C] : has_finite_products (C ⥤ Type v₁) :=
has_finite_products_of_has_products _

instance {C : Type v₁} [small_category C] : cartesian_closed (C ⥤ Type v₁) :=
{ closed := λ F,
  { is_adj :=
    begin
      apply is_left_adjoint_of_preserves_colimits (prod.functor.obj _),
      apply_instance,
      apply functor_category.prod_preserves_colimits,
    end } }

end cartesian_closed

end category_theory
