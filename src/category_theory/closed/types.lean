/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.presheaf
import category_theory.limits.preserves.functor_category
import category_theory.limits.shapes.types
import category_theory.closed.cartesian

namespace category_theory

noncomputable theory

open category limits
universes v₁ v₂ u₁ u₂

variables {C : Type v₂} [category.{v₁} C]
variables {D : Type u₂} [category.{v₂} D]

section cartesian_closed

@[simps]
def explicit_prod : Type v₁ ⥤ Type v₁ ⥤ Type v₁ :=
{ obj := λ X,
  { obj := λ Y, (types.binary_product_limit_cone X Y).cone.X,
    map := λ Y₁ Y₂ f,
    begin
      apply (types.binary_product_limit_cone X Y₂).is_limit.lift (binary_fan.mk _ _),
      apply (types.binary_product_limit_cone X Y₁).cone.π.app walking_pair.left,
      apply (types.binary_product_limit_cone X Y₁).cone.π.app walking_pair.right ≫ f,
    end },
  map := λ X₁ X₂ f,
  { app := λ Y,
    begin
      apply (types.binary_product_limit_cone X₂ Y).is_limit.lift (binary_fan.mk _ _),
      apply (types.binary_product_limit_cone X₁ Y).cone.π.app walking_pair.left ≫ f,
      apply (types.binary_product_limit_cone X₁ Y).cone.π.app walking_pair.right,
    end } }

instance (X : Type v₁) : is_left_adjoint (explicit_prod.obj X) :=
{ right :=
  { obj := λ Y, X ⟶ Y,
    map := λ Y₁ Y₂ f g, g ≫ f },
  adj := adjunction.mk_of_unit_counit
  { unit := { app := λ Z (z : Z) x, ⟨x, z⟩ },
    counit := { app := λ Z xf, xf.2 xf.1 } } }

-- tidy can do all of the proofs in this, but it times out, so we do them all manually
def same_prod : explicit_prod ≅ prod.functor :=
begin
  apply nat_iso.of_components _ _,
  { intro X,
    apply nat_iso.of_components _ _,
    { intro Y,
      exact ((limit.is_limit _).cone_point_unique_up_to_iso
             (types.binary_product_limit_cone X Y).is_limit).symm },
    { intros Y₁ Y₂ f,
      dsimp,
      simp only [is_limit.lift_comp_cone_point_unique_up_to_iso_inv, limit.is_limit_lift],
      ext1,
      { simp only [assoc, limit.lift_π, limits.prod.map_fst, comp_id,
                   limit.cone_point_unique_up_to_iso_inv_comp],
        refl },
      { simp only [assoc, limit.lift_π, limits.prod.map_snd,
                   limit.cone_point_unique_up_to_iso_inv_comp_assoc],
        refl } } },
  { intros X₁ X₂ g,
    ext Y : 3;
    dsimp,
    { simp only [assoc, limits.prod.map_fst, limit.cone_point_unique_up_to_iso_inv_comp_assoc,
                 is_limit.lift_comp_cone_point_unique_up_to_iso_inv, limit.is_limit_lift,
                 limit.lift_π],
      refl },
    { simp only [assoc, limits.prod.map_snd, limit.cone_point_unique_up_to_iso_inv_comp,
                 is_limit.lift_comp_cone_point_unique_up_to_iso_inv, limit.is_limit_lift,
                 limit.lift_π, comp_id],
      refl } },
end

-- Why isn't this automatically inferred? I can't seem to make
-- `has_finite_products_of_has_products` an instance, not sure why.
instance : has_finite_products (Type v₁) := has_finite_products_of_has_products _

instance : cartesian_closed (Type v₁) :=
{ closed := λ X, { is_adj := adjunction.left_adjoint_of_nat_iso (same_prod.app X) } }

-- As above
instance {C : Type v₁} [small_category C] : has_finite_products (C ⥤ Type v₁) :=
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
