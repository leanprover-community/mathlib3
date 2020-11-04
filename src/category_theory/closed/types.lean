/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.presheaf
import category_theory.limits.functor_category
import category_theory.limits.shapes.types
import category_theory.closed.cartesian

namespace category_theory

noncomputable theory

open category limits
universes v₁ v₂ u₁ u₂

variables {C : Type v₂} [category.{v₁} C]
variables {D : Type u₂} [category.{v₂} D]

section cartesian_closed

def prod_preserves_colimits [has_finite_products D] [has_colimits D]
  [∀ (X : D), preserves_colimits (prod.functor.obj X)]
  (F : C ⥤ D) :
  preserves_colimits (prod.functor.obj F) :=
{ preserves_colimits_of_shape := λ J 𝒥, by exactI
  { preserves_colimit := λ K,
    { preserves := λ c t,
      begin
        apply evaluation_jointly_reflects_colimits,
        intro k,
        change is_colimit ((prod.functor.obj F ⋙ (evaluation _ _).obj k).map_cocone c),
        let := is_colimit_of_preserves ((evaluation C D).obj k ⋙ prod.functor.obj (F.obj k)) t,
        apply is_colimit.map_cocone_equiv _ this,
        apply (nat_iso.of_components _ _).symm,
        { intro G,
          apply as_iso (prod_comparison ((evaluation C D).obj k) F G) },
        { intros G G',
          apply prod_comparison_natural ((evaluation C D).obj k) (𝟙 F) },
      end } } }

@[simps]
def explicit_prod (X : Type v₁) : Type v₁ ⥤ Type v₁ :=
{ obj := λ Y, (types.binary_product_limit_cone X Y).cone.X,
  map := λ Y₁ Y₂ f,
  begin
    apply (types.binary_product_limit_cone X Y₂).is_limit.lift (binary_fan.mk _ _),
    apply _root_.prod.fst,
    exact ↾_root_.prod.snd ≫ f,
  end }

instance (X : Type v₁) : is_left_adjoint (explicit_prod X) :=
{ right :=
  { obj := λ Y, X ⟶ Y,
    map := λ Y₁ Y₂ f g, g ≫ f },
  adj := adjunction.mk_of_unit_counit
  { unit := { app := λ Z (z : Z) x, ⟨x, z⟩ },
    counit :=
    { app := λ Z xf, xf.2 xf.1 } } }

def same_prod (X : Type v₁) : explicit_prod X ≅ prod.functor.obj X :=
begin
  apply nat_iso.of_components _ _,
  { intro Y,
    exact ((limit.is_limit _).cone_point_unique_up_to_iso (types.binary_product_limit_cone X Y).is_limit).symm },
  { tidy }
end

-- Why isn't this automatically inferred? I can't seem to make
-- `has_finite_products_of_has_products` an instance, not sure why.
instance : has_finite_products (Type v₁) := has_finite_products_of_has_products _

instance : cartesian_closed (Type v₁) :=
{ closed := λ X, { is_adj := adjunction.left_adjoint_of_nat_iso (same_prod X) } }

-- As above
instance {C : Type v₁} [small_category C] : has_finite_products (Cᵒᵖ ⥤ Type v₁) :=
has_finite_products_of_has_products _

instance {C : Type v₁} [small_category C] : cartesian_closed (Cᵒᵖ ⥤ Type v₁) :=
{ closed := λ F,
  { is_adj :=
    begin
      apply is_left_adjoint_of_preserves_colimits _,
      apply_instance,
      apply prod_preserves_colimits,
    end } }

end cartesian_closed

end category_theory
