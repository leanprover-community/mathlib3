/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.limits
import category_theory.limits.preserves
import category_theory.limits.shapes.binary_products

/-!
Show that a functor `F : C ⥤ D` preserves binary products if and only if
`⟨Fπ₁, Fπ₂⟩ : F (A ⨯ B) ⟶ F A ⨯ F B` (that is, `prod_comparison`) is an isomorphism for all `A, B`.
-/

open category_theory

namespace category_theory.limits

universes v u₁ u₂ u₃ -- declare the `v`'s first; see `category_theory.category` for an explanation

variables {C : Type u₁} [category.{v} C]
variables {D : Type u₂} [category.{v} D]

variables [has_binary_products D] (F : C ⥤ D)

/-- (Implementation). Construct a cone for `pair A B ⋙ F` which we will show is limiting. -/
@[simps]
def alternative_cone (A B : C) : cone (pair A B ⋙ F) :=
{ X := F.obj A ⨯ F.obj B,
  π := discrete.nat_trans (λ j, walking_pair.cases_on j limits.prod.fst limits.prod.snd)}

/-- (Implementation). Show that we have a limit for the shape `pair A B ⋙ F`. -/
def alternative_cone_is_limit (A B : C) : is_limit (alternative_cone F A B) :=
{ lift := λ s, prod.lift (s.π.app walking_pair.left) (s.π.app walking_pair.right),
  fac' := λ s j, walking_pair.cases_on j (prod.lift_fst _ _) (prod.lift_snd _ _),
  uniq' := λ s m w, prod.hom_ext
    (by { rw prod.lift_fst, apply w walking_pair.left })
    (by { rw prod.lift_snd, apply w walking_pair.right }) }

variable [has_binary_products C]

/-- If `prod_comparison F A B` is an iso, then `F` preserves the limit `A ⨯ B`. -/
def preserves_binary_prod_of_prod_comparison_iso (A B : C) [is_iso (prod_comparison F A B)] :
  preserves_limit (pair A B) F :=
preserves_limit_of_preserves_limit_cone (limit.is_limit (pair A B))
begin
  apply is_limit.of_iso_limit (alternative_cone_is_limit F A B) _,
  apply cones.ext _ _,
  { apply (as_iso (prod_comparison F A B)).symm },
  { rintro ⟨j⟩,
    { apply (as_iso (prod_comparison F A B)).eq_inv_comp.2 (prod.lift_fst _ _) },
    { apply (as_iso (prod_comparison F A B)).eq_inv_comp.2 (prod.lift_snd _ _) } },
end

/-- If `prod_comparison F A B` is an iso for all `A, B` , then `F` preserves binary products. -/
instance preserves_binary_prods_of_prod_comparison_iso [∀ A B, is_iso (prod_comparison F A B)] :
  preserves_limits_of_shape (discrete walking_pair) F :=
{ preserves_limit := λ K,
  begin
    haveI := preserves_binary_prod_of_prod_comparison_iso F (K.obj walking_pair.left) (K.obj walking_pair.right),
    apply preserves_limit_of_iso F (diagram_iso_pair K).symm,
  end }

variables [preserves_limits_of_shape (discrete walking_pair) F]

/--
The product comparison isomorphism. Technically a special case of `preserves_limit_iso`, but
this version is convenient to have.
-/
instance prod_comparison_iso_of_preserves_binary_prods (A B : C) : is_iso (prod_comparison F A B) :=
let t : is_limit (F.map_cone _) := preserves_limit.preserves (limit.is_limit (pair A B)) in
{ inv := t.lift (alternative_cone F A B),
  hom_inv_id' :=
  begin
    apply is_limit.hom_ext t,
    rintro ⟨j⟩,
    { rw [category.assoc, t.fac, category.id_comp], apply prod.lift_fst },
    { rw [category.assoc, t.fac, category.id_comp], apply prod.lift_snd },
  end,
  inv_hom_id' := by ext ⟨j⟩; { simpa [prod_comparison] using t.fac _ _ } }

end category_theory.limits
