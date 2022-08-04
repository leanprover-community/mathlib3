/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import algebra.category.Group.basic

/-!
# Equivalence between `Group` and `AddGroup`

This file contains two equivalence:
* `Group_AddGroup_equivalence` : the equivalence between `Group` and `AddGroup` by sending
  `X : Group` to `additive X` and `Y : AddGroup` to `multiplicative Y`.
* `CommGroup_AddCommGroup_equivlance` : the equivalence between `CommGroup` and `AddCommGroup` by
  sending `X : CommGroup` to `additive X` and `Y : AddCommGroup` to `multiplicative Y`.
-/


namespace Group

/--
The functor `Group ⥤ AddGroup` by sending `X ↦ additive X` and `f ↦ f`.
-/
@[simps] def to_AddGroup : Group ⥤ AddGroup :=
{ obj := λ X, AddGroup.of (additive X),
  map := λ X Y, monoid_hom.to_additive }

end Group

namespace CommGroup

/--
The functor `CommGroup ⥤ AddCommGroup` by sending `X ↦ additive X` and `f ↦ f`.
-/
@[simps] def to_AddCommGroup : CommGroup ⥤ AddCommGroup :=
{ obj := λ X, ⟨additive X⟩,
  map := λ X Y f,
  { to_fun := λ x, f x,
    map_zero' := by { erw [map_one], refl },
    map_add' := λ x y, by { erw [map_mul], refl } },
  map_id' := λ X, by { ext, refl },
  map_comp' := λ X Y Z f g, by { ext, refl } }

end CommGroup

namespace AddGroup

/--
The functor `AddGroup ⥤ Group` by sending `X ↦ multiplicative Y` and `f ↦ f`.
-/
@[simps] def to_Group : AddGroup ⥤ Group :=
{ obj := λ X, ⟨multiplicative X⟩,
  map := λ X Y f,
  { to_fun := λ x, f x,
    map_one' := by { erw [map_zero], refl },
    map_mul' := λ x y, by { erw [map_add], refl } },
  map_id' := λ X, by { ext, refl },
  map_comp' := λ X Y Z f g, by { ext, refl } }

end AddGroup

namespace AddCommGroup

/--
The functor `AddCommGroup ⥤ CommGroup` by sending `X ↦ multiplicative Y` and `f ↦ f`.
-/
@[simps] def to_CommGroup : AddCommGroup ⥤ CommGroup :=
{ obj := λ X, ⟨multiplicative X⟩,
  map := λ X Y f,
  { to_fun := λ x, f x,
    map_one' := by { erw [map_zero], refl },
    map_mul' := λ x y, by { erw [map_add], refl } },
  map_id' := λ X, by { ext, refl },
  map_comp' := λ X Y Z f g, by { ext, refl } }

end AddCommGroup

/--
The equivalence of categories between `Group` and `AddGroup`
-/
@[simps] def Group_AddGroup_equivalence : Group ≌ AddGroup :=
equivalence.mk Group.to_AddGroup AddGroup.to_Group
  (nat_iso.of_components
    (λ X, mul_equiv.to_Group_iso (mul_equiv.multiplicative_additive X))
    (λ X Y f, rfl))
  (nat_iso.of_components
    (λ X, add_equiv.to_AddGroup_iso (add_equiv.additive_multiplicative X))
    (λ X Y f, rfl))

/--
The equivalence of categories between `CommGroup` and `AddCommGroup`.
-/
def CommGroup_AddCommGroup_equivalence : CommGroup ≌ AddCommGroup :=
{ functor := CommGroup.to_AddCommGroup,
  inverse := AddCommGroup.to_CommGroup,
  unit_iso :=
  { hom :=
    { app := λ X, (𝟙 X),
      naturality' := λ _ _ _, by { ext, refl } },
    inv :=
    { app := λ X, (𝟙 X),
      naturality' := λ _ _ _, by { ext, refl } },
    hom_inv_id' := rfl,
    inv_hom_id' := rfl },
  counit_iso :=
  { hom :=
    { app := λ X, (𝟙 X),
      naturality' := λ _ _ _, by { ext, refl } },
    inv :=
    { app := λ X, (𝟙 X),
      naturality' := λ _ _ _, by { ext, refl } },
    hom_inv_id' := rfl,
    inv_hom_id' := rfl },
  functor_unit_iso_comp' := λ X, rfl }
