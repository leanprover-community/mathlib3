import algebra.category.Group.basic

namespace Group

@[simps]
def to_AddGroup : Group ⥤ AddGroup :=
{ obj := λ X, ⟨additive X⟩,
  map := λ X Y f,
  { to_fun := λ x, f x,
    map_zero' := by { erw [map_one], refl },
    map_add' := λ x y, by { erw [map_mul], refl } },
  map_id' := λ X, by { ext, refl },
  map_comp' := λ X Y Z f g, by { ext, refl } }

end Group

namespace CommGroup

@[simps]
def to_AddCommGroup : CommGroup ⥤ AddCommGroup :=
{ obj := λ X, ⟨additive X⟩,
  map := λ X Y f,
  { to_fun := λ x, f x,
    map_zero' := by { erw [map_one], refl },
    map_add' := λ x y, by { erw [map_mul], refl } },
  map_id' := λ X, by { ext, refl },
  map_comp' := λ X Y Z f g, by { ext, refl } }

end CommGroup

namespace AddGroup

@[simps]
def to_Group : AddGroup ⥤ Group :=
{ obj := λ X, ⟨multiplicative X⟩,
  map := λ X Y f,
  { to_fun := λ x, f x,
    map_one' := by { erw [map_zero], refl },
    map_mul' := λ x y, by { erw [map_add], refl } },
  map_id' := λ X, by { ext, refl },
  map_comp' := λ X Y Z f g, by { ext, refl } }

end AddGroup

namespace AddCommGroup

@[simps]
def to_CommGroup : AddCommGroup ⥤ CommGroup :=
{ obj := λ X, ⟨multiplicative X⟩,
  map := λ X Y f,
  { to_fun := λ x, f x,
    map_one' := by { erw [map_zero], refl },
    map_mul' := λ x y, by { erw [map_add], refl } },
  map_id' := λ X, by { ext, refl },
  map_comp' := λ X Y Z f g, by { ext, refl } }

end AddCommGroup

@[simps]
def Group_AddGroup_equivalence : Group ≌ AddGroup :=
{ functor := Group.to_AddGroup,
  inverse := AddGroup.to_Group,
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
