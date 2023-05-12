import category_theory.equivalence
import category_theory.functor.category

universes u₁ u₂ u₃ v₁ v₂ v₃

open category_theory

variables (A : Type u₁) (B : Type u₂) (C : Type u₃)
variables [category.{v₁} A] [category.{v₂} B] [category.{v₃} C]
variables (e : B ≌ C)

namespace category_theory.functor

@[simps] def equivalence_of_target_equivalence.functor' : (A ⥤ B) ⥤ (A ⥤ C) :=
{ obj := λ F, F ⋙ e.functor,
  map := λ F G α,
  { app := λ a, e.functor.map $ α.app a,
    naturality' := λ a b f, by rw [comp_map, comp_map, ←map_comp, α.naturality, map_comp] },
  map_id' := λ F, by { ext, exact map_id _ _ },
  map_comp' := λ F G H α β, by { ext, dsimp, simp, } }

@[simps] def equivalence_of_target_equivalence.inverse' : (A ⥤ C) ⥤ (A ⥤ B) :=
{ obj := λ F, F ⋙ e.inverse,
  map := λ F G α,
  { app := λ a, e.inverse.map $ α.app a,
    naturality' := λ a b f, by rw [comp_map, comp_map, ←map_comp, α.naturality, map_comp] },
  map_id' := λ F, by { ext, exact map_id _ _ },
  map_comp' := λ F G H α β, by { ext, dsimp, simp, } }

@[simps] def equivalence_of_target_equivalence.unit_iso_hom' :
  𝟭 (A ⥤ B) ⟶
    equivalence_of_target_equivalence.functor' A B C e ⋙
      equivalence_of_target_equivalence.inverse' A B C e :=
{ app := λ F, { app := λ a, e.unit.app _, naturality' := λ X Y f, e.unit.naturality' _ },
  naturality' := λ F G α, by { ext, dsimp, simp, } }

@[simps] def equivalence_of_target_equivalence.unit_iso_inv' :
  (equivalence_of_target_equivalence.functor' A B C e ⋙
      equivalence_of_target_equivalence.inverse' A B C e) ⟶
  𝟭 (A ⥤ B) :=
{ app := λ F, { app := λ a, e.unit_inv.app _, naturality' := λ X Y f, e.unit_inv.naturality' _ },
  naturality' := λ F G α, by { ext, dsimp, simp only [equivalence.inv_fun_map, category.assoc,
    iso.hom_inv_id_app, nat_iso.cancel_nat_iso_inv_left], erw category.comp_id, } }

lemma equivalence_of_target_equivalence.unit_iso_hom_inv_id' :
  equivalence_of_target_equivalence.unit_iso_hom' A B C e ≫
    equivalence_of_target_equivalence.unit_iso_inv' A B C e =
  𝟙 (𝟭 (A ⥤ B)) :=
begin
  ext F a,
  dsimp,
  simpa only [iso.hom_inv_id_app],
end

lemma equivalence_of_target_equivalence.unit_iso_inv_hom_id' :
  equivalence_of_target_equivalence.unit_iso_inv' A B C e ≫
    equivalence_of_target_equivalence.unit_iso_hom' A B C e =
  𝟙 _ :=
begin
  ext F a,
  dsimp,
  simpa only [iso.inv_hom_id_app],
end

@[simps] def equivalence_of_target_equivalence.unit_iso' :
  𝟭 (A ⥤ B) ≅ equivalence_of_target_equivalence.functor' A B C e ⋙
    equivalence_of_target_equivalence.inverse' A B C e :=
{ hom := equivalence_of_target_equivalence.unit_iso_hom' _ _ _ e,
  inv := equivalence_of_target_equivalence.unit_iso_inv' _ _ _ e,
  hom_inv_id' := equivalence_of_target_equivalence.unit_iso_hom_inv_id' _ _ _ e,
  inv_hom_id' := equivalence_of_target_equivalence.unit_iso_inv_hom_id' _ _ _ e }

@[simps] def equivalence_of_target_equivalence.counit_hom' :
  equivalence_of_target_equivalence.inverse' A B C e ⋙
  equivalence_of_target_equivalence.functor' A B C e ⟶
  𝟭 (A ⥤ C) :=
{ app := λ F, { app := λ a, e.counit.app _, naturality' := λ _ _ _, e.counit.naturality _ },
  naturality' := λ _ _ _,
  begin
    ext F a,
    dsimp,
    simpa only [equivalence.fun_inv_map, category.assoc, iso.inv_hom_id_app,
      nat_iso.cancel_nat_iso_hom_left] using category.comp_id _,
  end }

@[simps] def equivalence_of_target_equivalence.counit_inv' :
  𝟭 (A ⥤ C) ⟶
  equivalence_of_target_equivalence.inverse' A B C e ⋙
    equivalence_of_target_equivalence.functor' A B C e :=
{ app := λ F, { app := λ a, e.counit_inv.app _, naturality' := λ _ _ _, e.counit_inv.naturality _ },
  naturality' := λ _ _ _,
  begin
    ext F a,
    dsimp,
    simp only [equivalence.fun_inv_map, iso.inv_hom_id_app_assoc],
  end }

@[simps] def equivalence_of_target_equivalence.counit_iso' :
  equivalence_of_target_equivalence.inverse' A B C e ⋙
  equivalence_of_target_equivalence.functor' A B C e ≅
  𝟭 (A ⥤ C) :=
{ hom := equivalence_of_target_equivalence.counit_hom' _ _ _ e,
  inv := equivalence_of_target_equivalence.counit_inv' _ _ _ e,
  hom_inv_id' :=
  begin
    ext F a,
    dsimp,
    simpa only [iso.hom_inv_id_app],
  end,
  inv_hom_id' :=
  begin
    ext F a,
    dsimp,
    simpa only [iso.inv_hom_id_app],
  end }

@[simps] def equivalence_of_target_equivalence : (A ⥤ B) ≌ (A ⥤ C) :=
{ functor := equivalence_of_target_equivalence.functor' _ _ _ e,
  inverse := equivalence_of_target_equivalence.inverse' _ _ _ e,
  unit_iso := equivalence_of_target_equivalence.unit_iso' _ _ _ e,
  counit_iso := equivalence_of_target_equivalence.counit_iso' _ _ _ e,
  functor_unit_iso_comp' := λ F,
  begin
    ext a,
    dsimp,
    simp only [equivalence.functor_unit_comp],
  end }

end category_theory.functor
