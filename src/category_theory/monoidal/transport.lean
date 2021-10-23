/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.natural_transformation

/-!
# Transport a monoidal structure along an equivalence.

When `C` and `D` are equivalent as categories,
we can transport a monoidal structure on `C` along the equivalence,
obtaining a monoidal structure on `D`.

We don't yet prove anything about this transported structure!
The next step would be to show that the original functor can be upgraded
to a monoidal functor with respect to this new structure.
-/

universes v₁ v₂ u₁ u₂

open category_theory
open category_theory.category
open category_theory.monoidal_category

namespace category_theory.monoidal

variables {C : Type u₁} [category.{v₁} C] [monoidal_category.{v₁} C]
variables {D : Type u₂} [category.{v₂} D]

/--
Transport a monoidal structure along an equivalence of (plain) categories.
-/
@[simps]
def transport (e : C ≌ D) : monoidal_category.{v₂} D :=
{ tensor_obj := λ X Y, e.functor.obj (e.inverse.obj X ⊗ e.inverse.obj Y),
  tensor_hom := λ W X Y Z f g, e.functor.map (e.inverse.map f ⊗ e.inverse.map g),
  tensor_unit := e.functor.obj (𝟙_ C),
  associator := λ X Y Z, e.functor.map_iso
  (((e.unit_iso.app _).symm ⊗ iso.refl _) ≪≫
    (α_ (e.inverse.obj X) (e.inverse.obj Y) (e.inverse.obj Z)) ≪≫
    (iso.refl _ ⊗ (e.unit_iso.app _))),
  left_unitor := λ X,
    e.functor.map_iso (((e.unit_iso.app _).symm ⊗ iso.refl _) ≪≫
      λ_ (e.inverse.obj X)) ≪≫ (e.counit_iso.app _),
  right_unitor := λ X,
    e.functor.map_iso ((iso.refl _ ⊗ (e.unit_iso.app _).symm) ≪≫
      ρ_ (e.inverse.obj X)) ≪≫ (e.counit_iso.app _),
  triangle' := λ X Y,
  begin
    dsimp,
    simp only [iso.hom_inv_id_app_assoc, comp_tensor_id, equivalence.unit_inverse_comp, assoc,
      equivalence.inv_fun_map, comp_id, functor.map_comp, id_tensor_comp, e.inverse.map_id],
    simp only [←e.functor.map_comp],
    congr' 2,
    slice_lhs 2 3 { rw [←id_tensor_comp], simp, dsimp, rw [tensor_id], },
    rw [category.id_comp, ←associator_naturality_assoc, triangle],
  end,
  pentagon' := λ W X Y Z,
  begin
    dsimp,
    simp only [iso.hom_inv_id_app_assoc, comp_tensor_id, assoc, equivalence.inv_fun_map,
      functor.map_comp, id_tensor_comp, e.inverse.map_id],
    simp only [←e.functor.map_comp],
    congr' 2,
    slice_lhs 4 5 { rw [←comp_tensor_id, iso.hom_inv_id_app], dsimp, rw [tensor_id], },
    simp only [category.id_comp, category.assoc],
    slice_lhs 5 6 { rw [←id_tensor_comp, iso.hom_inv_id_app], dsimp, rw [tensor_id], },
    simp only [category.id_comp, category.assoc],
    slice_rhs 2 3 { rw [id_tensor_comp_tensor_id, ←tensor_id_comp_id_tensor], },
    slice_rhs 1 2 { rw [←tensor_id, ←associator_naturality], },
    slice_rhs 3 4 { rw [←tensor_id, associator_naturality], },
    slice_rhs 2 3 { rw [←pentagon], },
    simp only [category.assoc],
    congr' 2,
    slice_lhs 1 2 { rw [associator_naturality], },
    simp only [category.assoc],
    congr' 1,
    slice_lhs 1 2
    { rw [←id_tensor_comp, ←comp_tensor_id, iso.hom_inv_id_app],
      dsimp, rw [tensor_id, tensor_id], },
    simp only [category.id_comp, category.assoc],
  end,
  left_unitor_naturality' := λ X Y f,
  begin
    dsimp,
    simp only [functor.map_comp, functor.map_id, category.assoc],
    erw ←e.counit_iso.hom.naturality,
    simp only [functor.comp_map, ←e.functor.map_comp_assoc],
    congr' 2,
    rw [e.inverse.map_id, id_tensor_comp_tensor_id_assoc, ←tensor_id_comp_id_tensor_assoc,
      left_unitor_naturality],
  end,
  right_unitor_naturality' := λ X Y f,
  begin
    dsimp,
    simp only [functor.map_comp, functor.map_id, category.assoc],
    erw ←e.counit_iso.hom.naturality,
    simp only [functor.comp_map, ←e.functor.map_comp_assoc],
    congr' 2,
    rw [e.inverse.map_id, tensor_id_comp_id_tensor_assoc, ←id_tensor_comp_tensor_id_assoc,
      right_unitor_naturality],
  end,
  associator_naturality' := λ X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃,
  begin
    dsimp,
    simp only [equivalence.inv_fun_map, functor.map_comp, category.assoc],
    simp only [←e.functor.map_comp],
    congr' 1,
    conv_lhs { rw [←tensor_id_comp_id_tensor] },
    slice_lhs 2 3 { rw [id_tensor_comp_tensor_id, ←tensor_id_comp_id_tensor, ←tensor_id], },
    simp only [category.assoc],
    slice_lhs 3 4 { rw [associator_naturality], },
    conv_lhs { simp only [comp_tensor_id], },
    slice_lhs 3 4 { rw [←comp_tensor_id, iso.hom_inv_id_app], dsimp, rw [tensor_id], },
    simp only [category.id_comp, category.assoc],
    slice_lhs 2 3 { rw [associator_naturality], },
    simp only [category.assoc],
    congr' 2,
    slice_lhs 1 1 { rw [←tensor_id_comp_id_tensor], },
    slice_lhs 2 3 { rw [←id_tensor_comp, tensor_id_comp_id_tensor], },
    slice_lhs 1 2 { rw [tensor_id_comp_id_tensor], },
    conv_rhs { congr, skip, rw [←id_tensor_comp_tensor_id, id_tensor_comp], },
    simp only [category.assoc],
    slice_rhs 1 2 { rw [←id_tensor_comp, iso.hom_inv_id_app], dsimp, rw [tensor_id],},
    simp only [category.id_comp, category.assoc],
    conv_rhs { rw [id_tensor_comp], },
    slice_rhs 2 3 { rw [id_tensor_comp_tensor_id, ←tensor_id_comp_id_tensor], },
    slice_rhs 1 2 { rw [id_tensor_comp_tensor_id], },
  end, }.

/-- A type synonym for `D`, which will carry the transported monoidal structure. -/
@[derive category, nolint unused_arguments]
def transported (e : C ≌ D) := D

instance (e : C ≌ D) : monoidal_category (transported e) := transport e
instance (e : C ≌ D) : inhabited (transported e) := ⟨𝟙_ _⟩

/--
We can upgrade `e.functor` to a lax monoidal functor from `C` to `D` with the transported structure.
-/
@[simps]
def lax_to_transported (e : C ≌ D) : lax_monoidal_functor C (transported e) :=
{ ε := 𝟙 (e.functor.obj (𝟙_ C)),
  μ := λ X Y, e.functor.map (e.unit_inv.app X ⊗ e.unit_inv.app Y),
  μ_natural' := λ X Y X' Y' f g,
  begin
    dsimp,
    simp only [equivalence.inv_fun_map, functor.map_comp, tensor_comp, category.assoc],
    simp only [←e.functor.map_comp],
    congr' 1,
    rw [←tensor_comp, iso.hom_inv_id_app, iso.hom_inv_id_app, ←tensor_comp],
    dsimp,
    rw [comp_id, comp_id],
  end,
  associativity' := λ X Y Z,
  begin
    dsimp,
    simp only [comp_tensor_id, assoc, equivalence.inv_fun_map, functor.map_comp, id_tensor_comp,
      e.inverse.map_id],
    simp only [←e.functor.map_comp],
    congr' 2,
    slice_lhs 3 3 { rw [←tensor_id_comp_id_tensor], },
    slice_lhs 2 3 { rw [←comp_tensor_id, iso.hom_inv_id_app], dsimp, rw [tensor_id] },
    simp only [id_comp],
    slice_rhs 2 3 { rw [←id_tensor_comp, iso.hom_inv_id_app], dsimp, rw [tensor_id] },
    simp only [id_comp],
    conv_rhs { rw [←id_tensor_comp_tensor_id _ (e.unit_inv.app X)], },
    dsimp only [functor.comp_obj],
    slice_rhs 3 4 { rw [←id_tensor_comp, iso.hom_inv_id_app], dsimp, rw [tensor_id] },
    simp only [id_comp],
    simp [associator_naturality],
  end,
  left_unitality' := λ X,
  begin
    dsimp,
    simp only [tensor_id, assoc, id_comp, functor.map_comp, e.inverse.map_id],
    rw equivalence.counit_app_functor,
    simp only [←e.functor.map_comp],
    congr' 1,
    rw [←left_unitor_naturality],
    simp,
  end,
  right_unitality' := λ X,
  begin
    dsimp,
    simp only [tensor_id, assoc, id_comp, functor.map_comp, e.inverse.map_id],
    rw equivalence.counit_app_functor,
    simp only [←e.functor.map_comp],
    congr' 1,
    rw [←right_unitor_naturality],
    simp,
  end,
  ..e.functor, }.

/--
We can upgrade `e.functor` to a monoidal functor from `C` to `D` with the transported structure.
-/
@[simps]
def to_transported (e : C ≌ D) : monoidal_functor C (transported e) :=
{ ε_is_iso := by { dsimp, apply_instance, },
  μ_is_iso := λ X Y, by { dsimp, apply_instance, },
  ..lax_to_transported e, }

/--
We can upgrade `e.inverse` to a lax monoidal functor from `D` with the transported structure to `C`.
-/
@[simps]
def lax_from_transported (e : C ≌ D) : lax_monoidal_functor (transported e) C :=
{ ε := e.unit.app (𝟙_ C),
  μ := λ  X Y, e.unit.app (e.inverse.obj X ⊗ e.inverse.obj Y),
  μ_natural' := λ X Y X' Y' f g,
  begin
    dsimp,
    simp only [iso.hom_inv_id_app_assoc, equivalence.inv_fun_map],
  end,
  associativity' := λ X Y Z,
  begin
    dsimp,
    simp only [iso.hom_inv_id_app_assoc, assoc, equivalence.inv_fun_map, functor.map_comp],
    slice_lhs 1 2 { rw [←comp_tensor_id, iso.hom_inv_id_app], dsimp, rw [tensor_id], },
    simp,
  end,
  left_unitality' := λ X,
  begin
    dsimp,
    simp only [iso.hom_inv_id_app_assoc, equivalence.unit_inverse_comp, assoc,
      equivalence.inv_fun_map, comp_id, functor.map_comp],
    slice_rhs 1 2 { rw [←comp_tensor_id, iso.hom_inv_id_app], dsimp, rw [tensor_id], },
    simp,
  end,
  right_unitality' := λ X,
  begin
    dsimp,
    simp only [iso.hom_inv_id_app_assoc, equivalence.unit_inverse_comp, assoc,
      equivalence.inv_fun_map, comp_id, functor.map_comp],
    slice_rhs 1 2 { rw [←id_tensor_comp, iso.hom_inv_id_app], dsimp, rw [tensor_id], },
    simp,
  end,
  ..e.inverse, }

/--
We can upgrade `e.inverse` to a monoidal functor from `D` with the transported structure to `C`.
-/
@[simps]
def from_transported (e : C ≌ D) : monoidal_functor (transported e) C :=
{ ε_is_iso := by { dsimp, apply_instance, },
  μ_is_iso := λ X Y, by { dsimp, apply_instance, },
  ..lax_from_transported e, }

/-- The unit isomorphism upgrades to a monoidal isomorphism. -/
@[simps]
def transported_monoidal_unit_iso (e : C ≌ D) :
  lax_monoidal_functor.id C ≅ lax_to_transported e ⊗⋙ lax_from_transported e :=
monoidal_nat_iso.of_components (λ X, e.unit_iso.app X) (λ X Y f, e.unit.naturality f)
  (by { dsimp, simp })
  (λ X Y,
  begin
    dsimp, simp only [iso.hom_inv_id_app_assoc, id_comp, equivalence.inv_fun_map],
    slice_rhs 1 2 { rw [←tensor_comp, iso.hom_inv_id_app, iso.hom_inv_id_app],
      dsimp, rw [tensor_id] },
    simp,
  end)

/-- The counit isomorphism upgrades to a monoidal isomorphism. -/
@[simps]
def transported_monoidal_counit_iso (e : C ≌ D) :
  lax_from_transported e ⊗⋙ lax_to_transported e ≅ lax_monoidal_functor.id (transported e) :=
monoidal_nat_iso.of_components (λ X, e.counit_iso.app X) (λ X Y f, e.counit.naturality f)
  (by { dsimp, simp })
  (λ X Y,
  begin
    dsimp, simp only [iso.hom_inv_id_app_assoc, id_comp, equivalence.inv_fun_map],
    simp only [equivalence.counit_app_functor, ←e.functor.map_id, ←e.functor.map_comp],
    congr' 1,
    simp [equivalence.unit_inv_app_inverse],
    dsimp,
    simp, -- See note [dsimp, simp].
  end)

-- We could put these together as an equivalence of monoidal categories,
-- but I don't want to do this quite yet.
-- Etingof-Gelaki-Nikshych-Ostrik "Tensor categories" define an equivalence of monoidal categories
-- as a monoidal functor which, as a functor, is an equivalence.
-- Presumably one can show that the inverse functor can be upgraded to a monoidal
-- functor in a unique way, such that the unit and counit are monoidal natural isomorphisms,
-- but I've never seen this explained or worked it out.

end category_theory.monoidal
