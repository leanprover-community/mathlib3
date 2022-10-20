/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.natural_transformation
import category_theory.monoidal.Mon_

/-!
# Transport a monoidal structure along an equivalence.

When `C` and `D` are equivalent as categories,
we can transport a monoidal structure on `C` along the equivalence,
obtaining a monoidal structure on `D`.

We then upgrade the original functor and its inverse to monoidal functors
with respect to the new monoidal structure on `D`.
-/

universes v₁ v₂ u₁ u₂

noncomputable theory

open category_theory
open category_theory.category
open category_theory.monoidal_category

namespace category_theory.monoidal

variables {C : Type u₁} [category.{v₁} C] [monoidal_category.{v₁} C]
variables {D : Type u₂} [category.{v₂} D]

/--
Transport a monoidal structure along an equivalence of (plain) categories.
-/
@[simps {attrs := [`_refl_lemma]}] -- We just want these simp lemmas locally
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

section
local attribute [simp] transport_tensor_unit

section
local attribute [simp] transport_tensor_hom transport_associator
  transport_left_unitor transport_right_unitor

/--
We can upgrade `e.functor` to a lax monoidal functor from `C` to `D` with the transported structure.
-/
@[simps]
def lax_to_transported (e : C ≌ D) : lax_monoidal_functor C (transported e) :=
{ to_functor := e.functor,
  ε := 𝟙 (e.functor.obj (𝟙_ C)),
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
    simp only [associator_conjugation, ←tensor_id, ←tensor_comp, iso.inv_hom_id,
      iso.inv_hom_id_assoc, category.assoc, category.id_comp, category.comp_id],
  end,
  left_unitality' := λ X,
  begin
    dsimp,
    simp only [tensor_id, assoc, id_comp, functor.map_comp, e.inverse.map_id],
    rw equivalence.counit_app_functor,
    simp only [←e.functor.map_comp],
    congr' 1,
    simp only [←left_unitor_naturality, id_comp, ←tensor_comp_assoc, comp_id],
  end,
  right_unitality' := λ X,
  begin
    dsimp,
    simp only [tensor_id, assoc, id_comp, functor.map_comp, e.inverse.map_id],
    rw equivalence.counit_app_functor,
    simp only [←e.functor.map_comp],
    congr' 1,
    simp only [←right_unitor_naturality, id_comp, ←tensor_comp_assoc, comp_id],
  end, }.
end

/--
We can upgrade `e.functor` to a monoidal functor from `C` to `D` with the transported structure.
-/
@[simps]
def to_transported (e : C ≌ D) : monoidal_functor C (transported e) :=
{ to_lax_monoidal_functor := lax_to_transported e,
  ε_is_iso := by { dsimp, apply_instance, },
  μ_is_iso := λ X Y, by { dsimp, apply_instance, }, }
end

instance (e : C ≌ D) : is_equivalence (to_transported e).to_functor :=
by { dsimp, apply_instance, }

/--
We can upgrade `e.inverse` to a monoidal functor from `D` with the transported structure to `C`.
-/
@[simps]
def from_transported (e : C ≌ D) : monoidal_functor (transported e) C :=
monoidal_inverse (to_transported e)

/-- The unit isomorphism upgrades to a monoidal isomorphism. -/
@[simps]
def transported_monoidal_unit_iso (e : C ≌ D) :
  lax_monoidal_functor.id C ≅
    lax_to_transported e ⊗⋙ (from_transported e).to_lax_monoidal_functor :=
as_iso (monoidal_unit (to_transported e))

/-- The counit isomorphism upgrades to a monoidal isomorphism. -/
@[simps]
def transported_monoidal_counit_iso (e : C ≌ D) :
  (from_transported e).to_lax_monoidal_functor ⊗⋙ lax_to_transported e ≅
    lax_monoidal_functor.id (transported e) :=
as_iso (monoidal_counit (to_transported e))

section Mon_

def to_punit_to_transported.ε (e : C ≌ D) (F : lax_monoidal_functor (discrete punit) C) :
  𝟙_ (transported e) ⟶ e.functor.obj (F.to_functor.obj (𝟙_ (discrete punit))) :=
e.functor.map F.ε

def to_punit_to_transported.μ (e : C ≌ D) (F : lax_monoidal_functor (discrete punit) C) (X Y) :
  (e.functor.obj (F.to_functor.obj X) ⊗ e.functor.obj (F.to_functor.obj Y) : transported e) ⟶
    e.functor.obj (F.to_functor.obj (X ⊗ Y)) :=
((to_transported e).μ_iso (F.to_functor.obj X) (F.to_functor.obj Y)).hom ≫
  e.functor.map (F.μ X Y)

lemma to_punit_to_transported.associativity'_auxL (e : C ≌ D)
  (F : lax_monoidal_functor (discrete punit) C) (X Y Z) :
  (to_punit_to_transported.μ e F X Y ⊗ 𝟙 (e.functor.obj (F.to_functor.obj Z))) ≫
    to_punit_to_transported.μ e F (X ⊗ Y) Z ≫ e.functor.map (F.to_functor.map (α_ X Y Z).hom) =

  ((to_transported e).μ_iso₂' _ _ _).hom ≫

  (e.functor.map ((F.μ X Y ⊗ 𝟙 (F.to_functor.obj Z)) ≫ F.μ (X ⊗ Y) Z ≫
    F.to_functor.map (α_ X Y Z).hom)) :=
begin
  dsimp [to_punit_to_transported.μ],
  simp only [comp_tensor_id, discrete.functor_map_id, category_theory.functor.map_id, assoc,
    comp_id, functor.map_comp],
  congr' 1,
  simp only [←category.assoc],
  congr' 1,
  rw [←e.functor.map_comp, ←tensor_comp, category.comp_id, ←e.functor.map_id],
  erw [(to_transported e).map_tensor'],
  dsimp,
  rw [assoc, assoc, is_iso.inv_hom_id, category.comp_id, ←e.functor.map_comp,
    ←tensor_comp, category.comp_id],
end

lemma to_punit_to_transported.associativity'_auxR (e : C ≌ D)
  (F : lax_monoidal_functor (discrete punit) C) (X Y Z) :
  (α_ (e.functor.obj (F.to_functor.obj X)) (e.functor.obj (F.to_functor.obj Y))
     (e.functor.obj (F.to_functor.obj Z))).hom ≫
  (𝟙 (e.functor.obj (F.to_functor.obj X)) ⊗ to_punit_to_transported.μ e F Y Z) ≫
    to_punit_to_transported.μ e F X (Y ⊗ Z) =

  ((to_transported e).μ_iso₂' _ _ _).hom ≫

  e.functor.map
    ((α_ (F.to_functor.obj X) (F.to_functor.obj Y) (F.to_functor.obj Z)).hom ≫
       (𝟙 (F.to_functor.obj X) ⊗ F.μ Y Z) ≫ F.μ X (Y ⊗ Z)) :=
begin
  dsimp [to_punit_to_transported.μ, transport_associator],
  simp only [functor.map_comp, id_tensor_comp, assoc],
  simp only [←assoc],
  congr' 1,
  simp only [assoc],
  erw [←e.functor.map_id, (to_transported e).map_tensor', (to_transported e).map_tensor'],
  dsimp,
  simp only [assoc, is_iso.inv_hom_id, category.comp_id],
  simp only [←assoc],
  congr' 1,
  simp only [assoc, is_iso.inv_hom_id, category.comp_id],
  rw [←e.functor.map_comp, ←tensor_comp, category.comp_id, ←e.functor.map_comp, ←tensor_comp,
    category.id_comp, ←assoc (e.unit_iso.hom.app _), iso.hom_inv_id_app,
    category.id_comp],
  erw [←e.functor.map_id, (to_transported e).map_tensor'],
  dsimp,
  rw [assoc, assoc, ←assoc (inv _), is_iso.inv_hom_id, category.id_comp],
  simp only [←e.functor.map_comp],
  congr' 1,
  simp only [associator_conjugation, assoc, iso.inv_hom_id, comp_id],
  have eq1 : e.unit_iso.inv.app
    (e.inverse.obj (e.functor.obj (F.to_functor.obj X)) ⊗ e.inverse.obj (e.functor.obj (F.to_functor.obj Y))) ⊗
  𝟙 (e.inverse.obj (e.functor.obj (F.to_functor.obj Z))) =
  inv (e.unit.app _ ⊗ 𝟙 _),
  { ext, rw [←tensor_comp, iso.hom_inv_id_app, id_comp, tensor_id], },
  rw [eq1, is_iso.inv_comp_eq, ←assoc, ←tensor_comp, iso.hom_inv_id_app, id_comp],
  dsimp,
  rw [←tensor_id, ←assoc, associator_naturality, assoc, ←tensor_comp, id_comp, ←tensor_comp,
    id_comp, comp_id],
end

lemma to_punit_to_transported.associativity' (e : C ≌ D) (F : lax_monoidal_functor (discrete punit) C)
  (X Y Z) :
  (to_punit_to_transported.μ e F X Y ⊗ 𝟙 (e.functor.obj (F.to_functor.obj Z))) ≫
    to_punit_to_transported.μ e F (X ⊗ Y) Z ≫ e.functor.map (F.to_functor.map (α_ X Y Z).hom) =
  (α_ (e.functor.obj (F.to_functor.obj X)) (e.functor.obj (F.to_functor.obj Y))
       (e.functor.obj (F.to_functor.obj Z))).hom ≫
    (𝟙 (e.functor.obj (F.to_functor.obj X)) ⊗ to_punit_to_transported.μ e F Y Z) ≫
      to_punit_to_transported.μ e F X (Y ⊗ Z) :=
by rw [to_punit_to_transported.associativity'_auxL, F.associativity,
  to_punit_to_transported.associativity'_auxR]

lemma to_punit_to_transported.left_unitality_auxL
  (e : C ≌ D) (F : lax_monoidal_functor (discrete punit) C) (X : discrete punit) :
  (λ_ (e.functor.obj (F.to_functor.obj X)) : (𝟙_ (transported e)) ⊗ _ ≅ _).hom =
  ((λ_ _).hom ≫ e.functor.map (λ_ _).inv) ≫ e.functor.map (λ_ (F.to_functor.obj X)).hom :=
begin
  simp only [functor.map_comp, assoc, transport_left_unitor, iso.trans_hom, functor.map_iso_hom,
    tensor_iso_hom, iso.symm_hom, iso.app_inv, iso.refl_hom, iso.app_hom],
  rw [←e.functor.map_comp, iso.inv_hom_id, e.functor.map_id, comp_id],
end

lemma to_punit_to_transported.left_unitality_auxR
  (e : C ≌ D) (F : lax_monoidal_functor (discrete punit) C) (X : discrete punit) :
  (to_punit_to_transported.ε e F ⊗ 𝟙 (e.functor.obj (F.to_functor.obj X))) ≫
  to_punit_to_transported.μ e F (𝟙_ (discrete punit)) X ≫ e.functor.map (F.to_functor.map (λ_ X).hom) =
  ((λ_ _).hom ≫ e.functor.map (λ_ _).inv) ≫

  e.functor.map
  ((F.ε ⊗ 𝟙 (F.to_functor.obj X)) ≫ F.μ (𝟙_ (discrete punit)) X ≫ F.to_functor.map (λ_ X).hom) :=
begin
  simp only [to_punit_to_transported.ε, to_punit_to_transported.μ, transport_left_unitor, monoidal_functor.μ_iso_hom, assoc,
    iso.trans_hom, functor.map_iso_hom, tensor_iso_hom, iso.symm_hom, iso.app_inv, iso.refl_hom, iso.app_hom,
    functor.map_comp],
  dsimp,
  simp only [←assoc],
  congr' 2,
  erw [←e.functor.map_id, (to_transported e).map_tensor'],
  dsimp,
  rw [assoc, assoc, is_iso.inv_hom_id, comp_id],
  congr' 1,
  simp only [assoc],
  have eq1 : e.functor.map (e.unit_iso.inv.app (𝟙_ C) ⊗ 𝟙 (e.inverse.obj (e.functor.obj (F.to_functor.obj X)))) =
    inv (e.functor.map (e.unit.app _ ⊗ 𝟙 _)),
  { ext, rw [←e.functor.map_comp, ←tensor_comp, comp_id, iso.hom_inv_id_app, tensor_id, e.functor.map_id], },
  rw [eq1],
  symmetry,
  rw [is_iso.inv_comp_eq, ←e.functor.map_comp, ←tensor_comp, iso.hom_inv_id_app, id_comp],
  dsimp,
  simp only [left_unitor_conjugation, functor.map_comp],
  rw e.counit_app_functor,
end

lemma to_punit_to_transported.left_unitality'
  (e : C ≌ D) (F : lax_monoidal_functor (discrete punit) C) (X : discrete punit) :
  (λ_ (e.functor.obj (F.to_functor.obj X))).hom =
  (to_punit_to_transported.ε e F ⊗ 𝟙 (e.functor.obj (F.to_functor.obj X))) ≫
  to_punit_to_transported.μ e F (𝟙_ (discrete punit)) X ≫ e.functor.map (F.to_functor.map (λ_ X).hom) :=
by rw [to_punit_to_transported.left_unitality_auxL, lax_monoidal_functor.left_unitality,
    to_punit_to_transported.left_unitality_auxR]

lemma to_punit_to_transported.right_unitality'_auxL
  (e : C ≌ D) (F : lax_monoidal_functor (discrete punit) C) (X : discrete punit) :
  (ρ_ (e.functor.obj (F.to_functor.obj X)) : (_ ⊗ _ : transported e) ≅ _).hom =
  ((to_transported e).μ _ _) ≫
  e.functor.map (ρ_ _).hom :=
begin
  simp only [transport_right_unitor, functor.map_iso_trans, iso.trans_assoc, iso.trans_hom, functor.map_iso_hom, tensor_iso_hom,
    iso.refl_hom, iso.symm_hom, iso.app_inv, iso.app_hom, functor.map_comp],
  dsimp,
  erw [(to_transported e).map_right_unitor, (to_transported e).map_right_unitor],
  dsimp,
  erw [is_iso.inv_id, tensor_id, id_comp, tensor_id, id_comp],
  conv_rhs { rw [←assoc, is_iso.hom_inv_id, id_comp] },
  rw e.counit_app_functor,
  conv_lhs { rw ←e.inverse_counit_inv_comp (e.functor.obj (F.to_functor.obj X)) },
  have eq1 : inv (e.functor.map (e.unit_inv.app (e.inverse.obj (e.functor.obj (F.to_functor.obj X))) ⊗ e.unit_inv.app (𝟙_ C))) =
    e.functor.map (e.unit.app _ ⊗ e.unit.app _),
  { ext, rw [←e.functor.map_comp, ←tensor_comp, iso.inv_hom_id_app, iso.inv_hom_id_app, tensor_id, e.functor.map_id], },
  erw [eq1, ←assoc, ←assoc, ←e.functor.map_comp, ←tensor_comp, iso.inv_hom_id_app,
    category.assoc (e.inverse.map _), iso.inv_hom_id_app, comp_id],
  dsimp,
  erw [assoc, ←right_unitor_naturality, ←assoc, ←e.functor.map_comp, ←tensor_comp, id_comp,
    e.counit_inv_app_functor, ←e.inverse.map_comp, ←e.functor.map_comp, iso.hom_inv_id_app,
    e.inverse.map_id, e.functor.map_id, e.inverse.map_id, tensor_id, e.functor.map_id, id_comp],
end

lemma to_punit_to_transported.right_unitality'_auxR
  (e : C ≌ D) (F : lax_monoidal_functor (discrete punit) C) (X : discrete punit) :
  (tensor_hom (𝟙 (e.functor.obj (F.to_functor.obj X))) (to_punit_to_transported.ε e F)) ≫
  to_punit_to_transported.μ e F X (𝟙_ (discrete punit)) ≫ e.functor.map (F.to_functor.map (ρ_ X).hom) =
  ((to_transported e).μ _ _) ≫
  e.functor.map
    ((𝟙 (F.to_functor.obj X) ⊗ F.ε) ≫ F.μ X (𝟙_ (discrete punit)) ≫ F.to_functor.map (ρ_ X).hom) :=
begin
  simp only [to_punit_to_transported.ε, to_punit_to_transported.μ, monoidal_functor.μ_iso_hom, assoc,
    functor.map_comp],
  dsimp,
  simp only [←assoc],
  congr' 2,
  rw [←e.functor.map_comp, ←tensor_comp, comp_id],
  have eq1 : e.functor.map (e.unit_inv.app (F.to_functor.obj X) ⊗ e.unit_inv.app (F.to_functor.obj (𝟙_ (discrete punit)))) =
  inv (e.functor.map (e.unit.app _ ⊗ e.unit.app _)),
  { ext, rw [←e.functor.map_comp, ←tensor_comp, iso.hom_inv_id_app, iso.hom_inv_id_app, tensor_id, e.functor.map_id], },
  rw [eq1, is_iso.comp_inv_eq, ←e.functor.map_comp, ←tensor_comp, iso.inv_hom_id_app],
  erw [←e.functor.map_id, (to_transported e).map_tensor'],
  dsimp,
  rw [←assoc],
  symmetry,
  erw [is_iso.eq_comp_inv, ←e.functor.map_comp, ←tensor_comp, id_comp, assoc,
    iso.hom_inv_id_app, comp_id, ←e.functor.map_comp, ←tensor_comp, comp_id],
end

lemma to_punit_to_transported.right_unitality'
  (e : C ≌ D) (F : lax_monoidal_functor (discrete punit) C) (X : discrete punit) :
  (ρ_ (e.functor.obj (F.to_functor.obj X))).hom =
  (𝟙 (e.functor.obj (F.to_functor.obj X)) ⊗ to_punit_to_transported.ε e F) ≫
    to_punit_to_transported.μ e F X (𝟙_ (discrete punit)) ≫ e.functor.map (F.to_functor.map (ρ_ X).hom) :=
begin
  rw [to_punit_to_transported.right_unitality'_auxL, lax_monoidal_functor.right_unitality,
    to_punit_to_transported.right_unitality'_auxR],
end

@[simps] def to_punit_to_transported (e : C ≌ D) (F : lax_monoidal_functor (discrete punit) C) :
  lax_monoidal_functor (discrete punit) (transported e) :=
{ ε := to_punit_to_transported.ε e F,
  μ := to_punit_to_transported.μ e F,
  μ_natural' := begin
    rintros ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟩⟩,
    dsimp, simp only [category_theory.functor.map_id, tensor_id, id_comp, comp_id],
  end,
  associativity' := to_punit_to_transported.associativity' e F,
  left_unitality' := to_punit_to_transported.left_unitality' e F,
  right_unitality' := to_punit_to_transported.right_unitality' e F,
  ..(F.to_functor ⋙ e.functor)}

@[simps] def to_punit_to_transported.map (e : C ≌ D) {F G : lax_monoidal_functor (discrete punit) C}
  (α : F ⟶ G) : to_punit_to_transported e F ⟶ to_punit_to_transported e G :=
{ app := λ X, e.functor.map $ α.app X,
  naturality' :=
  begin
    rintros ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟩⟩,
    dsimp,
    simp only [category_theory.functor.map_id, id_comp, comp_id],
  end,
  unit' := begin
    dsimp [to_punit_to_transported.ε],
    rw [←e.functor.map_comp],
    congr',
    exact α.unit',
  end,
  tensor' := λ X Y,
  begin
    dsimp [to_punit_to_transported.μ],
    have := α.tensor' X Y,
    rw [←e.functor.map_comp, ←e.functor.map_comp, assoc, α.tensor' X Y, e.functor.map_comp,
      e.functor.map_comp, ←assoc, ←assoc],
    congr' 1,
    erw [(to_transported e).map_tensor'],
    dsimp,
    rw [assoc, assoc, is_iso.inv_hom_id, comp_id],
  end }

lemma to_punit_to_transported.map_id (e : C ≌ D) (F) :
  to_punit_to_transported.map e (𝟙 F) = 𝟙 _ :=
begin
  ext ⟨⟨⟩⟩,
  simp only [to_punit_to_transported.map_to_nat_trans_app],
  erw [nat_trans.id_app, e.functor.map_id],
  refl,
end

lemma to_punit_to_transported.map_comp (e : C ≌ D)
  {X Y Z : lax_monoidal_functor (discrete punit) C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  to_punit_to_transported.map e (f ≫ g) = to_punit_to_transported.map e f ≫ to_punit_to_transported.map e g :=
begin
  ext,
  simp only [to_punit_to_transported.map_to_nat_trans_app, monoidal_nat_trans.comp_to_nat_trans_lax, nat_trans.comp_app,
  functor.map_comp],
end

@[simps] def to_punit_to_transported.functor (e : C ≌ D) :
  lax_monoidal_functor (discrete punit) C ⥤ lax_monoidal_functor (discrete punit) (transported e) :=
{ obj := to_punit_to_transported e,
  map := λ _ _, to_punit_to_transported.map e,
  map_id' := to_punit_to_transported.map_id e,
  map_comp' := λ _ _ _, to_punit_to_transported.map_comp e }

def from_punit_to_transported.ε (e : C ≌ D) (F : lax_monoidal_functor (discrete punit) (transported e)) :
  𝟙_ C ⟶ e.inverse.obj (F.to_functor.obj (𝟙_ (discrete punit))) :=
e.unit.app _ ≫ e.inverse.map (F.ε)

def from_punit_to_transported.μ (e : C ≌ D)
  (F : lax_monoidal_functor (discrete punit) (transported e)) (X Y) :
e.inverse.obj (F.to_functor.obj X) ⊗ e.inverse.obj (F.to_functor.obj Y) ⟶ e.inverse.obj (F.to_functor.obj (X ⊗ Y)) :=
(from_transported e).μ _ _ ≫ e.inverse.map (F.μ X Y)

lemma from_punit_to_transported.associativity'_auxL (e : C ≌ D)
  (F : lax_monoidal_functor (discrete punit) (transported e)) (X Y Z) :
(from_punit_to_transported.μ e F X Y ⊗ 𝟙 (e.inverse.obj (F.to_functor.obj Z))) ≫
    from_punit_to_transported.μ e F (X ⊗ Y) Z ≫ e.inverse.map (F.to_functor.map (α_ X Y Z).hom) =
((from_transported e).μ_iso₂' _ _ _).hom ≫
e.inverse.map ((F.μ X Y ⊗ 𝟙 (F.to_functor.obj Z)) ≫ F.μ (X ⊗ Y) Z ≫ F.to_functor.map (α_ X Y Z).hom) :=
begin
  dsimp [from_punit_to_transported.μ],
  simp only [from_transported_to_lax_monoidal_functor_μ, assoc, comp_tensor_id,
    associator_conjugation, discrete.functor_map_id, category_theory.functor.map_id, comp_id,
    functor.map_comp, iso.cancel_iso_hom_left],
  congr' 4,
  simp only [←assoc],
  congr' 1,
  simp only [assoc],
  erw [←e.inverse.map_id, (from_transported e).map_tensor'],
  simp only [from_transported_to_lax_monoidal_functor_μ, assoc, is_iso.inv_hom_id, comp_id],
  congr' 1,
end

lemma from_punit_to_transported.associativity'_auxR (e : C ≌ D)
  (F : lax_monoidal_functor (discrete punit) (transported e)) (X Y Z) :
(α_ (e.inverse.obj (F.to_functor.obj X)) (e.inverse.obj (F.to_functor.obj Y))
     (e.inverse.obj (F.to_functor.obj Z))).hom ≫
  (𝟙 (e.inverse.obj (F.to_functor.obj X)) ⊗ from_punit_to_transported.μ e F Y Z) ≫
    from_punit_to_transported.μ e F X (Y ⊗ Z) =
((from_transported e).μ_iso₂' _ _ _).hom ≫
e.inverse.map ((α_ (F.to_functor.obj X) (F.to_functor.obj Y) (F.to_functor.obj Z)).hom ≫
  (𝟙 (F.to_functor.obj X) ⊗ F.μ Y Z) ≫ F.μ X (Y ⊗ Z)) :=
sorry

lemma from_punit_to_transported.associativity' (e : C ≌ D)
  (F : lax_monoidal_functor (discrete punit) (transported e)) (X Y Z) :
(from_punit_to_transported.μ e F X Y ⊗ 𝟙 (e.inverse.obj (F.to_functor.obj Z))) ≫
    from_punit_to_transported.μ e F (X ⊗ Y) Z ≫ e.inverse.map (F.to_functor.map (α_ X Y Z).hom) =
(α_ (e.inverse.obj (F.to_functor.obj X)) (e.inverse.obj (F.to_functor.obj Y))
     (e.inverse.obj (F.to_functor.obj Z))).hom ≫
  (𝟙 (e.inverse.obj (F.to_functor.obj X)) ⊗ from_punit_to_transported.μ e F Y Z) ≫
    from_punit_to_transported.μ e F X (Y ⊗ Z) :=
by rw [from_punit_to_transported.associativity'_auxL, F.associativity,
  from_punit_to_transported.associativity'_auxR]

@[simps] def lax_monoid_functor_from_punit_equivalence (e : C ≌ D) :
  lax_monoidal_functor (discrete punit) C ≌ lax_monoidal_functor (discrete punit) (transported e) :=
{ functor := to_punit_to_transported.functor e,
  inverse :=
  { obj := λ F,
    { ε := from_punit_to_transported.ε e F,
      μ := from_punit_to_transported.μ e F,
      μ_natural' :=
      begin
        rintros ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟩⟩,
        dsimp, simp only [category_theory.functor.map_id, tensor_id, id_comp, comp_id],
      end,
      associativity' := from_punit_to_transported.associativity' e F,
      left_unitality' := sorry,
      right_unitality' := sorry,
      .. (F.to_functor ⋙ e.inverse) },
    map := _,
    map_id' := _,
    map_comp' := _ },
  unit_iso := sorry,
  counit_iso := sorry,
  functor_unit_iso_comp' := sorry }

def Mon_equivalence_of_equivalence (e : C ≌ D) : Mon_ C ≌ Mon_ (transported e) :=
(Mon_.equiv_lax_monoidal_functor_punit _).symm.trans $
  (lax_monoid_functor_from_punit_equivalence e).trans $
    Mon_.equiv_lax_monoidal_functor_punit _

end Mon_

end category_theory.monoidal
