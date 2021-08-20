/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.category

/-!
# Monoidal opposites

We write `Cᵐᵒᵖ` for the monoidal opposite of a monoidal category `C`.
-/


universes v₁ v₂ u₁ u₂

variables {C : Type u₁}

namespace category_theory

open category_theory.monoidal_category

/-- A type synonym for the monoidal opposite. Use the notation `Cᵐᵒᵖ`. -/
@[nolint has_inhabited_instance]
def monoidal_opposite (C : Type u₁) := C

namespace monoidal_opposite

notation C `ᵐᵒᵖ`:std.prec.max_plus := monoidal_opposite C

/-- Think of an object of `C` as an object of `Cᵐᵒᵖ`. -/
@[pp_nodot]
def mop (X : C) : Cᵐᵒᵖ := X

/-- Think of an object of `Cᵐᵒᵖ` as an object of `C`. -/
@[pp_nodot]
def unmop (X : Cᵐᵒᵖ) : C := X

lemma op_injective : function.injective (mop : C → Cᵐᵒᵖ) := λ _ _, id
lemma unop_injective : function.injective (unmop : Cᵐᵒᵖ → C) := λ _ _, id

@[simp] lemma op_inj_iff (x y : C) : mop x = mop y ↔ x = y := iff.rfl
@[simp] lemma unop_inj_iff (x y : Cᵐᵒᵖ) : unmop x = unmop y ↔ x = y := iff.rfl

attribute [irreducible] monoidal_opposite

@[simp] lemma mop_unmop (X : Cᵐᵒᵖ) : mop (unmop X) = X := rfl
@[simp] lemma unmop_mop (X : C) : unmop (mop X) = X := rfl

instance monoidal_opposite_category [I : category.{v₁} C] : category Cᵐᵒᵖ :=
{ hom := λ X Y, unmop X ⟶ unmop Y,
  id := λ X, 𝟙 (unmop X),
  comp := λ X Y Z f g, f ≫ g, }

end monoidal_opposite

end category_theory

open category_theory
open category_theory.monoidal_opposite

variables [category.{v₁} C]

/-- The monoidal opposite of a morphism `f : X ⟶ Y` is just `f`, thought of as `mop X ⟶ mop Y`. -/
def quiver.hom.mop {X Y : C} (f : X ⟶ Y) : @quiver.hom Cᵐᵒᵖ _ (mop X) (mop Y) := f
/-- We can think of a morphism `f : mop X ⟶ mop Y` as a morphism `X ⟶ Y`. -/
def quiver.hom.unmop {X Y : Cᵐᵒᵖ} (f : X ⟶ Y) : unmop X ⟶ unmop Y := f

namespace category_theory

lemma mop_inj {X Y : C} :
  function.injective (quiver.hom.mop : (X ⟶ Y) → (mop X ⟶ mop Y)) :=
λ _ _ H, congr_arg quiver.hom.unmop H

lemma unmop_inj {X Y : Cᵐᵒᵖ} :
  function.injective (quiver.hom.unmop : (X ⟶ Y) → (unmop X ⟶ unmop Y)) :=
λ _ _ H, congr_arg quiver.hom.mop H

@[simp] lemma unmop_mop {X Y : C} {f : X ⟶ Y} : f.mop.unmop = f := rfl
@[simp] lemma mop_unmop {X Y : Cᵐᵒᵖ} {f : X ⟶ Y} : f.unmop.mop = f := rfl

@[simp] lemma mop_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} :
  (f ≫ g).mop = f.mop ≫ g.mop := rfl
@[simp] lemma mop_id {X : C} : (𝟙 X).mop = 𝟙 (mop X) := rfl

@[simp] lemma unmop_comp {X Y Z : Cᵐᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z} :
  (f ≫ g).unmop = f.unmop ≫ g.unmop := rfl
@[simp] lemma unmop_id {X : Cᵐᵒᵖ} : (𝟙 X).unmop = 𝟙 (unmop X) := rfl

@[simp] lemma unmop_id_mop {X : C} : (𝟙 (mop X)).unmop = 𝟙 X := rfl
@[simp] lemma mop_id_unmop {X : Cᵐᵒᵖ} : (𝟙 (unmop X)).mop = 𝟙 X := rfl

namespace iso

variables {X Y : C}

/-- An isomorphism in `C` gives an isomorphism in `Cᵐᵒᵖ`. -/
@[simps]
def mop (f : X ≅ Y) : mop X ≅ mop Y :=
{ hom := f.hom.mop,
  inv := f.inv.mop,
  hom_inv_id' := unmop_inj f.hom_inv_id,
  inv_hom_id' := unmop_inj f.inv_hom_id }

end iso

variables [monoidal_category.{v₁} C]

open opposite monoidal_category

instance monoidal_category_op : monoidal_category Cᵒᵖ :=
{ tensor_obj := λ X Y, op (unop X ⊗ unop Y),
  tensor_hom := λ X₁ Y₁ X₂ Y₂ f g, (f.unop ⊗ g.unop).op,
  tensor_unit := op (𝟙_ C),
  associator := λ X Y Z, (α_ (unop X) (unop Y) (unop Z)).symm.op,
  left_unitor := λ X, (λ_ (unop X)).symm.op,
  right_unitor := λ X, (ρ_ (unop X)).symm.op,
  associator_naturality' :=
  begin
    intros,
    apply quiver.hom.unop_inj,
    simp [associator_inv_naturality],
  end,
  left_unitor_naturality' :=
  begin
    intros,
    apply quiver.hom.unop_inj,
    simp [left_unitor_inv_naturality],
  end,
  right_unitor_naturality' :=
  begin
    intros,
    apply quiver.hom.unop_inj,
    simp [right_unitor_inv_naturality],
  end,
  triangle' :=
  begin
    intros,
    apply quiver.hom.unop_inj,
    dsimp,
    simp,
  end,
  pentagon' :=
  begin
    intros,
    apply quiver.hom.unop_inj,
    dsimp,
    simp [pentagon_inv],
  end }

lemma op_tensor_obj (X Y : Cᵒᵖ) : X ⊗ Y = op (unop X ⊗ unop Y) := rfl
lemma op_tensor_unit : (𝟙_ Cᵒᵖ) = op (𝟙_ C) := rfl

instance monoidal_category_mop : monoidal_category Cᵐᵒᵖ :=
{ tensor_obj := λ X Y, mop (unmop Y ⊗ unmop X),
  tensor_hom := λ X₁ Y₁ X₂ Y₂ f g, (g.unmop ⊗ f.unmop).mop,
  tensor_unit := mop (𝟙_ C),
  associator := λ X Y Z, (α_ (unmop Z) (unmop Y) (unmop X)).symm.mop,
  left_unitor := λ X, (ρ_ (unmop X)).mop,
  right_unitor := λ X, (λ_ (unmop X)).mop,
  associator_naturality' :=
  begin
    intros,
    apply unmop_inj,
    simp [associator_inv_naturality],
  end,
  left_unitor_naturality' :=
  begin
    intros,
    apply unmop_inj,
    simp [right_unitor_naturality],
  end,
  right_unitor_naturality' :=
  begin
    intros,
    apply unmop_inj,
    simp [left_unitor_naturality],
  end,
  triangle' :=
  begin
    intros,
    apply unmop_inj,
    dsimp,
    simp,
  end,
  pentagon' :=
  begin
    intros,
    apply unmop_inj,
    dsimp,
    simp [pentagon_inv],
  end }

lemma mop_tensor_obj (X Y : Cᵐᵒᵖ) : X ⊗ Y = mop (unmop Y ⊗ unmop X) := rfl
lemma mop_tensor_unit : (𝟙_ Cᵐᵒᵖ) = mop (𝟙_ C) := rfl

end category_theory
