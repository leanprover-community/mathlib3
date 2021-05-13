/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.opposite
import category_theory.monoidal.functor
import tactic.rewrite_search

universes v₁ v₂ u₁ u₂

namespace category_theory

open opposite
open monoidal_opposite
open category_theory.monoidal_category

variables {C : Type u₁} [category.{v₁} C] [monoidal_category.{v₁} C]

/--
A choice of dual object. Use `Xᘁ` to select an arbitrary representative.

The literature is not consistent about the distinction between left and right duals:
this is the right dual in the sense of https://ncatlab.org/nlab/show/rigid+monoidal+category.
-/
structure dual_data (X : C) :=
(dual : C)
(ev : X ⊗ dual ⟶ 𝟙_ C)
(coev : 𝟙_ C ⟶ dual ⊗ X)
(zigzag₁ : (ρ_ X).inv ≫ (𝟙 X ⊗ coev) ≫ (α_ _ _ _).inv ≫ (ev ⊗ 𝟙 X) ≫ (λ_ X).hom = 𝟙 X)
(zigzag₂ :
  (λ_ dual).inv ≫ (coev ⊗ 𝟙 dual) ≫ (α_ _ _ _).hom ≫ (𝟙 dual ⊗ ev) ≫ (ρ_ dual).hom = 𝟙 dual)

def dual_data.ext {X : C} (d e : dual_data X) : d.dual ≅ e.dual :=
{ hom := (λ_ _).inv ≫ (e.coev ⊗ 𝟙 _) ≫ (α_ _ _ _).hom ≫ (𝟙 _ ⊗ d.ev) ≫ (ρ_ _).hom,
  inv := (λ_ _).inv ≫ (d.coev ⊗ 𝟙 _) ≫ (α_ _ _ _).hom ≫ (𝟙 _ ⊗ e.ev) ≫ (ρ_ _).hom,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry, }

-- TODO this isomorphism intertwines `ev` and `coev`, and is the unique such isomorphism.

variables (C)

def dual_data.tensor_unit : dual_data (𝟙_ C) :=
{ dual := 𝟙_ C,
  ev := (λ_ _).hom,
  coev := (ρ_ _).inv,
  zigzag₁ := begin sorry, end,
  zigzag₂ := begin sorry, end, }

variables {C}

def dual_data.tensor_obj {X Y : C} (d : dual_data X) (e : dual_data Y) : dual_data (X ⊗ Y) :=
{ dual := e.dual ⊗ d.dual,
  ev := (α_ _ _ _).hom ≫ (𝟙 X ⊗ ((α_ _ _ _).inv ≫ (e.ev ⊗ 𝟙 _) ≫ (λ_ d.dual).hom)) ≫ d.ev,
  coev := e.coev ≫ (((ρ_ e.dual).inv ≫ (𝟙 _ ⊗ d.coev) ≫ (α_ _ _ _).inv) ⊗ 𝟙 Y) ≫ (α_ _ _ _).hom,
  zigzag₁ := sorry,
  zigzag₂ := sorry, }

class has_dual (X : C) : Prop :=
(out : nonempty (dual_data X))

attribute [instance] has_dual.out

noncomputable theory

def dual (X : C) [has_dual X] : C := (classical.arbitrary (dual_data X)).dual

-- From https://en.wikipedia.org/wiki/Unified_Canadian_Aboriginal_Syllabics_(Unicode_block)
postfix `ᘁ`:700 := dual

def ev (X : C) [has_dual X] : X ⊗ Xᘁ ⟶ 𝟙_ C := (classical.arbitrary (dual_data X)).ev
def coev (X : C) [has_dual X] : 𝟙_ C ⟶ Xᘁ ⊗ X := (classical.arbitrary (dual_data X)).coev

lemma dual_zigzag₁ (X : C) [has_dual X] :
  (ρ_ X).inv ≫ (𝟙 X ⊗ coev X) ≫ (α_ _ _ _).inv ≫ (ev X ⊗ 𝟙 X) ≫ (λ_ X).hom = 𝟙 X :=
(classical.arbitrary (dual_data X)).zigzag₁

lemma dual_zigzag₂ (X : C) [has_dual X] :
  (λ_ (Xᘁ)).inv ≫ (coev X ⊗ 𝟙 (Xᘁ)) ≫ (α_ _ _ _).hom ≫ (𝟙 (Xᘁ) ⊗ ev X) ≫ (ρ_ (Xᘁ)).hom = 𝟙 (Xᘁ) :=
(classical.arbitrary (dual_data X)).zigzag₂

variables (C)

def dual_tensor_unit_iso [has_dual (𝟙_ C)] : (𝟙_ C)ᘁ ≅ 𝟙_ C :=
dual_data.ext _ (dual_data.tensor_unit C)

variables {C}

def dual_tensor_obj_iso (X Y : C) [has_dual X] [has_dual Y] [has_dual (X ⊗ Y)] :
  (X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ :=
dual_data.ext _ (dual_data.tensor_obj _ _)

variables (C)

open category

/-- We verify that if every object has a dual,
these choices can be assembled into a monoidal functor (in fact, it's an equivalence)
from `C` to `(Cᵒᵖ)ᵐᵒᵖ`. -/
def duality_functor [∀ X : C, has_dual X] : monoidal_functor C (Cᵒᵖ)ᵐᵒᵖ :=
{ obj := λ X, mop (op (Xᘁ)),
  map := λ X Y f,
    ((λ_ _).inv ≫ (coev X ⊗ 𝟙 _) ≫ ((𝟙 _ ⊗ f) ⊗ 𝟙 _) ≫ (α_ _ _ _).hom ≫
       (𝟙 _ ⊗ ev Y) ≫ (ρ_ _).hom).op.mop,
  ε := (dual_tensor_unit_iso C).op.mop.hom,
  μ := λ X Y, (dual_tensor_obj_iso X Y).op.mop.hom,
  map_id' := λ X,
  begin
    simp only [tensor_id, id_comp, dual_zigzag₂],
    refl,
  end,
  map_comp' := λ X Y Z f g,
  begin
    simp only [←mop_comp, ←op_comp],
    sorry,
  end, }

/-- A monoidal category is rigid if every object admits both right and left duals. -/
class rigid :=
(right_duals : ∀ X : C, has_dual X)
(left_duals : ∀ X : C, ∃ Y : C, nonempty (X ≅ Yᘁ))

end category_theory
