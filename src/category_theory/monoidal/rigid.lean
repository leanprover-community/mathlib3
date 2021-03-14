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

structure dual_data (X : C) :=
(dual : C)
(ev : X ⊗ dual ⟶ 𝟙_ C)
(coev : 𝟙_ C ⟶ dual ⊗ X)
(zigzag₁ : (ρ_ X).inv ≫ (𝟙 X ⊗ coev) ≫ (α_ _ _ _).inv ≫ (ev ⊗ 𝟙 X) ≫ (λ_ X).hom = 𝟙 X)
(zigzag₂ : (λ_ dual).inv ≫ (coev ⊗ 𝟙 dual) ≫ (α_ _ _ _).hom ≫ (𝟙 dual ⊗ ev) ≫ (ρ_ dual).hom = 𝟙 dual)

def has_dual (X : C) : Prop := nonempty (dual_data X)
attribute [class] has_dual

instance nonempty_dual_data_of_has_dual (X : C) [I : has_dual X] : nonempty (dual_data X) := I

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

open category

def duality [∀ X : C, has_dual X] : monoidal_functor C (Cᵒᵖ)ᵐᵒᵖ :=
{ obj := λ X, mop (op (Xᘁ)),
  map := λ X Y f,
    ((λ_ _).inv ≫ (coev X ⊗ 𝟙 _) ≫ ((𝟙 _ ⊗ f) ⊗ 𝟙 _) ≫ (α_ _ _ _).hom ≫ (𝟙 _ ⊗ ev Y) ≫ (ρ_ _).hom).op.mop,
  ε := begin dsimp, sorry, end,
  μ := sorry,
  map_id' := λ X,
  begin
    simp only [tensor_id, id_comp, dual_zigzag₂],
    refl,
  end,
  map_comp' := λ X Y Z f g,
  begin
    simp only [←mop_comp, ←op_comp],
    sorry,
  end,
  ε_is_iso := sorry,
  μ_is_iso := sorry, }


end category_theory
