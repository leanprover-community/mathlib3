import category_theory.monoidal.opposite
import category_theory.monoidal.functor

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

postfix `ᘁ`:70 := dual -- From https://en.wikipedia.org/wiki/Unified_Canadian_Aboriginal_Syllabics_(Unicode_block)

def ev (X : C) [has_dual X] : X ⊗ Xᘁ ⟶ 𝟙_ C := (classical.arbitrary (dual_data X)).ev
def coev (X : C) [has_dual X] : 𝟙_ C ⟶ Xᘁ ⊗ X := (classical.arbitrary (dual_data X)).coev

def duality [∀ X : C, has_dual X] : monoidal_functor C (Cᵒᵖ)ᵐᵒᵖ :=
{ obj := λ X, mop (op (Xᘁ)),
  map := λ X Y f, ((λ_ _).inv ≫ (coev X ⊗ 𝟙 _) ≫ ((𝟙 _ ⊗ f) ⊗ 𝟙 _) ≫ (α_ _ _ _).hom ≫ (𝟙 _ ⊗ ev Y) ≫ (ρ_ _).hom).op.mop,
 }


end category_theory
