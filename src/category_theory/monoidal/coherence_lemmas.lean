/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison, Bhavik Mehta, Jakob von Raumer
-/
import category_theory.monoidal.coherence

/-!
# Lemmas which are consequences of monoidal coherence

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

These lemmas are all proved `by coherence`.

## Future work
Investigate whether these lemmas are really needed,
or if they can be replaced by use of the `coherence` tactic.
-/

open category_theory
open category_theory.category
open category_theory.iso

namespace category_theory.monoidal_category

variables {C : Type*} [category C] [monoidal_category C]

-- See Proposition 2.2.4 of <http://www-math.mit.edu/~etingof/egnobookfinal.pdf>
@[reassoc]
lemma left_unitor_tensor' (X Y : C) :
  ((α_ (𝟙_ C) X Y).hom) ≫ ((λ_ (X ⊗ Y)).hom) = ((λ_ X).hom ⊗ (𝟙 Y)) :=
by coherence

@[reassoc, simp]
lemma left_unitor_tensor (X Y : C) :
  ((λ_ (X ⊗ Y)).hom) = ((α_ (𝟙_ C) X Y).inv) ≫ ((λ_ X).hom ⊗ (𝟙 Y)) :=
by coherence

@[reassoc]
lemma left_unitor_tensor_inv (X Y : C) :
  (λ_ (X ⊗ Y)).inv = ((λ_ X).inv ⊗ (𝟙 Y)) ≫ (α_ (𝟙_ C) X Y).hom :=
by coherence

@[reassoc]
lemma id_tensor_right_unitor_inv (X Y : C) : 𝟙 X ⊗ (ρ_ Y).inv = (ρ_ _).inv ≫ (α_ _ _ _).hom :=
by coherence

@[reassoc]
lemma left_unitor_inv_tensor_id (X Y : C) : (λ_ X).inv ⊗ 𝟙 Y = (λ_ _).inv ≫ (α_ _ _ _).inv :=
by coherence

@[reassoc]
lemma pentagon_inv_inv_hom (W X Y Z : C) :
  (α_ W (X ⊗ Y) Z).inv ≫ ((α_ W X Y).inv ⊗ (𝟙 Z)) ≫ (α_ (W ⊗ X) Y Z).hom
  = ((𝟙 W) ⊗ (α_ X Y Z).hom) ≫ (α_ W X (Y ⊗ Z)).inv :=
by coherence

@[simp, reassoc] lemma triangle_assoc_comp_right_inv (X Y : C) :
  ((ρ_ X).inv ⊗ 𝟙 Y) ≫ (α_ X (𝟙_ C) Y).hom = ((𝟙 X) ⊗ (λ_ Y).inv) :=
by coherence

lemma unitors_equal : (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom :=
by coherence

lemma unitors_inv_equal : (λ_ (𝟙_ C)).inv = (ρ_ (𝟙_ C)).inv :=
by coherence

@[reassoc]
lemma pentagon_hom_inv {W X Y Z : C} :
  (α_ W X (Y ⊗ Z)).hom ≫ (𝟙 W ⊗ (α_ X Y Z).inv)
  = (α_ (W ⊗ X) Y Z).inv ≫ ((α_ W X Y).hom ⊗ 𝟙 Z) ≫ (α_ W (X ⊗ Y) Z).hom :=
by coherence

@[reassoc]
lemma pentagon_inv_hom (W X Y Z : C) :
  (α_ (W ⊗ X) Y Z).inv ≫ ((α_ W X Y).hom ⊗ 𝟙 Z)
  = (α_ W X (Y ⊗ Z)).hom ≫ (𝟙 W ⊗ (α_ X Y Z).inv) ≫ (α_ W (X ⊗ Y) Z).inv :=
by coherence

end category_theory.monoidal_category
