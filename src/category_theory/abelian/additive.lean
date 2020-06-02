/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.biproducts
import category_theory.preadditive
import category_theory.simple

open category_theory
open category_theory.preadditive
open category_theory.limits

universes v u

namespace category_theory

variables {C : Type u} [category.{v} C]
variables [preadditive.{v} C] [has_binary_biproducts.{v} C]

/--
If
```
(f 0)
(0 g)
```
is invertible, then `f` is invertible.
-/
def is_iso_left_of_is_iso_biprod_map {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [is_iso (biprod.map f g)] : is_iso f :=
begin
  fsplit,
  exact biprod.inl ≫ inv (biprod.map f g) ≫ biprod.fst,
  have := is_iso.hom_inv_id (biprod.map f g),
  have := congr_arg (λ p : W ⊞ X ⟶ W ⊞ X, biprod.inl ≫ p ≫ biprod.fst) this,
  simp only [category.id_comp, category.assoc] at this,
  dsimp,
  sorry,
end

def is_iso_right_of_is_iso_biprod_map {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [is_iso (biprod.map f g)] : is_iso g :=
sorry

def biprod.of_components {X₁ X₂ Y₁ Y₂ : C} (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂) :
  X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂ := sorry

lemma biprod.of_components_comp {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C}
  (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂)
  (g₁₁ : Y₁ ⟶ Z₁) (g₁₂ : Y₁ ⟶ Z₂) (g₂₁ : Y₂ ⟶ Z₁) (g₂₂ : Y₂ ⟶ Z₂) :
  biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂ ≫ biprod.of_components g₁₁ g₁₂ g₂₁ g₂₂ =
    biprod.of_components (f₁₁ ≫ g₁₁ + f₁₂ ≫ g₂₁) (f₁₁ ≫ g₁₂ + f₁₂ ≫ g₂₂) (f₂₁ ≫ g₁₁ + f₂₂ ≫ g₂₁) (f₂₁ ≫ g₁₂ + f₂₂ ≫ g₂₂) :=
sorry

/--
If `X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂` via a two-by-two matrix whose `X₁ ⟶ Y₁` entry is an isomorphism,
then we can construct an isomorphism `X₂ ≅ Y₂`, via Gaussian elimination.
-/
def foo {X₁ X₂ Y₁ Y₂ : C} (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂)
  [is_iso f₁₁] [is_iso (biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂)] : X₂ ≅ Y₂ :=
begin
  -- We use Gaussian elimination to show that the matrix `f` is equivalent to a diagonal matrix,
  -- which then must be an isomorphism.
  let f := biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂,
  let a : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂ := sorry,
  let b : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂ := sorry,
  let r : X₂ ⟶ Y₂ := sorry,
  let d : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂ := biprod.map f₁₁ r,
  have w : a.hom ≫ f ≫ b.hom = d := sorry,
  haveI : is_iso d := by {rw ←w, apply_instance, },
  haveI : is_iso r := (is_iso_right_of_is_iso_biprod_map f₁₁ r),
  exact as_iso r
end

section
variables (C)
structure simples :=
(ι : Type*)
[fintype : fintype ι]
(f : ι → C)
(simple : Π i, simple.{v} (f i))
end

def simples.sum (S : simples.{v} C) : C := sorry

def bar {S T : simples.{v} C} (f : S.sum ≅ T.sum) : S.ι ≃ T.ι := sorry
def bar' {S T : simples.{v} C} (f : S.sum ≅ T.sum) (i : S.ι) : S.f i ≅ T.f (bar f i) := sorry

end category_theory
