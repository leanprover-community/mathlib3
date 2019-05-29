import category_theory.canonical_isomorphism
import category_theory.monoidal.category

universes v₁ u₁

open category_theory
open category_theory.monoidal_category

namespace category_theory

variables {C : Type u₁} [𝒞 : monoidal_category.{v₁} C]
include 𝒞

local notation `𝟙_` := tensor_unit
local notation `α_` := associator
local notation `λ_` := left_unitor
local notation `ρ_` := right_unitor

class is_tensor_product (X : C) (factors : list C) :=
(iso : X ≅ factors.foldl (⊗) (𝟙_ C))

namespace is_tensor_product

instance unit : is_tensor_product.{v₁} (𝟙_ C) [] :=
{ iso := iso.refl _ }

instance singleton (X : C) : is_tensor_product.{v₁} X [X] :=
{ iso := (λ_ X).symm }

instance product_1 (X Y : C) (factorsY : list C)
  [is_tensor_product.{v₁} Y factorsY] :
  is_tensor_product.{v₁} (X ⊗ Y) (X :: factorsY) :=
{ iso := sorry }
instance product_2 (X Y Z : C) (factorsZ : list C)
  [is_tensor_product.{v₁} Z factorsZ] :
  is_tensor_product.{v₁} ((X ⊗ Y) ⊗ Z) (X :: Y :: factorsZ) :=
{ iso := sorry }
instance product_3 (W X Y Z : C) (factorsZ : list C)
  [is_tensor_product.{v₁} Z factorsZ] :
  is_tensor_product.{v₁} (((W ⊗ X) ⊗ Y) ⊗ Z) (W :: X :: Y :: factorsZ) :=
{ iso := sorry }

example (Y Z : C) : is_tensor_product.{v₁} (Y ⊗ Z) [Y, Z] := is_tensor_product.product_1 Y Z [Z]
example (Y Z : C) : is_tensor_product.{v₁} (Y ⊗ Z) [Y, Z] := by apply_instance
example (X Y Z : C) : is_tensor_product.{v₁} (X ⊗ (Y ⊗ Z)) [X, Y, Z] := by apply_instance
example (X Y Z : C) : is_tensor_product.{v₁} ((X ⊗ Y) ⊗ Z) [X, Y, Z] := by apply_instance

instance (X Y : C) (factors : list C) [is_tensor_product.{v₁} X factors] [is_tensor_product.{v₁} Y factors] :
  canonically_isomorphic.{v₁} X Y :=
{ iso := (is_tensor_product.iso.{v₁} X factors) ≪≫ (is_tensor_product.iso.{v₁} Y factors).symm }

example (X Y Z : C) : canonically_isomorphic.{v₁} (X ⊗ (Y ⊗ Z)) ((X ⊗ Y) ⊗ Z) := by apply_instance
example (W X Y Z : C) : canonically_isomorphic.{v₁} (W ⊗ (X ⊗ (Y ⊗ Z))) (((W ⊗ X) ⊗ Y) ⊗ Z) := by apply_instance

example {A B X Y Z : C} (f : A ⟶ X ⊗ (Y ⊗ Z)) (g : (X ⊗ Y) ⊗ Z ⟶ B) : A ⟶ B := f ≫≅ g

end is_tensor_product

end category_theory
