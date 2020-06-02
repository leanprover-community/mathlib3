import category_theory.limits.shapes.biproducts

universes v u

open category_theory
open category_theory.limits

variables {C : Type u} [category.{v} C] [preadditive.{v} C]

lemma biprod.inl_map [has_preadditive_binary_biproducts.{v} C] {W X Y Z : C} {f : W ⟶ Y} {g : X ⟶ Z} :
  biprod.inl ≫ biprod.map f g = f ≫ biprod.inl := sorry
