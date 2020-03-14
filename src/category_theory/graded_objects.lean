import category_theory.category

namespace category_theory

universes v u

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

instance {β : Type u} : category (β → C) :=
{ hom := λ X Y, Π b : β, X b ⟶ Y b,
  id := λ X b, 𝟙 (X b),
  comp := λ X Y Z f g b, f b ≫ g b, }

end category_theory
