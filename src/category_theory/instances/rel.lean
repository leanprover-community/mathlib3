import category_theory.category

namespace category_theory

universe u

def rel : large_category (Type u) :=
{ hom  := λ X Y, X → Y → Prop,
  id   := λ X, λ x y, x = y,
  comp := λ X Y Z f g x z, ∃ y, f x y ∧ g y z }

end category_theory
