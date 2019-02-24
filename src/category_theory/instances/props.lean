import category_theory.category

namespace category_theory

universe u

def props : category Prop :=
{ hom  := λ X Y, X → Y,
  id   := λ X, id,
  comp := λ X Y Z f g, g ∘ f }

end category_theory
