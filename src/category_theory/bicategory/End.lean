import category_theory.bicategory.basic
import category_theory.monoidal.category

namespace category_theory

variables {C : Type*} [bicategory C]

@[derive category]
def End_monoidal (X : C) := X ⟶ X

open_locale bicategory

instance (X : C) : monoidal_category (End_monoidal X) :=
{ tensor_obj := λ X Y, X ≫ Y,
  tensor_hom := λ W X Y Z f g, (f ▷ Y) ≫ (X ◁ g),
  tensor_unit := 𝟙 _,
  associator := λ X Y Z, α_ X Y Z,
  left_unitor := λ X, λ_ X,
  right_unitor := λ X, ρ_ X,
  associator_naturality' := sorry,
  left_unitor_naturality' := sorry,
  right_unitor_naturality' := sorry,
  pentagon' := sorry, }

end category_theory
