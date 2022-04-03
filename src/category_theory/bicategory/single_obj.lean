import category_theory.bicategory.End
import category_theory.monoidal.functorial

namespace category_theory

variables (C : Type*) [category C] [monoidal_category C]

/--
Promote a monoidal category to a bicategory with a single object.
(The objects of the monoidal category become the 1-morphisms,
with composition given by tensor product,
and the morphisms of the monoidal category become the 2-morphisms.)
-/
def monoidal_single_obj (C : Type*) := punit

instance : bicategory (monoidal_single_obj C) :=
{ hom := λ _ _, C,
  id := λ _, 𝟙_ C,
  comp := λ _ _ _ X Y, X ⊗ Y,
  whisker_left := λ _ _ _ X Y Z f, 𝟙 X ⊗ f,
  whisker_right := λ _ _ _ X Y f Z, f ⊗ 𝟙 Z,
  associator := λ _ _ _ _ X Y Z, α_ X Y Z,
  left_unitor := λ _ _ X, λ_ X,
  right_unitor := λ _ _ X, ρ_ X,
  associator_naturality_left' := sorry,
  associator_naturality_middle' := sorry,
  associator_naturality_right' := sorry,
  left_unitor_naturality' := sorry,
  right_unitor_naturality' := sorry,
  pentagon' := sorry, }

namespace monoidal_single_obj

protected def star : monoidal_single_obj C := punit.star

def End_monoidal_star_functor : monoidal_functor (End_monoidal (monoidal_single_obj.star C)) C :=
sorry

def End_monoidal_star_functor_is_equivalence :
  is_equivalence (End_monoidal_star_functor C).to_functor :=
sorry

end monoidal_single_obj

end category_theory
