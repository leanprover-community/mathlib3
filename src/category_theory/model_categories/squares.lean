import category_theory.category
import category_theory.arrow
import category_theory.model_categories.lifting_properties

namespace category_theory

universes v₁ u₁
variables {C : Type u₁} [category.{v₁} C]

variables {A B X Y Z : C}


/-- Given two composable morphisms, construct a square
X  = X
↓i   ↓ i ≫ p
A →p Y
-/
def square_from_composable_left_id {X A Y : C} (i : X ⟶ A) (p : A ⟶ Y) : arrow.mk i ⟶ arrow.mk (i ≫ p) :=
{ left := 𝟙 X,
  right := p }

/-- Given two composable morphisms, construct a square
X  →i A
↓i≫p ↓p
Y  =  Y
-/
def square_from_composable_right_id {X A Y : C} (i : X ⟶ A) (p : A ⟶ Y) : arrow.mk (i ≫ p) ⟶ arrow.mk p :=
{ left := i,
  right := 𝟙 Y }

end category_theory
