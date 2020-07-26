import category_theory.monoidal.internal
import category_theory.monoidal.types

universes v u

open category_theory
open category_theory.monoidal

variables (C : Type u) [category.{v} C] [monoidal_category.{v} C]

namespace Mon_Type_equivalent_Mon

def functor : Mon_ (Type u) ⥤ Mon.{u} :=
{ obj := λ A, ⟨A.X,
  { one := as_term A.ι,
    mul := λ x y, A.μ (tmul x y),
    one_mul := λ x,
    begin dsimp [(*)], convert congr_fun A.ι_μ x, sorry, end,
    mul_one := λ x,
    begin dsimp [(*)], convert congr_fun A.μ_ι x, sorry, end,
    mul_assoc := λ x y z,
    begin dsimp [(*)], convert congr_fun A.μ_assoc (tmul x (tmul y z)), sorry, sorry, end, }⟩,
  map := sorry, }

end Mon_Type_equivalent_Mon


def Mon_Type_equivalent_Mon : Mon_ (Type u) ≌ Mon.{u} :=
sorry
