import category_theory.monoidal.internal
import category_theory.monoidal.types

universes v u

open category_theory
open category_theory.monoidal

variables (C : Type u) [category.{v} C] [monoidal_category.{v} C]

namespace Mon_Type_equivalent_Mon

def functor : Mon_ (Type u) ⥤ Mon.{u} :=
{ obj := λ A, ⟨A.X,
  { one := A.one punit.star,
    mul := λ x y, A.mul (x, y),
    one_mul := λ x, by convert congr_fun A.one_mul (punit.star, x),
    mul_one := λ x, by convert congr_fun A.mul_one (x, punit.star),
    mul_assoc := λ x y z, by convert congr_fun A.mul_assoc ((x, y), z), }⟩,
  map := sorry, }.

def inverse : Mon.{u} ⥤ Mon_ (Type u) :=
{ obj := λ A,
  { X := A,
    one := λ _, 1,
    mul := λ p, p.1 * p.2,
    mul_assoc' := by { ext ⟨⟨x, y⟩, z⟩, simp [mul_assoc], }, },
  map := λ A B f,
  { hom := f, }, }.

end Mon_Type_equivalent_Mon


def Mon_Type_equivalent_Mon : Mon_ (Type u) ≌ Mon.{u} :=
sorry
