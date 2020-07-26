import algebra.category.Mon.monoidal
import category_theory.monoidal.internal

open category_theory
open category_theory.monoidal

namespace Mon_Mon_equivalence_CommMon

def functor : Mon_ Mon ⥤ CommMon :=
{ obj := λ A, ⟨ A.X,
  { one := A.one 1,
    mul := λ x y, A.mul (x, y), -- (x, y) has type ↥(A.X) × ↥(A.X) but is expected to have type ↥(A.X ⊗ A.X)
    one_mul := sorry,
    mul_one := sorry,
    mul_assoc := sorry,
    mul_comm := sorry, }⟩,
  map := λ A B f,
  { to_fun := f.hom,
    map_one' := f.hom.map_one, -- type mismatch at field 'map_one'' ... f.hom has type @eq (@coe_sort
    map_mul' := sorry, }, }.

end Mon_Mon_equivalence_CommMon
