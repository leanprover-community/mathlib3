import category_theory.monoidal.functor
import category_theory.skeletal

namespace category_theory
open monoidal_category

universes v u

variables {C : Type u} [category.{v} C] [monoidal_category C]

def monoid_of_skeletal_monoidal (hC : skeletal C) : monoid C :=
{ mul := λ X Y, (X ⊗ Y : C),
  one := (𝟙_ C : C),
  one_mul := λ X, hC ⟨λ_ X⟩,
  mul_one := λ X, hC ⟨ρ_ X⟩,
  mul_assoc := λ X Y Z, hC ⟨α_ X Y Z⟩ }

end category_theory
