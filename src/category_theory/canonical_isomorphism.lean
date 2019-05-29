import category_theory.isomorphism

universes v₁ u₁

open category_theory

variables {C : Sort u₁} [𝒞 : category.{v₁} C]
include 𝒞

class canonically_isomorphic (X Y : C) :=
(iso : X ≅ Y)

namespace canonically_isomorphic

instance refl (X : C) : canonically_isomorphic.{v₁} X X :=
{ iso := iso.refl.{v₁} X }

def equal_up_to_canonical_isomorphism {X Y X' Y' : C}
  [canonically_isomorphic.{v₁} X X'] [canonically_isomorphic.{v₁} Y Y'] (f : X ⟶ Y) (g : X' ⟶ Y') :=
f ≫ (canonically_isomorphic.iso.{v₁} Y Y').hom = (canonically_isomorphic.iso.{v₁} X X').hom ≫ g

infixr ` =≅ `:70 := equal_up_to_canonical_isomorphism

def compose_up_to_canonical_isomorphism {X Y Y' Z : C} [canonically_isomorphic.{v₁} Y Y']
  (f : X ⟶ Y) (g : Y' ⟶ Z) : X ⟶ Z :=
f ≫ (canonically_isomorphic.iso.{v₁} Y Y').hom ≫ g

infixr ` ≫≅ `:70 := compose_up_to_canonical_isomorphism

end canonically_isomorphic
