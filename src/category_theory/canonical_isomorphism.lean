import category_theory.groupoid
import category_theory.eq_to_hom

universes v₁ u₁

open category_theory

variables {C : Sort u₁} [𝒞 : category.{v₁} C]
include 𝒞
variables {J : Sort u₁} [𝒥 : groupoid.{v₁} J] [∀ X Y : J, subsingleton (X ⟶ Y)]
include 𝒥

class canonically_isomorphic (F : J ⥤ C) (X₁ X₂ : C) :=
(j₁ j₂ : J)
(f : j₁ ⟶ j₂)
(h₁ : F.obj j₁ = X₁ . obviously)
(h₂ : F.obj j₂ = X₂ . obviously)

namespace canonically_isomorphic

variables (F : J ⥤ C)

def iso (X Y : C) [i : canonically_isomorphic F X Y] : X ≅ Y :=
eq_to_iso (canonically_isomorphic.h₁ F X Y).symm
  ≪≫ F.map_iso (as_iso (canonically_isomorphic.f F X Y))
  ≪≫ eq_to_iso (canonically_isomorphic.h₂ F X Y)

-- err... assume F is surjective on objects?
instance refl (j : J) : canonically_isomorphic F (F.obj j) (F.obj j) :=
{ j₁ := j,
  j₂ := j,
  f := 𝟙 _, }

instance symm (X Y : C) [i : canonically_isomorphic F X Y] : canonically_isomorphic F Y X :=
{ j₁ := i.j₂,
  j₂ := i.j₁,
  f := inv i.f,
  h₁ := i.h₂,
  h₂ := i.h₁ }

def equal_up_to_canonical_isomorphism {X Y X' Y' : C}
  [canonically_isomorphic.{v₁} F X X'] [canonically_isomorphic.{v₁} F Y Y'] (f : X ⟶ Y) (g : X' ⟶ Y') :=
f ≫ (canonically_isomorphic.iso.{v₁} F Y Y').hom = (canonically_isomorphic.iso.{v₁} F X X').hom ≫ g

infixr ` =≅ `:70 := equal_up_to_canonical_isomorphism

def compose_up_to_canonical_isomorphism {X Y Y' Z : C} [canonically_isomorphic.{v₁} F Y Y']
  (f : X ⟶ Y) (g : Y' ⟶ Z) : X ⟶ Z :=
f ≫ (canonically_isomorphic.iso.{v₁} F Y Y').hom ≫ g

infixr ` ≫≅ `:70 := compose_up_to_canonical_isomorphism

end canonically_isomorphic
