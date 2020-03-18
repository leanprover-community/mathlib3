import category_theory.equivalence
import category_theory.limits.shapes.zero

namespace category_theory

universes v u

variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

/-- A category has a shift, or translation, if it is equipped with an automorphism. -/
class has_shift :=
(shift : C ≌ C)

variables [has_shift.{v} C]

/-- The shift functor, moving objects and morphisms 'up'. -/
def shift : C ⥤ C := (has_shift.shift.{v} C).functor

-- Any better notational suggestions?
notation X`[1]`:20 := (shift _).obj X
notation f`[[1]]`:80 := (shift _).map f

example {X Y : C} (f : X ⟶ Y) : X[1] ⟶ Y[1] := f[[1]]

open category_theory.limits
variables [has_zero_morphisms.{v} C]

@[simp]
lemma shift_zero (X Y : C) : (0 : X ⟶ Y)[[1]] = (0 : X[1] ⟶ Y[1]) :=
by apply equivalence_preserves_zero_morphisms

end category_theory
