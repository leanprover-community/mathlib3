/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.zero

/-!
# Shift

A `shift` on a category is nothing more than an automorphism of the category. An example to
keep in mind might be the category of complexes ⋯ → C_{n-1} → C_n → C_{n+1} → ⋯ with the shift
operator re-indexing the terms, so the degree `n` term of `shift C` would be the degree `n+1`
term of `C`.

-/
namespace category_theory

universes v u

variables (C : Type u) [category.{v} C]

/-- A category has a shift, or translation, if it is equipped with an automorphism. -/
class has_shift :=
(shift : C ≌ C)

variables [has_shift C]

/-- The shift autoequivalence, moving objects and morphisms 'up'. -/
def shift : C ≌ C := has_shift.shift

-- Any better notational suggestions?
notation X`⟦`n`⟧`:20 := ((shift _)^(n : ℤ)).functor.obj X
notation f`⟦`n`⟧'`:80 := ((shift _)^(n : ℤ)).functor.map f

example {X Y : C} (f : X ⟶ Y) : X⟦1⟧ ⟶ Y⟦1⟧ := f⟦1⟧'
example {X Y : C} (f : X ⟶ Y) : X⟦-2⟧ ⟶ Y⟦-2⟧ := f⟦-2⟧'

open category_theory.limits
variables [has_zero_morphisms C]

@[simp]
lemma shift_zero_eq_zero (X Y : C) (n : ℤ) : (0 : X ⟶ Y)⟦n⟧' = (0 : X⟦n⟧ ⟶ Y⟦n⟧) :=
by apply equivalence_preserves_zero_morphisms

end category_theory
