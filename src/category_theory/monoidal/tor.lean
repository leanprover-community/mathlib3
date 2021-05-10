/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.derived
import category_theory.monoidal.preadditive

/-!
# Tor, the left-derived functor of tensor product

We define `Tor C n : C ⥤ C ⥤ C`, by left-deriving in the second factor of `(X, Y) ↦ X ⊗ Y`.

For now we have almost nothing to say about it!
It would be good to show that this is naturally isomorphic to the functor obtained
by left-deriving in the first factor, instead.
-/

noncomputable theory

open category_theory.limits
open category_theory.monoidal_category

namespace category_theory

variables {C : Type*} [category C] [monoidal_category C] [preadditive C] [monoidal_preadditive C]
  [has_zero_object C] [has_equalizers C] [has_cokernels C] [has_images C] [has_image_maps C]
  [has_projective_resolutions C]

variables (C)

/-- We define `Tor C n : C ⥤ C ⥤ C` by left-deriving in the second factor of `(X, Y) ↦ X ⊗ Y`. -/
@[simps]
def Tor (n : ℕ) : C ⥤ C ⥤ C :=
{ obj := λ X, functor.left_derived ((tensoring_left C).obj X) n,
  map := λ X Y f, nat_trans.left_derived ((tensoring_left C).map f) n, }

/-- An alternative definition of `Tor`, where we left-derive in the first factor instead. -/
@[simps]
def Tor' (n : ℕ) : C ⥤ C ⥤ C :=
functor.flip
{ obj := λ X, functor.left_derived ((tensoring_right C).obj X) n,
  map := λ X Y f, nat_trans.left_derived ((tensoring_right C).map f) n, }

-- PROJECT showing `Tor C n ≅ Tor' C n` will require a bit more theory!
-- Possibly it's best to axiomatize delta functors, and obtain a unique characterisation?

end category_theory
