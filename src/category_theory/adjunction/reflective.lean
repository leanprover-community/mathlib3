/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.preserves.shapes.binary_products
import category_theory.adjunction.fully_faithful

universes v₁ v₂ u₁ u₂

noncomputable theory

namespace category_theory

open limits category

variables {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₂} D]

/--
A functor is *reflective*, or *a reflective inclusion*, if it is fully faithful and right adjoint.
-/
class reflective (R : D ⥤ C) extends is_right_adjoint R, full R, faithful R.

end category_theory
