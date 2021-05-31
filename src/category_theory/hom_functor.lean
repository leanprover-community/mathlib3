/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Scott Morrison
-/
import category_theory.products.basic

/-!
The hom functor, sending `(X, Y)` to the type `X ⟶ Y`.
-/

universes v u

open opposite
open category_theory

namespace category_theory.functor

variables (C : Type u) [category.{v} C]

/-- `functor.hom` is the hom-pairing, sending `(X, Y)` to `X ⟶ Y`, contravariant in `X` and
covariant in `Y`. -/
definition hom : Cᵒᵖ × C ⥤ Type v :=
{ obj       := λ p, unop p.1 ⟶ p.2,
  map       := λ X Y f, λ h, f.1.unop ≫ h ≫ f.2 }

@[simp] lemma hom_obj (X : Cᵒᵖ × C) : (hom C).obj X = (unop X.1 ⟶ X.2) := rfl
@[simp] lemma hom_pairing_map {X Y : Cᵒᵖ × C} (f : X ⟶ Y) :
  (hom C).map f = λ h, f.1.unop ≫ h ≫ f.2 := rfl

end category_theory.functor
