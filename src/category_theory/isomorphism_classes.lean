/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import category_theory.category.Cat
import category_theory.groupoid

/-!
# Objects of a category up to an isomorphism

`is_isomorphic X Y := nonempty (X ≅ Y)` is an equivalence relation on the objects of a category.
The quotient with respect to this relation defines a functor from our category to `Type`.
-/

universes v u

namespace category_theory

section category

variables {C : Type u} [category.{v} C]

/-- An object `X` is isomorphic to an object `Y`, if `X ≅ Y` is not empty. -/
def is_isomorphic : C → C → Prop := λ X Y, nonempty (X ≅ Y)

variable (C)

/-- `is_isomorphic` defines a setoid. -/
def is_isomorphic_setoid : setoid C :=
{ r := is_isomorphic,
  iseqv := ⟨λ X, ⟨iso.refl X⟩, λ X Y ⟨α⟩, ⟨α.symm⟩, λ X Y Z ⟨α⟩ ⟨β⟩, ⟨α.trans β⟩⟩ }

end category

/--
The functor that sends each category to the quotient space of its objects up to an isomorphism.
-/
def isomorphism_classes : Cat.{v u} ⥤ Type u :=
{ obj := λ C, quotient (is_isomorphic_setoid C.α),
  map := λ C D F, quot.map F.obj $ λ X Y ⟨f⟩, ⟨F.map_iso f⟩ }

lemma groupoid.is_isomorphic_iff_nonempty_hom {C : Type u} [groupoid.{v} C] {X Y : C} :
  is_isomorphic X Y ↔ nonempty (X ⟶ Y) :=
(groupoid.iso_equiv_hom X Y).nonempty_congr

-- PROJECT: define `skeletal`, and show every category is equivalent to a skeletal category,
-- using the axiom of choice to pick a representative of every isomorphism class.
end category_theory
