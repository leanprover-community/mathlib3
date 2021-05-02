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

lemma is_isomorphic.refl (X : C) : is_isomorphic X X :=
⟨iso.refl X⟩

lemma is_isomorphic.symm {X Y : C} : is_isomorphic X Y → is_isomorphic Y X :=
λ ⟨α⟩, ⟨α.symm⟩

lemma is_isomorphic.trans {X Y Z : C} :
  is_isomorphic X Y → is_isomorphic Y Z → is_isomorphic X Z :=
λ ⟨α⟩ ⟨β⟩, ⟨α ≪≫ β⟩

variable (C)
open is_isomorphic

/-- `is_isomorphic` defines a setoid. -/
def is_isomorphic_setoid : setoid C :=
{ r := is_isomorphic,
  iseqv := ⟨refl, λ X Y, symm, λ X Y Z, trans⟩ }

end category

/--
The functor that sends each category to the quotient space of its objects up to an isomorphism.
-/
def isomorphism_classes : Cat.{v u} ⥤ Type u :=
{ obj := λ C, quotient (is_isomorphic_setoid C.α),
  map := λ C D F, quot.map F.obj $ λ X Y ⟨f⟩, ⟨F.map_iso f⟩ }

lemma groupoid.is_isomorphic_iff_nonempty_hom {C : Type u} [groupoid.{v} C] {X Y : C} :
  is_isomorphic X Y ↔ nonempty (X ⟶ Y) :=
(groupoid.iso_equiv_hom X Y).nonempty_iff_nonempty

-- PROJECT: define `skeletal`, and show every category is equivalent to a skeletal category,
-- using the axiom of choice to pick a representative of every isomorphism class.
end category_theory
