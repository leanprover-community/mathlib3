/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Yury Kudryashov
-/
import logic.rel.lemmas category_theory.opposites category_theory.concrete_category.unbundled_hom

/-!
# Several categories with relations as morphisms or objects.

This file defines the following categories:

* `Rel` : a type synonym for `Type`; uses binary relations as morphisms;
* `HeteroBRel` : bundled relations, heterogeneous version; an object is a pair of types
  with a bundled binary relation, and a morphism between two objects is a pair of functions
  related by `X.r ⇒ Y.r`;
* `BRel` : bundled homogeneous relations; an object is a type `α` with a bundled
  binary relation `rel α α`; a morphism between two objects is a function that sends related
  pairs to related pairs.
-/

namespace category_theory

universes u v

/-- A type synonym for `Type`, which carries the category instance for which
    morphisms are binary relations. -/
def Rel := Type u

namespace Rel

/-- The category of types with binary relations as morphisms. -/
instance category : large_category Rel.{u} :=
{ hom := rel,
  comp := λ X Y Z r₁ r₂, r₂.comp r₁,
  id := @eq,
  comp_id' := @rel.id_comp,
  id_comp' := @rel.comp_id,
  assoc' := λ _ _ _ _ r₁ r₂ r₃, (rel.comp_assoc r₃ r₂ r₁).symm }

/-- The functor that sends each `α` to `set α`, and `r` to `r.image : set α → set β`. -/
def image : Rel ⥤ Type u :=
{ obj := set,
  map := @rel.image,
  map_id' := λ _, funext rel.image_id,
  map_comp' := λ _ _ _ r₁ r₂, funext $ rel.image_comp r₂ r₁ }

instance image_faithful : faithful image :=
{ injectivity' := λ X Y r r' h, rel.ext $ λ x y,
  calc r x y ↔ y ∈ r.image {x}  : by simp only [r.image_singleton x, set.mem_set_of_eq]
         ... ↔ y ∈ r'.image {x} : by rw h
         ... ↔ r' x y           : by simp only [r'.image_singleton x, set.mem_set_of_eq] }

open opposite (op unop)

/-- The contravariant functor that sends each relation to its converse. -/
protected def flip : Relᵒᵖ ⥤ Rel :=
{ obj := λ X, unop X,
  map := λ X Y r, r.unop.flip,
  map_id' := λ X, rel.flip_id,
  map_comp' := λ _ _ _ _ _, rel.flip_comp _ _ }

instance flip_faithful : faithful Rel.flip :=
{ injectivity' := λ X Y r r' h, has_hom.hom.unop_inj $ rel.flip_inj h }

instance flip_full : full Rel.flip := { preimage := _ }

/-- The contravariant functor that sends each `α` to `set α`, and `r`
to `r.preimage : set α → set β`. -/
def preimage : Relᵒᵖ ⥤ Type u :=
{ obj := λ X, set (unop X),
  map := λ X Y r, rel.preimage r.unop,
  map_id' := λ X, funext rel.preimage_id,
  map_comp' := λ _ _ _ _ _, funext $ rel.preimage_comp _ _ }

/- This is an example, because rewriting on functor equalities is usually a bad idea. -/
example : Rel.flip ⋙ image = preimage := rfl

instance preimage_faithful : faithful preimage := faithful.comp Rel.flip image

end Rel

/-- The graph of a function as a faithful functor from `Type` to `Rel`. -/
def function_to_rel : Type u ⥤ Rel.{u} :=
{ obj := id,
  map := @function.to_rel,
  map_id' := @function.to_rel_id,
  map_comp' := λ X Y Z f g, function.to_rel_comp g f }

instance function_to_rel_faithful : faithful function_to_rel :=
⟨@function.to_rel_inj⟩

/-- The category of pairs of `Type`s with bundled relations. -/
structure HeteroBRel :=
{α : Type u}
{β : Type v}
(r : rel α β)

structure HeteroBRel_hom (X Y : HeteroBRel) :=
(f : X.α → Y.α)
(g : X.β → Y.β)
(h : (X.r ⇒ Y.r) f g)

instance HeteroBRel.category : large_category HeteroBRel.{u v} :=
{ hom := HeteroBRel_hom,
  id := λ X, ⟨_, _, rel.rel_id X.r⟩,
  comp := λ X Y Z XY YZ, ⟨_, _, rel.rel_comp YZ.h XY.h⟩,
  id_comp' := by rintros X Y ⟨f, g, h⟩; refl,
  comp_id' := by rintros X Y ⟨f, g, h⟩; refl,
  assoc' := by intros; refl }

/-- The category of bundled homogeneous relations. Several other concrete categories
(order structures, setoids etc) can be induced from this one. -/
@[reducible] def BRel := bundled (λ α, rel α α)

namespace BRel

instance rel.lift_fun.unbundled_hom :
  unbundled_hom (λ α β (ra : rel α α) (rb : rel β β), (ra ⇒ rb).diag) :=
{ hom_id := λ α, rel.rel_id,
  hom_comp := λ α β γ ra rb rc g f hg hf, rel.rel_comp hg hf }

/-- The functor that forgets that a relation is homogeneous. -/
def to_HeteroBRel : BRel ⥤ HeteroBRel :=
{ obj := λ X, ⟨X.str⟩,
  map := λ X Y F, ⟨_, _, F.property⟩ }

instance : faithful to_HeteroBRel := { }

end BRel

end category_theory
