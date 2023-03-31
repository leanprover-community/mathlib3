/-
Copyright (c) 2018 Reid Barton All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Scott Morrison, David Wärn
-/
import category_theory.full_subcategory
import category_theory.products.basic
import category_theory.pi.basic
import category_theory.category.basic
import combinatorics.quiver.connected_component

/-!
# Groupoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define `groupoid` as a typeclass extending `category`,
asserting that all morphisms have inverses.

The instance `is_iso.of_groupoid (f : X ⟶ Y) : is_iso f` means that you can then write
`inv f` to access the inverse of any morphism `f`.

`groupoid.iso_equiv_hom : (X ≅ Y) ≃ (X ⟶ Y)` provides the equivalence between
isomorphisms and morphisms in a groupoid.

We provide a (non-instance) constructor `groupoid.of_is_iso` from an existing category
with `is_iso f` for every `f`.

## See also

See also `category_theory.core` for the groupoid of isomorphisms in a category.
-/

namespace category_theory

universes v v₂ u u₂ -- morphism levels before object levels. See note [category_theory universes].

/-- A `groupoid` is a category such that all morphisms are isomorphisms. -/
class groupoid (obj : Type u) extends category.{v} obj : Type (max u (v+1)) :=
(inv       : Π {X Y : obj}, (X ⟶ Y) → (Y ⟶ X))
(inv_comp' : ∀ {X Y : obj} (f : X ⟶ Y), comp (inv f) f = id Y . obviously)
(comp_inv' : ∀ {X Y : obj} (f : X ⟶ Y), comp f (inv f) = id X . obviously)

restate_axiom groupoid.inv_comp'
restate_axiom groupoid.comp_inv'

/--
A `large_groupoid` is a groupoid
where the objects live in `Type (u+1)` while the morphisms live in `Type u`.
-/
abbreviation large_groupoid (C : Type (u+1)) : Type (u+1) := groupoid.{u} C
/--
A `small_groupoid` is a groupoid
where the objects and morphisms live in the same universe.
-/
abbreviation small_groupoid (C : Type u) : Type (u+1) := groupoid.{u} C

section

variables {C : Type u} [groupoid.{v} C] {X Y : C}

@[priority 100] -- see Note [lower instance priority]
instance is_iso.of_groupoid (f : X ⟶ Y) : is_iso f :=
⟨⟨groupoid.inv f, groupoid.comp_inv f, groupoid.inv_comp f⟩⟩

@[simp] lemma groupoid.inv_eq_inv (f : X ⟶ Y) : groupoid.inv f = inv f :=
is_iso.eq_inv_of_hom_inv_id $ groupoid.comp_inv f

/-- `groupoid.inv` is involutive. -/
@[simps] def groupoid.inv_equiv : (X ⟶ Y) ≃ (Y ⟶ X) :=
⟨groupoid.inv, groupoid.inv, λ f, by simp, λ f, by simp⟩

@[priority 100]
instance groupoid_has_involutive_reverse : quiver.has_involutive_reverse C :=
{ reverse' := λ X Y f, groupoid.inv f,
  inv' := λ X Y f, by { dsimp [quiver.reverse], simp, } }

@[simp] lemma groupoid.reverse_eq_inv (f : X ⟶ Y) : quiver.reverse f = groupoid.inv f := rfl

instance functor_map_reverse {D : Type*} [groupoid D] (F : C ⥤ D) :
  F.to_prefunctor.map_reverse :=
{ map_reverse' := λ X Y f, by
  simp only [quiver.reverse, quiver.has_reverse.reverse', groupoid.inv_eq_inv,
               functor.to_prefunctor_map, functor.map_inv], }

variables (X Y)

/-- In a groupoid, isomorphisms are equivalent to morphisms. -/
def groupoid.iso_equiv_hom : (X ≅ Y) ≃ (X ⟶ Y) :=
{ to_fun := iso.hom,
  inv_fun := λ f, ⟨f, groupoid.inv f⟩,
  left_inv := λ i, iso.ext rfl,
  right_inv := λ f, rfl }

variables (C)

/-- The functor from a groupoid `C` to its opposite sending every morphism to its inverse. -/
@[simps] noncomputable def groupoid.inv_functor : C ⥤ Cᵒᵖ :=
{ obj := opposite.op,
  map := λ {X Y} f, (inv f).op }

end

section

variables {C : Type u} [category.{v} C]

/-- A category where every morphism `is_iso` is a groupoid. -/
noncomputable
def groupoid.of_is_iso (all_is_iso : ∀ {X Y : C} (f : X ⟶ Y), is_iso f) : groupoid.{v} C :=
{ inv := λ X Y f, inv f }

/-- A category with a unique morphism between any two objects is a groupoid -/
def groupoid.of_hom_unique (all_unique : ∀ {X Y : C}, unique (X ⟶ Y)) : groupoid.{v} C :=
{ inv := λ X Y f, all_unique.default }

end

instance induced_category.groupoid {C : Type u} (D : Type u₂) [groupoid.{v} D] (F : C → D) :
   groupoid.{v} (induced_category D F) :=
{ inv       := λ X Y f, groupoid.inv f,
  inv_comp' := λ X Y f, groupoid.inv_comp f,
  comp_inv' := λ X Y f, groupoid.comp_inv f,
  .. induced_category.category F }

section

instance groupoid_pi {I : Type u} {J : I → Type u₂} [∀ i, groupoid.{v} (J i)] :
  groupoid.{max u v} (Π i : I, J i) :=
{ inv := λ (x y : Π i, J i) (f : Π i, x i ⟶ y i), (λ i : I, groupoid.inv (f i)), }

instance groupoid_prod {α : Type u} {β : Type v} [groupoid.{u₂} α] [groupoid.{v₂} β] :
  groupoid.{max u₂ v₂} (α × β) :=
{ inv := λ (x y : α × β) (f : x ⟶ y), (groupoid.inv f.1, groupoid.inv f.2) }

end

end category_theory
