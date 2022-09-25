/-
Copyright (c) 2018 Reid Barton All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Scott Morrison, David Wärn
-/
import category_theory.full_subcategory
import category_theory.products.basic
import category_theory.pi.basic
import category_theory.category.basic
import tactic.nth_rewrite

/-!
# Groupoids

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

@[simps] def groupoid.inv_equiv : (X ⟶ Y) ≃ (Y ⟶ X) :=
{ to_fun := groupoid.inv,
  inv_fun := groupoid.inv,
  left_inv := λ f, by simp,
  right_inv := λ f, by simp }

variables (X Y)

/-- In a groupoid, isomorphisms are equivalent to morphisms. -/
def groupoid.iso_equiv_hom : (X ≅ Y) ≃ (X ⟶ Y) :=
{ to_fun := iso.hom,
  inv_fun := λ f, ⟨f, groupoid.inv f⟩,
  left_inv := λ i, iso.ext rfl,
  right_inv := λ f, rfl }

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

section

variables {C : Type u}

@[simp] lemma groupoid.inv_id  [G : groupoid.{v} C] (X : C) :
  G.inv (𝟙 X) = 𝟙 X :=
calc G.inv (𝟙 X)
   = (G.inv (𝟙 X)) ≫ (𝟙 X) : (category.comp_id (G.inv (𝟙 _))).symm
...= 𝟙 X                   : groupoid.inv_comp' (𝟙 _)

@[simp] lemma groupoid.inv_of_comp  [G : groupoid.{v} C]
  {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : G.inv (f ≫ g) = (G.inv g) ≫ (G.inv f) :=
( calc (G.inv g) ≫ (G.inv f)
     = (G.inv g) ≫ (G.inv f) ≫ (f ≫ g) ≫ (G.inv $ f ≫ g) : by simp
  ...= (G.inv g) ≫ g ≫ (G.inv $ f ≫ g) : by { rw category.assoc, nth_rewrite 1 ←category.assoc,
                                               simp, }
  ...= G.inv (f ≫ g) : by { rw ←category.assoc, simp, }
).symm

@[simp] lemma groupoid.inv_inv  [G : groupoid.{v} C] (X Y : C) (f : X ⟶ Y) :
  G.inv (G.inv f) = f :=
calc G.inv (G.inv f)
   = (G.inv (G.inv f)) ≫ (𝟙 _) : by rw category.comp_id
...= (G.inv (G.inv f)) ≫ (G.inv f ≫ f) : by rw ←groupoid.inv_comp
...= (G.inv (G.inv f) ≫ G.inv f) ≫ f : by rw ←category.assoc
...= (𝟙 _) ≫ f : by rw groupoid.inv_comp
...= f : by rw category.id_comp

@[simp]
lemma groupoid.functor_map_inv  [G : groupoid.{v} C] {D : Type u₂} [H : groupoid.{v₂} D]
  (φ : C ⥤ D) {c d : C} (f : c ⟶ d) :
  φ.map (G.inv f) = H.inv (φ.map f) :=
calc φ.map (G.inv f)
   = ((φ.map $ G.inv f) ≫ (φ.map f)) ≫ (H.inv $ φ.map f) : by simp
...= (H.inv $ φ.map f) : by simp [←functor.map_comp']

end

end category_theory
