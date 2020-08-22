/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import algebraic_geometry.sheafed_space
import algebra.category.CommRing
import algebraic_geometry.stalks
import ring_theory.ideal.basic


universes v u

open category_theory
open Top
open topological_space
open opposite
open category_theory.category category_theory.functor

--move this
lemma ring_hom.is_unit_map {A B: Type*} [semiring A] [semiring B]
  (f : A →+* B) {a : A} (h : is_unit a) : is_unit (f a) :=
begin
  rcases h with ⟨u, rfl⟩,
  exact ⟨units.map f.to_monoid_hom u, rfl⟩,
end

namespace algebraic_geometry

-- /-- A `RingedSpace` is a topological space equipped with a sheaf of commutative rings.

-- A morphism of ringed spaces is a morphism of ring-presheafed spaces. -/
-- @[derive category]
-- def RingedSpace := SheafedSpace CommRing

/-- A `LocallyRingedSpace` is a topological space equipped with a sheaf of commutative rings
such that all the stalks are local rings.

A morphism of locally ringed spaces is a morphism of ringed spaces
such that the morphims induced on stalks are local ring homomorphisms. -/
structure LocallyRingedSpace extends SheafedSpace CommRing :=
(local_ring : ∀ x, local_ring (presheaf.stalk x))

namespace LocallyRingedSpace

variables (X : LocallyRingedSpace)

/-- The underlying topological space of a locally ringed space. -/
def to_Top : Top := X.1.carrier

instance : has_coe_to_sort LocallyRingedSpace :=
{ S := Type u,
  coe := λ X : LocallyRingedSpace, (X.to_Top : Type u), }

-- PROJECT: how about a typeclass "has_structure_sheaf" to mediate the 𝒪 notation, rather
-- than defining it over and over for PresheafedSpace, LRS, Scheme, etc.

/-- The structure sheaf of a locally ringed space. -/
def 𝒪 : sheaf CommRing X.to_Top := ⟨X.1.presheaf, X.1.sheaf_condition⟩

/-- A morphism of locally ringed spaces is a morphism of ringed spaces
 such that the morphims induced on stalks are local ring homomorphisms. -/
def hom (X Y : LocallyRingedSpace) : Type* :=
{ f : X.to_SheafedSpace ⟶ Y.to_SheafedSpace // ∀ x, is_local_ring_hom (PresheafedSpace.stalk_map f x) }

instance : has_hom LocallyRingedSpace := ⟨hom⟩

@[ext] lemma hom_ext {X Y : LocallyRingedSpace} (f g : hom X Y) (w : f.1 = g.1) : f = g :=
subtype.eq w

-- TODO define `sheaf.stalk` so we can write `X.𝒪.stalk` here?
def stalk (X : LocallyRingedSpace) (x : X) := X.presheaf.stalk x

def stalk_map {X Y : LocallyRingedSpace} (f : X ⟶ Y) (x : X) :
  Y.stalk (f.1.1 x) ⟶ X.stalk x :=
PresheafedSpace.stalk_map f.1 x

instance {X Y : LocallyRingedSpace} (f : X ⟶ Y) (x : X) :
  is_local_ring_hom (stalk_map f x) := f.2 x

-- move this
instance is_local_ring_hom_id (A : Type*) [semiring A] : is_local_ring_hom (ring_hom.id A) :=
{ map_nonunit := λ a, id }

-- move this
@[simp] lemma is_unit_map_iff {A B : Type*} [semiring A] [semiring B] (f : A →+* B)
  [is_local_ring_hom f] (a) :
  is_unit (f a) ↔ is_unit a :=
⟨is_local_ring_hom.map_nonunit a, f.is_unit_map⟩

-- move this
instance is_local_ring_hom_comp {A B C : Type*} [semiring A] [semiring B] [semiring C]
  (g : B →+* C) (f : A →+* B) [is_local_ring_hom g] [is_local_ring_hom f] :
  is_local_ring_hom (g.comp f) :=
{ map_nonunit :=
  begin
    intro a,
    simp only [function.comp_app, ring_hom.coe_comp, is_unit_map_iff],
    exact id
  end }

@[simps]
def id (X : LocallyRingedSpace) : hom X X :=
⟨𝟙 _, λ x, by { erw PresheafedSpace.stalk_map.id, apply LocallyRingedSpace.is_local_ring_hom_id, }⟩

@[simps]
def comp {X Y Z : LocallyRingedSpace} (f : hom X Y) (g : hom Y Z) : hom X Z :=
⟨f.val ≫ g.val, λ x,
begin
  -- TODO yuck!
  erw PresheafedSpace.stalk_map.comp,
  apply @LocallyRingedSpace.is_local_ring_hom_comp _ _ _ _ _ _ _ _ _ _,
  exact f.2 _,
  exact g.2 _,
end⟩

instance : category LocallyRingedSpace :=
{ hom := hom,
  id := id,
  comp := λ X Y Z f g, comp f g,
  comp_id' := by { intros, ext1, simp, },
  id_comp' := by { intros, ext1, simp, },
  assoc' := by { intros, ext1, simp, }, }

end LocallyRingedSpace

end algebraic_geometry
