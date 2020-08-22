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

namespace algebraic_geometry

-- /-- A `RingedSpace` is a topological space equipped with a sheaf of commutative rings.

-- A morphism of ringed spaces is a morphism of ring-presheafed spaces. -/
-- @[derive category]
-- def RingedSpace := SheafedSpace CommRing

/-- A `LocallyRingedSpace` is a topological space equipped with a sheaf of commutative rings
such that all the stalks are local rings.

A morphism of locally ringed spaces is a morphism of ringed spaces
 such that the morphims induced on stalks are local ring homomorphisms. -/
 @[derive has_coe_to_sort]
def LocallyRingedSpace :=
{X : SheafedSpace CommRing // ∀ x : X, local_ring (X.𝒪.stalk x)}

namespace LocallyRingedSpace

variables (X : LocallyRingedSpace)

/-- The underlying topological space of a locally ringed space. -/
def to_Top : Top := X.1.carrier

/-- The structure sheaf of a locally ringed space. -/
def 𝒪 : sheaf CommRing X.to_Top := ⟨X.1.𝒪, X.1.sheaf_condition⟩

/-- A morphism of locally ringed spaces is a morphism of ringed spaces
 such that the morphims induced on stalks are local ring homomorphisms. -/
def hom (X Y : LocallyRingedSpace) : Type* :=
{ f : X.1 ⟶ Y.1 // ∀ x, is_local_ring_hom (PresheafedSpace.stalk_map f x) }

instance : has_hom LocallyRingedSpace := ⟨hom⟩

def stalk_map {X Y : LocallyRingedSpace} (f : X ⟶ Y) (x : X) :
  Y.𝒪.presheaf.stalk (f.1.1 x) ⟶ X.𝒪.presheaf.stalk x :=
PresheafedSpace.stalk_map _ _

instance {X Y : LocallyRingedSpace} (f : X ⟶ Y) (x : X) :
  is_local_ring_hom (stalk_map f x) := f.2 x

-- move this
instance is_local_ring_hom_id (A : Type*) [semiring A] : is_local_ring_hom (ring_hom.id A) :=
{ map_nonunit := λ a, id }

-- move this
@[simp] lemma is_unit_map_iff {A B : Type*} [semiring A] [semiring B] (f : A →+* B)
  [is_local_ring_hom f] (a) :
  is_unit (f a) ↔ is_unit a :=
⟨is_local_ring_hom.map_nonunit a, sorry⟩

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

instance : category LocallyRingedSpace :=
{ hom := hom,
  id := λ X, ⟨𝟙 _, λ x,
  by { sorry }⟩,
  comp := λ X Y Z f g,
  ⟨f.val ≫ g.val, _⟩,
  id_comp' := _,
  comp_id' := _,
  assoc' := _ }

end LocallyRingedSpace

end algebraic_geometry
