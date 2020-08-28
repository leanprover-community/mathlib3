/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import algebraic_geometry.sheafed_space
import algebra.category.CommRing
import algebraic_geometry.stalks
import ring_theory.ideal.basic
import data.equiv.transfer_instance

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

-- move this
lemma local_ring.of_surjective {A B : Type*} [comm_ring A] [local_ring A] [comm_ring B] [nontrivial B]
  (f : A →+* B) (hf : function.surjective f) :
  local_ring B :=
{ is_local :=
  begin
    intros b,
    obtain ⟨a, rfl⟩ := hf b,
    apply (local_ring.is_unit_or_is_unit_one_sub_self a).imp f.is_unit_map _,
    rw [← f.map_one, ← f.map_sub],
    apply f.is_unit_map,
  end,
  .. ‹nontrivial B› }

-- move this
lemma local_ring.of_ring_equiv {A B : Type*} [comm_ring A] [comm_ring B] (e : A ≃+* B) :
  local_ring A ↔ local_ring B :=
begin
  split,
  { introI _inst,
    haveI := e.symm.to_equiv.nontrivial,
    refine @local_ring.of_surjective A B _ _ _ _ e e.to_equiv.surjective, },
  { introI _inst,
    haveI := e.to_equiv.nontrivial,
    refine @local_ring.of_surjective B A _ _ _ _ e.symm e.symm.to_equiv.surjective, },
end

namespace algebraic_geometry

/-- A `LocallyRingedSpace` is a topological space equipped with a sheaf of commutative rings
such that all the stalks are local rings.

A morphism of locally ringed spaces is a morphism of ringed spaces
such that the morphims induced on stalks are local ring homomorphisms. -/
structure LocallyRingedSpace extends SheafedSpace CommRing :=
(local_ring : ∀ x, local_ring (presheaf.stalk x))

attribute [instance] LocallyRingedSpace.local_ring

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

/-- The identity morphism on a locally ringed space. -/
@[simps]
def id (X : LocallyRingedSpace) : hom X X :=
⟨𝟙 _, λ x, by { erw PresheafedSpace.stalk_map.id, apply is_local_ring_hom_id, }⟩

/-- Composition of morphisms of locally ringed spaces. -/
@[simps]
def comp {X Y Z : LocallyRingedSpace} (f : hom X Y) (g : hom Y Z) : hom X Z :=
⟨f.val ≫ g.val, λ x,
begin
  erw PresheafedSpace.stalk_map.comp,
  exact @is_local_ring_hom_comp _ _ _ _ _ _ _ _ (f.2 _) (g.2 _),
end⟩

/-- The category of locally ringed spaces. -/
instance : category LocallyRingedSpace :=
{ hom := hom,
  id := id,
  comp := λ X Y Z f g, comp f g,
  comp_id' := by { intros, ext1, simp, },
  id_comp' := by { intros, ext1, simp, },
  assoc' := by { intros, ext1, simp, }, }.

-- PROJECT: once we have `PresheafedSpace.restrict_stalk_iso`
-- (that restriction doesn't change stalks) we can uncomment this.
/-
def restrict {U : Top} (X : LocallyRingedSpace)
  (f : U ⟶ X.to_Top) (h : open_embedding f) : LocallyRingedSpace :=
{ local_ring :=
  begin
    intro x,
    dsimp at *,
    -- We show that the stalk of the restriction is isomorphic to the original stalk,
    have := X.to_SheafedSpace.to_PresheafedSpace.restrict_stalk_iso f h x,
    -- and then transfer `local_ring` across the ring equivalence.
    apply (local_ring.of_ring_equiv (this.CommRing_iso_to_ring_equiv)).mpr,
    apply X.local_ring,
  end,
  .. X.to_SheafedSpace.restrict _ f h }
-/

end LocallyRingedSpace

end algebraic_geometry
