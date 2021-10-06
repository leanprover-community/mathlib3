/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import algebraic_geometry.ringed_space
import data.equiv.transfer_instance

/-!
# The category of locally ringed spaces

We define (bundled) locally ringed spaces (as `SheafedSpace CommRing` along with the fact that the
stalks are local rings), and morphisms between these (morphisms in `SheafedSpace` with
`is_local_ring_hom` on the stalk maps).

## Future work
* Define the restriction along an open embedding
-/

universes v u

open category_theory
open Top
open topological_space
open opposite
open category_theory.category category_theory.functor

namespace algebraic_geometry

/-- A `LocallyRingedSpace` is a topological space equipped with a sheaf of commutative rings
such that all the stalks are local rings.

A morphism of locally ringed spaces is a morphism of ringed spaces
such that the morphims induced on stalks are local ring homomorphisms. -/
@[nolint has_inhabited_instance]
structure LocallyRingedSpace extends SheafedSpace CommRing :=
(local_ring : ∀ x, local_ring (presheaf.stalk x))

attribute [instance] LocallyRingedSpace.local_ring

namespace LocallyRingedSpace

variables (X : LocallyRingedSpace)

/--
An alias for `to_SheafedSpace`, where the result type is a `RingedSpace`.
This allows us to use dot-notation for the `RingedSpace` namespace.
 -/
def to_RingedSpace : RingedSpace := X.to_SheafedSpace

/-- The underlying topological space of a locally ringed space. -/
def to_Top : Top := X.1.carrier

instance : has_coe_to_sort LocallyRingedSpace :=
{ S := Type u,
  coe := λ X : LocallyRingedSpace, (X.to_Top : Type u), }

-- PROJECT: how about a typeclass "has_structure_sheaf" to mediate the 𝒪 notation, rather
-- than defining it over and over for PresheafedSpace, LRS, Scheme, etc.

/-- The structure sheaf of a locally ringed space. -/
def 𝒪 : sheaf CommRing X.to_Top := X.to_SheafedSpace.sheaf

/-- A morphism of locally ringed spaces is a morphism of ringed spaces
 such that the morphims induced on stalks are local ring homomorphisms. -/
def hom (X Y : LocallyRingedSpace) : Type* :=
{ f : X.to_SheafedSpace ⟶ Y.to_SheafedSpace //
    ∀ x, is_local_ring_hom (PresheafedSpace.stalk_map f x) }

instance : quiver LocallyRingedSpace := ⟨hom⟩

@[ext] lemma hom_ext {X Y : LocallyRingedSpace} (f g : hom X Y) (w : f.1 = g.1) : f = g :=
subtype.eq w

/--
The stalk of a locally ringed space, just as a `CommRing`.
-/
-- TODO perhaps we should make a bundled `LocalRing` and return one here?
-- TODO define `sheaf.stalk` so we can write `X.𝒪.stalk` here?
noncomputable
def stalk (X : LocallyRingedSpace) (x : X) : CommRing := X.presheaf.stalk x

/--
A morphism of locally ringed spaces `f : X ⟶ Y` induces
a local ring homomorphism from `Y.stalk (f x)` to `X.stalk x` for any `x : X`.
-/
noncomputable
def stalk_map {X Y : LocallyRingedSpace} (f : X ⟶ Y) (x : X) :
  Y.stalk (f.1.1 x) ⟶ X.stalk x :=
PresheafedSpace.stalk_map f.1 x

instance {X Y : LocallyRingedSpace} (f : X ⟶ Y) (x : X) :
  is_local_ring_hom (stalk_map f x) := f.2 x

/-- The identity morphism on a locally ringed space. -/
@[simps]
def id (X : LocallyRingedSpace) : hom X X :=
⟨𝟙 _, λ x, by { erw PresheafedSpace.stalk_map.id, apply is_local_ring_hom_id, }⟩

instance (X : LocallyRingedSpace) : inhabited (hom X X) := ⟨id X⟩

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

/-- The forgetful functor from `LocallyRingedSpace` to `SheafedSpace CommRing`. -/
def forget_to_SheafedSpace : LocallyRingedSpace ⥤ SheafedSpace CommRing :=
{ obj := λ X, X.to_SheafedSpace,
  map := λ X Y f, f.1, }

instance : faithful forget_to_SheafedSpace := {}

/--
Given two locally ringed spaces `X` and `Y`, an isomorphism between `X` and `Y` as _sheafed_
spaces can be lifted to a morphism `X ⟶ Y` as locally ringed spaces.

See also `iso_of_SheafedSpace_iso`.
-/
@[simps]
def hom_of_SheafedSpace_hom_of_is_iso {X Y : LocallyRingedSpace}
  (f : X.to_SheafedSpace ⟶ Y.to_SheafedSpace) [is_iso f] : X ⟶ Y :=
subtype.mk f $ λ x,
-- Here we need to see that the stalk maps are really local ring homomorphisms.
-- This can be solved by type class inference, because stalk maps of isomorphisms are isomorphisms
-- and isomorphisms are local ring homomorphisms.
show is_local_ring_hom (PresheafedSpace.stalk_map
  (SheafedSpace.forget_to_PresheafedSpace.map f) x),
by apply_instance

/--
Given two locally ringed spaces `X` and `Y`, an isomorphism between `X` and `Y` as _sheafed_
spaces can be lifted to an isomorphism `X ⟶ Y` as locally ringed spaces.

This is related to the property that the functor `forget_to_SheafedSpace` reflects isomorphisms.
In fact, it is slightly stronger as we do not require `f` to come from a morphism between
_locally_ ringed spaces.
-/
def iso_of_SheafedSpace_iso {X Y : LocallyRingedSpace}
  (f : X.to_SheafedSpace ≅ Y.to_SheafedSpace) : X ≅ Y :=
{ hom := hom_of_SheafedSpace_hom_of_is_iso f.hom,
  inv := hom_of_SheafedSpace_hom_of_is_iso f.inv,
  hom_inv_id' := hom_ext _ _ f.hom_inv_id,
  inv_hom_id' := hom_ext _ _ f.inv_hom_id }

instance : reflects_isomorphisms forget_to_SheafedSpace :=
{ reflects := λ X Y f i,
  { out := by exactI
    ⟨hom_of_SheafedSpace_hom_of_is_iso (category_theory.inv (forget_to_SheafedSpace.map f)),
      hom_ext _ _ (is_iso.hom_inv_id _), hom_ext _ _ (is_iso.inv_hom_id _)⟩ } }

/--
The restriction of a locally ringed space along an open embedding.
-/
@[simps]
noncomputable def restrict {U : Top} (X : LocallyRingedSpace) (f : U ⟶ X.to_Top)
  (h : open_embedding f) : LocallyRingedSpace :=
{ local_ring :=
  begin
    intro x,
    dsimp at *,
    -- We show that the stalk of the restriction is isomorphic to the original stalk,
    apply @ring_equiv.local_ring _ _ _ (X.local_ring (f x)),
    exact (X.to_PresheafedSpace.restrict_stalk_iso f h x).symm.CommRing_iso_to_ring_equiv,
  end,
  .. X.to_SheafedSpace.restrict f h }

/--
The restriction of a locally ringed space `X` to the top subspace is isomorphic to `X` itself.
-/
noncomputable def restrict_top_iso (X : LocallyRingedSpace) :
  X.restrict (opens.inclusion ⊤) (opens.open_embedding ⊤) ≅ X :=
@iso_of_SheafedSpace_iso (X.restrict (opens.inclusion ⊤) (opens.open_embedding ⊤)) X
  X.to_SheafedSpace.restrict_top_iso

/--
The global sections, notated Gamma.
-/
def Γ : LocallyRingedSpaceᵒᵖ ⥤ CommRing :=
forget_to_SheafedSpace.op ⋙ SheafedSpace.Γ

lemma Γ_def : Γ = forget_to_SheafedSpace.op ⋙ SheafedSpace.Γ := rfl

@[simp] lemma Γ_obj (X : LocallyRingedSpaceᵒᵖ) : Γ.obj X = (unop X).presheaf.obj (op ⊤) := rfl

lemma Γ_obj_op (X : LocallyRingedSpace) : Γ.obj (op X) = X.presheaf.obj (op ⊤) := rfl

@[simp] lemma Γ_map {X Y : LocallyRingedSpaceᵒᵖ} (f : X ⟶ Y) :
  Γ.map f = f.unop.1.c.app (op ⊤) ≫ (unop Y).presheaf.map (opens.le_map_top _ _).op := rfl

lemma Γ_map_op {X Y : LocallyRingedSpace} (f : X ⟶ Y) :
  Γ.map f.op = f.1.c.app (op ⊤) ≫ X.presheaf.map (opens.le_map_top _ _).op := rfl

end LocallyRingedSpace

end algebraic_geometry
