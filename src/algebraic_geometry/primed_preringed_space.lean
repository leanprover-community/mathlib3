/-
Copyright (c) 2021 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/

import algebraic_geometry.locally_ringed_space
import algebraic_geometry.prime_spectrum.basic

/-! Primed preringed spaces

We introduce the category of primed preringed spaces, whose objects are
objects of `PresheafedSpace CommRing` equipped with a choice of a subset
of the prime spectrum of the stalk at each point in the space, and
morphisms are presheafed space morphisms whose induced maps on stalks
are compatible with the choices of subsets. We show that `PrimedPreringedSpace`
has all limits.

We then define the obviously fully faithful inclusion functor from
`LocallyRingedSpace` to `PrimedPreringedSpace` and Gillam's localization
functor in the other direction, and show they are an adjoint pair. The
inclusion functor (the left adjoint) is therefore coreflective, which implies
that `LocallyRingedSpace` also has all limits. We also deduce the Gamma-Spec
adjunction from this adjunction.

Finally, we use the Gamma-adjunction adjunciton to show that `LocallyRingedSpace`
having all limits implies that `Scheme` has all finite limits.

Reference: Gillam, Localization of Ringed Spaces, https://arxiv.org/abs/1103.2139

-/


universe v

open category_theory
open topological_space
open opposite
open Top
open Top.presheaf

namespace algebraic_geometry

/-- A `PrimedPreringedSpace` is a topological space equipped with a presheaf of
commutative rings and a choice of a subset of the prime spectrum of the stalk at
every point, called a prime system. -/
@[nolint has_inhabited_instance]
structure PrimedPreringedSpace extends PresheafedSpace CommRing :=
(prime_system : Π x, set (prime_spectrum (presheaf.stalk x)))


namespace PrimedPreringedSpace

variables (X Y Z : PrimedPreringedSpace.{v})

instance : has_coe_to_sort PrimedPreringedSpace (Type v) :=
⟨λ X : PrimedPreringedSpace, (X.to_PresheafedSpace : Type v)⟩

/-- A morphism of primed preringed spaces is a morphism of presheafed spaces such that
the morphisms induced on prime spectra of stalks send one prime system into the other. -/
def hom : Type* :=
{ f : X.to_PresheafedSpace ⟶ Y.to_PresheafedSpace // ∀ x, X.prime_system x ⊆
  (prime_spectrum.comap (PresheafedSpace.stalk_map f x))⁻¹' Y.prime_system (f.1 x) }

instance : quiver PrimedPreringedSpace := ⟨hom⟩

@[ext] lemma hom_ext {X Y} (f g : hom X Y) (w : f.1 = g.1) : f = g :=
subtype.eq w

/-- The stalk of a primed preringed space. -/
noncomputable
def stalk (x : X) : CommRing := X.presheaf.stalk x

/-- The identity morphism on a primed preringed space. -/
@[simps]
def id : hom X X :=
⟨𝟙 _, λ x, by { rw PresheafedSpace.stalk_map.id, erw prime_spectrum.comap_id, refl }⟩

instance : inhabited (hom X X) := ⟨id X⟩

/-- Composition of morphisms of primed preringed spaces. -/
@[simps]
def comp {X Y Z} (f : hom X Y) (g : hom Y Z) : hom X Z :=
⟨f.val ≫ g.val, λ x,
  by { rw PresheafedSpace.stalk_map.comp, erw prime_spectrum.comap_comp,
    exact (f.property x).trans (λ _ h, g.property (f.1.1 x) h) }⟩

/-- The category of primed preringed spaces. -/
instance : category PrimedPreringedSpace :=
{ hom := hom,
  id := id,
  comp := λ X Y Z f g, comp f g,
  comp_id' := by { intros, ext1, apply category.comp_id },
  id_comp' := by { intros, ext1, apply category.id_comp },
  assoc' := by { intros, ext1, apply category.assoc } }.

def emb_from_LocallyRingedSpace : LocallyRingedSpace ⥤ PrimedPreringedSpace :=
{ obj := λ X, ⟨X.to_PresheafedSpace, λ x, {@local_ring.closed_point _ _ (X.local_ring x)}⟩,
  map := λ X Y f, ⟨f.val, λ x, by { rw [set.singleton_subset_iff, set.mem_preimage,
    (@local_ring.local_hom_iff_comap_closed_point _ _ (Y.2 _) _ _ (X.2 x)
      (PresheafedSpace.stalk_map f.1 x)).1 (f.property x)], apply set.mem_singleton }⟩}



end PrimedPreringedSpace

end algebraic_geometry
