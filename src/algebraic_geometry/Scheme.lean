/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebraic_geometry.locally_ringed_space
import algebraic_geometry.Spec

/-!
# The category of schemes

A scheme is a locally ringed space such that every point is contained in some open set
where there is an isomorphism of presheaves between the restriction to that open set,
and the structure sheaf of `Spec R`, for some commutative ring `R`.

A morphism is schemes is just a morphism of the underlying locally ringed spaces.

-/

open topological_space
open category_theory
open Top

namespace algebraic_geometry

/--
We define `Scheme` as a `X : LocallyRingedSpace`,
along with a proof that every point has an open neighbourhood `U`
so that that the restriction of `X` to `U` is isomorphic, as a space with a presheaf of commutative rings,
to `Spec.PresheafedSpace R` for some `R : CommRing`.

(Note we're not asking in the definition that this is an isomorphism as locally ringed spaces,
although that is a consequence.)
-/
structure Scheme extends X : LocallyRingedSpace :=
(local_affine : ∀ x : carrier, ∃ (U : opens carrier) (m : x ∈ U) (R : CommRing)
  (i : X.to_SheafedSpace.to_PresheafedSpace.restrict _ (opens.inclusion_open_embedding U) ≅
    Spec.PresheafedSpace R), true)

-- PROJECT
-- In fact, we can construct `Spec.LocallyRingedSpace R`,
-- and the isomorphism `i` above is an isomorphism in `LocallyRingedSpace`.
-- However this is a consequence of the above definition, and not necessary for defining schemes.
-- We haven't done this yet because:
-- 1. We haven't proved that the stalk of the structure sheaf is isomorphic to the localisation
--    **as a ring**, only at the level of `Type`.
--    To do this, we need to know that `forget CommRing` preserves filtered colimits.
-- 2. We haven't shown that you can restrict a `LocallyRingedSpace` along an open embedding.
--    We can do this already for `SheafedSpace` (as above), but we need to know that
--    the stalks of the restriction are still local rings, which we follow if we knew that
--    the stalks didn't change.
--    This will follow if we define cofinal functors, and show precomposing with a cofinal functor
--    doesn't change colimits, because open neighbourhoods of `x` within `U` are cofinal in
--    all open neighbourhoods of `x`.

namespace Scheme

/--
Every `Scheme` is a `LocallyRingedSpace`.
-/
-- (This parent projection is apparently not automatically generated because
-- we used the `extends X : LocallyRingedSpace` syntax.)
def to_LocallyRingedSpace (S : Scheme) : LocallyRingedSpace := { ..S }

/--
The empty scheme, as `Spec 0`.
-/
noncomputable
def empty : Scheme :=
{ local_ring := λ x, false.elim (prime_spectrum.punit x),
  local_affine := λ x, false.elim (prime_spectrum.punit x),
  ..Spec.SheafedSpace (CommRing.of punit) }

noncomputable
instance : has_emptyc Scheme := ⟨empty⟩

noncomputable
instance : inhabited Scheme := ⟨∅⟩

/--
Schemes are a full subcategory of locally ringed spaces.
-/
instance : category Scheme :=
induced_category.category Scheme.to_LocallyRingedSpace

end Scheme

end algebraic_geometry
