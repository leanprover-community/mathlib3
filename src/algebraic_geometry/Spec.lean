/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebraic_geometry.locally_ringed_space
import algebraic_geometry.structure_sheaf
import data.equiv.transfer_instance

/-!
# $Spec R$ as a `LocallyRingedSpace`

We bundle the `structure_sheaf R` construction for `R : CommRing` as a `LocallyRingedSpace`.

## Future work

Make it a functor.

-/

noncomputable theory

namespace algebraic_geometry

/--
Spec of a commutative ring, as a `SheafedSpace`.
-/
def Spec.SheafedSpace (R : CommRing) : SheafedSpace CommRing :=
{ carrier := Top.of (prime_spectrum R),
  ..structure_sheaf R }

/--
Spec of a commutative ring, as a `PresheafedSpace`.
-/
def Spec.PresheafedSpace (R : CommRing) : PresheafedSpace CommRing :=
(Spec.SheafedSpace R).to_PresheafedSpace

/--
Spec of a commutative ring, as a `LocallyRingedSpace`.
-/
def Spec.LocallyRingedSpace (R : CommRing) : LocallyRingedSpace :=
{ local_ring := λ x, @@ring_equiv.local_ring _
    (show local_ring (localization.at_prime _), by apply_instance) _
    (category_theory.iso.CommRing_iso_to_ring_equiv $ stalk_iso R x).symm,
  .. Spec.SheafedSpace R }

end algebraic_geometry
