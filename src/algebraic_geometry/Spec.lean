/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebraic_geometry.locally_ringed_space
import algebraic_geometry.structure_sheaf

/-!
# $Spec R$ as a `SheafedSpace`

We bundle the `structure_sheaf R` construction for `R : CommRing` as a `SheafedSpace`.

## Future work
Show that this is a locally ringed space.

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


-- PROJECT: define `Spec.LocallyRingedSpace`. For more details see the PROJECT note in `Scheme.lean`.

end algebraic_geometry
