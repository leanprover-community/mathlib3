import algebraic_geometry.locally_ringed_space
import algebraic_geometry.structure_sheaf

noncomputable theory

namespace algebraic_geometry

def Spec.SheafedSpace (R : CommRing) : SheafedSpace CommRing :=
{ carrier := Top.of (prime_spectrum R),
  ..structure_sheaf R }

-- PROJECT: define `Spec.LocallyRingedSpace`. For more details see the PROJECT note in `Scheme.lean`.

end algebraic_geometry
