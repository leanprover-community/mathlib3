import algebraic_geometry.locally_ringed_space
import algebraic_geometry.structure_sheaf

noncomputable theory

namespace algebraic_geometry

def Spec_as_LRS (R : CommRing) : LocallyRingedSpace :=
{ carrier := Top.of (prime_spectrum R),
  local_ring := λ x, begin dsimp, sorry, end, -- we need to calculate the stalks of the structure sheaf!
  ..structure_sheaf R }

end algebraic_geometry
