import algebraic_geometry.locally_ringed_space
import algebraic_geometry.structure_sheaf

noncomputable theory

namespace algebraic_geometry

def Spec_as_LRS (R : CommRing) : LocallyRingedSpace :=
{ carrier := Top.of (prime_spectrum R),
  local_ring := λ x,
    (local_ring.of_ring_equiv (stalk_iso R x).symm.CommRing_iso_to_ring_equiv).mp
      (by { dsimp, apply_instance, }),
  ..structure_sheaf R }

end algebraic_geometry
