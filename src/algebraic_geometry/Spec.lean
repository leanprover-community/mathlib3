import algebraic_geometry.locally_ringed_space
import algebraic_geometry.structure_sheaf

noncomputable theory

namespace algebraic_geometry

def Spec.SheafedSpace (R : CommRing) : SheafedSpace CommRing :=
{ carrier := Top.of (prime_spectrum R),
  ..structure_sheaf R }

def Spec.LocallyRingedSpace (R : CommRing) : LocallyRingedSpace :=
{ local_ring := λ x,
    (local_ring.of_ring_equiv (stalk_iso R x).symm.CommRing_iso_to_ring_equiv).mp
      (by { dsimp, apply_instance, }),
  ..Spec.SheafedSpace R }

end algebraic_geometry
