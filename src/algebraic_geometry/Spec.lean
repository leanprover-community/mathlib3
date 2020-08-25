import algebraic_geometry.locally_ringed_space
import algebraic_geometry.structure_sheaf

noncomputable theory

namespace algebraic_geometry

def Spec_as_LRS (R : CommRing) : LocallyRingedSpace :=
{ carrier := Top.of (prime_spectrum R),
  local_ring := λ x,
  begin
    -- TODO golf!
    dsimp,
    apply (local_ring.of_ring_equiv _).mp,
    swap 4,
    apply category_theory.iso.CommRing_iso_to_ring_equiv,
    exact (stalk_iso R x).symm,
    show local_ring (localization.at_prime _), -- Need simp lemmas for this!
    apply_instance,
  end,
  ..structure_sheaf R }

end algebraic_geometry
