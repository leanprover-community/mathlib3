/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import topology.noetherian_space
import algebraic_geometry.Scheme

/-!

# The spectrum of a noetherian ring is noetherian.

-/

open topological_space prime_spectrum

section

lemma prime_spectrum.noetherian_space :
  noetherian_space (prime_spectrum R) ↔ is_noetherian_ring R :=
begin
  rw (noetherian_space_tfae (prime_spectrum R)).out 0 1,
  rw [is_noetherian_ring_iff, is_noetherian_iff_well_founded],
  symmetry,
  fapply surjective.well_founded_iff,
  { exact λ I, ⟨_, is_closed_zero_locus I⟩ },
  { exact λ s, ⟨_, closeds.ext $ ((is_closed_iff_zero_locus_ideal _).mp s.2).some_spec.symm⟩ },
  { intros a b, change _ ↔ zero_locus (a : set R) < zero_locus b,
    have := (gi R).l_lt_l_iff, }
end

end

namespace algebraic_geometry



end algebraic_geometry
