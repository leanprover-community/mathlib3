import ring_theory.dedekind_domain.integral_closure
import ring_theory.dedekind_domain.ideal

open ideal

variables {A K : Type*} [comm_ring A] [field K] [is_domain A] [is_dedekind_domain A]
variables [algebra A K] [is_fraction_ring A K]
variables {L : Type*} [field L] {C : Type*} [comm_ring C]
variables [algebra K L] [finite_dimensional K L] [algebra A L] [is_scalar_tower A K L]
variables [algebra C L] [is_integral_closure C A L] [algebra A C] [is_scalar_tower A C L]
variables {P : ideal A} [is_maximal P] {Q : ideal C} [is_prime Q]
include K L
--example : (Q.comap $ algebra_map A C).is_prime := ideal.is_prime.comap (algebra_map A C)
--example : P.map (algebra_map A C) ≤ Q ↔ P ≤ Q.comap (algebra_map A C) := map_le_iff_le_comap
--example : Q ∣ P.map (algebra_map A C) ↔ Q.comap (algebra_map A C) ∣ P :=
--by rw [dvd_iff_le, dvd_iff_le, map_le_iff_le_comap]  --requires dedekind domain.
