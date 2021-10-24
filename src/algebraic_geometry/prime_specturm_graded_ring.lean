import topology.opens
import ring_theory.ideal.prod
import linear_algebra.finsupp
import algebra.punit_instances
import ring_theory.homogeneous_ideal
import algebra.direct_sum.ring


-- we only consider rings graded by nonnegative elements

noncomputable theory
open_locale classical direct_sum big_operators pointwise
open direct_sum

variables {ι : Type*} [linear_ordered_cancel_add_comm_monoid ι]
variables (A : ι → Type*) [Π i, add_comm_group (A i)] [gcomm_semiring A]

def irrelavent_ideal : ideal (⨁ i, A i) :=
  ideal.span (graded_monoid.to_direct_sum '' { x | 0 < x.1})

def prime_spectrum_of_graded_ring :=
  {I : ideal (⨁ i, A i) //
    I.is_prime ∧ homogeneous_ideal I ∧ ¬(irrelavent_ideal A ≤ I)}
