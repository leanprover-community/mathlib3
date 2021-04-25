/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import linear_algebra.exterior_algebra
import linear_algebra.clifford_algebra

/-!
Tests that the ring instances for `free_algebra` and derived quotient types actually work.

There is some discussion about this in
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/algebra.2Esemiring_to_ring.20breaks.20semimodule.20typeclass.20lookup/near/212580241

In essence, the use of `attribute [irreducible] the_type` was breaking instance resolution on that
type.
-/

variables {S : Type*} {M : Type*}


section free

variables [comm_ring S]

example : (1 : free_algebra S M) - (1 : free_algebra S M) = 0 := by rw sub_self

end free


section exterior

variables [comm_ring S] [add_comm_monoid M] [module S M]

example : (1 : exterior_algebra S M) - (1 : exterior_algebra S M) = 0 := by rw sub_self

end exterior


section clifford

variables [comm_ring S] [add_comm_group M] [module S M] (Q : quadratic_form S M)

example : (1 : clifford_algebra Q) - (1 : clifford_algebra Q) = 0 := by rw sub_self

end clifford
