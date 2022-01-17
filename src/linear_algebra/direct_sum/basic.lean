/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.algebra.subalgebra
import algebra.direct_sum.internal
import linear_algebra.dfinsupp

/-!
# Miscellaneous result about submodules expressed in terms of direct sums

This file contains results which need the ring structure on `direct_sum` as well as various linear
algebra results.
-/
open_locale direct_sum

namespace submodule
variables {R A : Type*} [comm_ring R] [semiring A] [algebra R A]

/-- The supremum of powers of a submodule is a subalgebra, and equal to the range of the `alg_hom`
formed summing the coercions of each element of the direct sum. -/
lemma supr_pow_eq_range (S : submodule R A) :
  (⨆ i : ℕ, S ^ i) =
  (direct_sum.to_algebra R _
    (λ i : ℕ, (S ^ i).subtype) rfl (λ i j hi hj, rfl) (λ r, rfl)).range.to_submodule :=
begin
  rw submodule.supr_eq_range_dfinsupp_lsum,
  exact set_like.coe_injective rfl
end

end submodule
