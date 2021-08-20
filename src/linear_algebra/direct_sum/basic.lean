/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.algebra.subalgebra
import algebra.direct_sum_graded
import linear_algebra.dfinsupp

/-!
# Miscellaneous result about submodules expressed in terms of direct sums

This file contains results which need the ring structure on `direct_sum` as well as various linear
algebra results.
-/
open_locale direct_sum

namespace submodule
variables {R A : Type*} [comm_ring R] [semiring A] [algebra R A]

/-- A version of `submodule.supr_eq_range_dfinsupp_lsum` when working with submodules of an algebra.
-/
lemma to_add_submonoid_supr_pow_eq_srange (S : submodule R A) :
  (⨆ i : ℕ, S ^ i).to_add_submonoid =
  (direct_sum.to_semiring
    (λ i : ℕ, (S ^ i).subtype.to_add_monoid_hom) rfl (λ i j hi hj, rfl)).srange.to_add_submonoid :=
begin
  rw submodule.supr_eq_range_dfinsupp_lsum,
  exact set_like.coe_injective rfl
end

/-- -/
lemma supr_pow_eq_top_iff (S : submodule R A) :
  (⨆ i : ℕ, S ^ i) = ⊤ ↔
  (direct_sum.to_semiring
    (λ i : ℕ, (S ^ i).subtype.to_add_monoid_hom) rfl (λ i j hi hj, rfl)).srange = ⊤ :=
begin
  rw submodule.supr_eq_range_dfinsupp_lsum,
  rw ←subsemiring.to_add_submonoid_injective.eq_iff,
  rw ←submodule.to_add_submonoid_injective.eq_iff,
  exact iff.rfl,
end

end submodule
