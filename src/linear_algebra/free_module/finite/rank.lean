/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import linear_algebra.free_module.rank
import linear_algebra.free_module.finite.basic

/-!

# Rank of finite free modules

This is a basic API for the rank of finite free modules.

-/

universes u v w

variables (R : Type u) (M : Type v) (N : Type w)

open_locale tensor_product direct_sum big_operators cardinal

open cardinal

namespace module.free

section comm_ring

variables [comm_ring R] [nontrivial R] [strong_rank_condition R]
variables [add_comm_group M] [module R M] [module.free R M] [module.finite R M]
variables [add_comm_group N] [module R N] [module.free R N] [module.finite R N]

/-- The rank of `M →ₗ[R] N` is `(module.rank R M).lift * (module.rank R N).lift`. -/
@[simp] lemma rank_linear_hom : module.rank R (M →ₗ[R] N) = lift.{w v} (module.rank R M) *
  lift.{v w} (module.rank R N) :=
begin
  classical,
  have h := (linear_map.to_matrix (choose_basis R M) (choose_basis R N)).lift_dim_eq,
  simp only [rank_matrix, lift_lift, lift_mul] at h,
  rw [← lift_lift.{(max w v) (max (max w v u) v w) w},
    ← lift_lift.{(max v w) (max (max w v u) v w) v}, ← lift_mul, lift_inj] at h,
  simpa [rank_eq_card_choose_basis_index, lift_umax, mul_comm] using h
end

/-- If `M` and `N` lie in the same universe, the rank of `M →ₗ[R] N` is
  `(module.rank R M) * (module.rank R N)`. -/
@[simp] lemma rank_linear_hom' (N : Type v) [add_comm_group N] [module R N] [module.free R N]
  [module.finite R N] : module.rank R (M →ₗ[R] N) = (module.rank R M) * (module.rank R N) :=
by simp

end comm_ring

end module.free
