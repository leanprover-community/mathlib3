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

open cardinal finite_dimensional

namespace module.free

section ring

variables [ring R] [strong_rank_condition R]
variables [add_comm_group M] [module R M] [module.free R M] [module.finite R M]

/-- If `M` is finite and free, `finrank M = rank M`. -/
lemma finrank_eq_rank : ↑(finrank R M) = module.rank R M :=
begin
  letI := nontrivial_of_invariant_basis_number R,
  simp [finrank, rank_eq_card_choose_basis_index, fintype_card],
end

end ring

section comm_ring

variables [comm_ring R] [strong_rank_condition R]
variables [add_comm_group M] [module R M] [module.free R M] [module.finite R M]
variables [add_comm_group N] [module R N] [module.free R N] [module.finite R N]

/-- The finrank of `M →ₗ[R] N` is `(finrank R M) * (finrank R N)`. -/
@[simp] lemma finrank_linear_hom : finrank R (M →ₗ[R] N) = (finrank R M) * (finrank R N) :=
begin
  classical,
  letI := nontrivial_of_invariant_basis_number R,
  have h := (linear_map.to_matrix (choose_basis R M) (choose_basis R N)),
  let b := (matrix.std_basis _ _ _).map h.symm,
  rw [finrank, dim_eq_card_basis b, ← fintype_card, mk_to_nat_eq_card, finrank, finrank,
    rank_eq_card_choose_basis_index, rank_eq_card_choose_basis_index, mk_to_nat_eq_card,
    mk_to_nat_eq_card, fintype.card_prod, mul_comm]
end

/-- The finrank of `M × N` is `(finrank R M) + (finrank R N)`. -/
@[simp] lemma finrank_prod : finrank R (M × N) = (finrank R M) + (finrank R N) :=
begin
  letI := nontrivial_of_invariant_basis_number R,
  rw [finrank, ← ((choose_basis R M).prod (choose_basis R N)).mk_eq_dim'',
    mk_to_nat_eq_card, fintype.card_sum, finrank, finrank, rank_eq_card_choose_basis_index,
    rank_eq_card_choose_basis_index, mk_to_nat_eq_card, mk_to_nat_eq_card]
end

end comm_ring

end module.free
