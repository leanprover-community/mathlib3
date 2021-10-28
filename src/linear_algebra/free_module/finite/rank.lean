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

--TODO: `linear_algebra/finite_dimensional` should import this file, and a lot of results should
--be moved here.

universes u v w

variables (R : Type u) (M : Type v) (N : Type w)

open_locale tensor_product direct_sum big_operators cardinal

open cardinal finite_dimensional fintype

namespace module.free

section ring

variables [ring R] [strong_rank_condition R]
variables [add_comm_group M] [module R M] [module.free R M] [module.finite R M]
variables [add_comm_group N] [module R N] [module.free R N] [module.finite R N]

/-- The rank of a finite and free module is finite. -/
lemma rank_lt_omega : module.rank R M < ω :=
begin
  letI := nontrivial_of_invariant_basis_number R,
  rw [← (choose_basis R M).mk_eq_dim'', lt_omega_iff_fintype],
  exact nonempty.intro infer_instance
end

/-- If `M` is finite and free, `finrank M = rank M`. -/
@[simp] lemma finrank_eq_rank : ↑(finrank R M) = module.rank R M :=
by { rw [finrank, cast_to_nat_of_lt_omega (rank_lt_omega R M)] }

/-- The finrank of a free module `M` over `R` is the cardinality of `choose_basis_index R M`. -/
lemma finrank_eq_card_choose_basis_index : finrank R M = @card (choose_basis_index R M)
  (@choose_basis_index.fintype R M _ _ _ _ (nontrivial_of_invariant_basis_number R) _) :=
begin
  letI := nontrivial_of_invariant_basis_number R,
  simp [finrank, rank_eq_card_choose_basis_index]
end

/-- The finrank of `(ι →₀ R)` is `fintype.card ι`. -/
@[simp] lemma finrank_finsupp {ι : Type v} [fintype ι] : finrank R (ι →₀ R) = card ι :=
by { rw [finrank, rank_finsupp, ← mk_to_nat_eq_card, to_nat_lift] }

/-- The finrank of `(ι → R)` is `fintype.card ι`. -/
lemma finrank_pi {ι : Type v} [fintype ι] : finrank R (ι → R) = card ι :=
by { simp [finrank, sum_const_eq_lift_mul] }

/-- The finrank of the direct sum is the sum of the finranks. -/
@[simp] lemma finrank_direct_sum  {ι : Type v} [fintype ι] (M : ι → Type w)
  [Π (i : ι), add_comm_group (M i)] [Π (i : ι), module R (M i)] [Π (i : ι), module.free R (M i)]
  [Π (i : ι), module.finite R (M i)] : finrank R (⨁ i, M i) = ∑ i, finrank R (M i) :=
begin
  letI := nontrivial_of_invariant_basis_number R,
  simp [finrank, λ i, rank_eq_card_choose_basis_index R (M i)],
end

/-- The finrank of `M × N` is `(finrank R M) + (finrank R N)`. -/
@[simp] lemma finrank_prod : finrank R (M × N) = (finrank R M) + (finrank R N) :=
by { simp [finrank, rank_lt_omega R M, rank_lt_omega R N] }

/-- The finrank of a finite product is the sum of the finranks. -/
--TODO: this should follow from `linear_equiv.finrank_eq`, that is over a field.
lemma finrank_pi_fintype {ι : Type v} [fintype ι] {M : ι → Type w}
  [Π (i : ι), add_comm_group (M i)] [Π (i : ι), module R (M i)] [Π (i : ι), module.free R (M i)]
  [Π (i : ι), module.finite R (M i)] : finrank R (Π i, M i) = ∑ i, finrank R (M i) :=
begin
  letI := nontrivial_of_invariant_basis_number R,
  simp [finrank, λ i, rank_eq_card_choose_basis_index R (M i)]
end

/-- If `n` and `m` are `fintype`, the finrank of `n × m` matrices is
  `(fintype.card n) * (fintype.card m)`. -/
lemma finrank_matrix (n : Type v) [fintype n] (m : Type w) [fintype m] :
  finrank R (matrix n m R) = (card n) * (card m) :=
by { simp [finrank] }

end ring

section comm_ring

variables [comm_ring R] [strong_rank_condition R]
variables [add_comm_group M] [module R M] [module.free R M] [module.finite R M]
variables [add_comm_group N] [module R N] [module.free R N] [module.finite R N]

/-- The finrank of `M →ₗ[R] N` is `(finrank R M) * (finrank R N)`. -/
--TODO: this should follow from `linear_equiv.finrank_eq`, that is over a field.
lemma finrank_linear_hom : finrank R (M →ₗ[R] N) = (finrank R M) * (finrank R N) :=
begin
  classical,
  letI := nontrivial_of_invariant_basis_number R,
  have h := (linear_map.to_matrix (choose_basis R M) (choose_basis R N)),
  let b := (matrix.std_basis _ _ _).map h.symm,
  rw [finrank, dim_eq_card_basis b, ← fintype_card, mk_to_nat_eq_card, finrank, finrank,
    rank_eq_card_choose_basis_index, rank_eq_card_choose_basis_index, mk_to_nat_eq_card,
    mk_to_nat_eq_card, card_prod, mul_comm]
end

/-- The finrank of `M ⊗[R] N` is `(finrank R M) * (finrank R N)`. -/
@[simp] lemma finrank_tensor_product (M : Type v) (N : Type w) [add_comm_group M] [module R M]
  [module.free R M] [add_comm_group N] [module R N] [module.free R N] :
finrank R (M ⊗[R] N) = (finrank R M) * (finrank R N) :=
by { simp [finrank] }

end comm_ring

end module.free
