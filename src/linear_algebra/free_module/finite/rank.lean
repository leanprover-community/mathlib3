/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import linear_algebra.finrank
import linear_algebra.free_module.rank
import linear_algebra.free_module.finite.basic

/-!

# Rank of finite free modules

This is a basic API for the rank of finite free modules.

-/

--TODO: many results from `linear_algebra/finite_dimensional` should be moved here.

universes u v w

variables (R : Type u) (M : Type v) (N : Type w)

open_locale tensor_product direct_sum big_operators cardinal

open cardinal finite_dimensional fintype

namespace finite_dimensional
open module.free

section ring
variables [ring R]
variables [add_comm_group M] [module R M]
variables [add_comm_group N] [module R N]

@[simp]
lemma submodule.finrank_map_subtype_eq (p : submodule R M) (q : submodule R p) :
  finrank R (q.map p.subtype) = finrank R q :=
(submodule.equiv_subtype_map p q).symm.finrank_eq

end ring

section ring_finite

variables [ring R] [strong_rank_condition R]
variables [add_comm_group M] [module R M] [module.finite R M]
variables [add_comm_group N] [module R N] [module.finite R N]

/-- The rank of a finite module is finite. -/
lemma rank_lt_aleph_0 : module.rank R M < ℵ₀ :=
begin
  dunfold module.rank,
  letI := nontrivial_of_invariant_basis_number R,
  obtain ⟨S, hS⟩ := module.finite_def.mp ‹_›,
  refine (csupr_le' $ λ i, _).trans_lt (nat_lt_aleph_0 S.card),
  exact linear_independent_le_span_finset _ i.prop S hS,
end

/-- If `M` is finite, `finrank M = rank M`. -/
@[simp] lemma finrank_eq_rank : ↑(finrank R M) = module.rank R M :=
by { rw [finrank, cast_to_nat_of_lt_aleph_0 (rank_lt_aleph_0 R M)] }

end ring_finite

section ring_free

variables [ring R] [strong_rank_condition R]
variables [add_comm_group M] [module R M] [module.free R M] [module.finite R M]
variables [add_comm_group N] [module R N] [module.free R N] [module.finite R N]

/-- The finrank of a free module `M` over `R` is the cardinality of `choose_basis_index R M`. -/
lemma finrank_eq_card_choose_basis_index : finrank R M = @card (choose_basis_index R M)
  (@choose_basis_index.fintype R M _ _ _ _ (nontrivial_of_invariant_basis_number R) _) :=
begin
  letI := nontrivial_of_invariant_basis_number R,
  simp [finrank, rank_eq_card_choose_basis_index]
end

/-- The finrank of `(ι →₀ R)` is `fintype.card ι`. -/
@[simp] lemma finrank_finsupp {ι : Type v} [fintype ι] : finrank R (ι →₀ R) = card ι :=
by { rw [finrank, rank_finsupp_self, ← mk_to_nat_eq_card, to_nat_lift] }

/-- The finrank of `(ι → R)` is `fintype.card ι`. -/
lemma finrank_pi {ι : Type v} [fintype ι] : finrank R (ι → R) = card ι :=
by simp [finrank]

/-- The finrank of the direct sum is the sum of the finranks. -/
@[simp] lemma finrank_direct_sum  {ι : Type v} [fintype ι] (M : ι → Type w)
  [Π (i : ι), add_comm_group (M i)] [Π (i : ι), module R (M i)] [Π (i : ι), module.free R (M i)]
  [Π (i : ι), module.finite R (M i)] : finrank R (⨁ i, M i) = ∑ i, finrank R (M i) :=
begin
  letI := nontrivial_of_invariant_basis_number R,
  simp only [finrank, λ i, rank_eq_card_choose_basis_index R (M i), rank_direct_sum,
    ← mk_sigma, mk_to_nat_eq_card, card_sigma],
end

/-- The finrank of `M × N` is `(finrank R M) + (finrank R N)`. -/
@[simp] lemma finrank_prod : finrank R (M × N) = (finrank R M) + (finrank R N) :=
by { simp [finrank, rank_lt_aleph_0 R M, rank_lt_aleph_0 R N] }

/-- The finrank of a finite product is the sum of the finranks. -/
--TODO: this should follow from `linear_equiv.finrank_eq`, that is over a field.
lemma finrank_pi_fintype {ι : Type v} [fintype ι] {M : ι → Type w}
  [Π (i : ι), add_comm_group (M i)] [Π (i : ι), module R (M i)] [Π (i : ι), module.free R (M i)]
  [Π (i : ι), module.finite R (M i)] : finrank R (Π i, M i) = ∑ i, finrank R (M i) :=
begin
  letI := nontrivial_of_invariant_basis_number R,
  simp only [finrank, λ i, rank_eq_card_choose_basis_index R (M i), rank_pi,
    ← mk_sigma, mk_to_nat_eq_card, card_sigma],
end

/-- If `m` and `n` are `fintype`, the finrank of `m × n` matrices is
  `(fintype.card m) * (fintype.card n)`. -/
lemma finrank_matrix (m n : Type*) [fintype m] [fintype n] :
  finrank R (matrix m n R) = (card m) * (card n) :=
by { simp [finrank] }

variables {R M N}

/-- Two finite and free modules are isomorphic if they have the same (finite) rank. -/
theorem nonempty_linear_equiv_of_finrank_eq
  (cond : finrank R M = finrank R N) : nonempty (M ≃ₗ[R] N) :=
nonempty_linear_equiv_of_lift_rank_eq $ by simp only [← finrank_eq_rank, cond, lift_nat_cast]

/-- Two finite and free modules are isomorphic if and only if they have the same (finite) rank. -/
theorem nonempty_linear_equiv_iff_finrank_eq :
  nonempty (M ≃ₗ[R] N) ↔ finrank R M = finrank R N :=
⟨λ ⟨h⟩, h.finrank_eq, λ h, nonempty_linear_equiv_of_finrank_eq h⟩

variables (M N)

/-- Two finite and free modules are isomorphic if they have the same (finite) rank. -/
noncomputable def _root_.linear_equiv.of_finrank_eq (cond : finrank R M = finrank R N) :
  M ≃ₗ[R] N :=
classical.choice $ nonempty_linear_equiv_of_finrank_eq cond

end ring_free

section comm_ring

variables [comm_ring R] [strong_rank_condition R]
variables [add_comm_group M] [module R M] [module.free R M] [module.finite R M]
variables [add_comm_group N] [module R N] [module.free R N] [module.finite R N]

/-- The finrank of `M ⊗[R] N` is `(finrank R M) * (finrank R N)`. -/
@[simp] lemma finrank_tensor_product (M : Type v) (N : Type w) [add_comm_group M] [module R M]
  [module.free R M] [add_comm_group N] [module R N] [module.free R N] :
  finrank R (M ⊗[R] N) = (finrank R M) * (finrank R N) :=
by { simp [finrank] }

end comm_ring

end finite_dimensional

section
open finite_dimensional

variables {R M N}
variables [ring R] [strong_rank_condition R]
variables [add_comm_group M] [module R M]
variables [add_comm_group N] [module R N]

lemma linear_map.finrank_le_finrank_of_injective [module.finite R N] {f : M →ₗ[R] N}
  (hf : function.injective f) : finrank R M ≤ finrank R N :=
finrank_le_finrank_of_rank_le_rank
  (linear_map.lift_rank_le_of_injective _ hf) (rank_lt_aleph_0 _ _)

lemma linear_map.finrank_range_le [module.finite R M] (f : M →ₗ[R] N) :
  finrank R f.range ≤ finrank R M :=
finrank_le_finrank_of_rank_le_rank (lift_rank_range_le f) (rank_lt_aleph_0 _ _)

/-- The dimension of a submodule is bounded by the dimension of the ambient space. -/
lemma submodule.finrank_le [module.finite R M] (s : submodule R M) :
  finrank R s ≤ finrank R M :=
by simpa only [cardinal.to_nat_lift] using to_nat_le_of_le_of_lt_aleph_0
  (rank_lt_aleph_0 _ _) (rank_submodule_le s)

/-- The dimension of a quotient is bounded by the dimension of the ambient space. -/
lemma submodule.finrank_quotient_le [module.finite R M] (s : submodule R M) :
  finrank R (M ⧸ s) ≤ finrank R M :=
by simpa only [cardinal.to_nat_lift] using to_nat_le_of_le_of_lt_aleph_0
  (rank_lt_aleph_0 _ _) ((submodule.mkq s).rank_le_of_surjective (surjective_quot_mk _))

/-- Pushforwards of finite submodules have a smaller finrank. -/
lemma submodule.finrank_map_le (f : M →ₗ[R] N) (p : submodule R M) [module.finite R p] :
  finrank R (p.map f) ≤ finrank R p :=
finrank_le_finrank_of_rank_le_rank (lift_rank_map_le _ _) (rank_lt_aleph_0 _ _)

lemma submodule.finrank_le_finrank_of_le {s t : submodule R M} [module.finite R t]
  (hst : s ≤ t) : finrank R s ≤ finrank R t :=
calc finrank R s = finrank R (s.comap t.subtype)
      : (submodule.comap_subtype_equiv_of_le hst).finrank_eq.symm
... ≤ finrank R t : submodule.finrank_le _

end
