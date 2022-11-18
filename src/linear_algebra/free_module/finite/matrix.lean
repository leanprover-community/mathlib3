/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import linear_algebra.finrank
import linear_algebra.free_module.finite.basic
import linear_algebra.matrix.to_lin

/-!
# Finite and free modules using matrices

We provide some instances for finite and free modules involving matrices.

## Main results

* `module.free.linear_map` : if `M` and `N` are finite and free, then `M →ₗ[R] N` is free.
* `module.finite.of_basis` : A free module with a basis indexed by a `fintype` is finite.
* `module.finite.linear_map` : if `M` and `N` are finite and free, then `M →ₗ[R] N`
  is finite.
-/

universes u v w

variables (R : Type u) (M : Type v) (N : Type w)

namespace module.free

section comm_ring

variables [comm_ring R] [add_comm_group M] [module R M] [module.free R M]
variables [add_comm_group N] [module R N] [module.free R N]

instance linear_map [module.finite R M] [module.finite R N] : module.free R (M →ₗ[R] N) :=
begin
  casesI subsingleton_or_nontrivial R,
  { apply module.free.of_subsingleton' },
  classical,
  exact of_equiv
    (linear_map.to_matrix (module.free.choose_basis R M) (module.free.choose_basis R N)).symm,
end

variables {R}

instance _root_.module.finite.linear_map [module.finite R M] [module.finite R N] :
  module.finite R (M →ₗ[R] N) :=
begin
  casesI subsingleton_or_nontrivial R,
  { apply_instance },
  classical,
  have f := (linear_map.to_matrix (choose_basis R M) (choose_basis R N)).symm,
  exact module.finite.of_surjective f.to_linear_map (linear_equiv.surjective f),
end

end comm_ring

section integer

variables [add_comm_group M] [module.finite ℤ M] [module.free ℤ M]
variables [add_comm_group N] [module.finite ℤ N] [module.free ℤ N]

instance _root_.module.finite.add_monoid_hom : module.finite ℤ (M →+ N) :=
module.finite.equiv (add_monoid_hom_lequiv_int ℤ).symm

instance add_monoid_hom : module.free ℤ (M →+ N) :=
begin
  letI : module.free ℤ (M →ₗ[ℤ] N) := module.free.linear_map _ _ _,
  exact module.free.of_equiv (add_monoid_hom_lequiv_int ℤ).symm
end

end integer

section comm_ring

open finite_dimensional

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
  rw [finrank, dim_eq_card_basis b, ← cardinal.mk_fintype, cardinal.mk_to_nat_eq_card, finrank,
    finrank, rank_eq_card_choose_basis_index, rank_eq_card_choose_basis_index,
    cardinal.mk_to_nat_eq_card, cardinal.mk_to_nat_eq_card, fintype.card_prod, mul_comm]
end

end comm_ring

end module.free
