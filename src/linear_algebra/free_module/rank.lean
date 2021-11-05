/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import linear_algebra.free_module.basic
import linear_algebra.finsupp_vector_space

/-!

# Rank of free modules

This is a basic API for the rank of free modules.

-/

universes u v w

variables (R : Type u) (M : Type v) (N : Type w)

open_locale tensor_product direct_sum big_operators cardinal

open cardinal

namespace module.free

section ring

variables [ring R] [strong_rank_condition R]
variables [add_comm_group M] [module R M] [module.free R M]
variables [add_comm_group N] [module R N] [module.free R N]

/-- The rank of a free module `M` over `R` is the cardinality of `choose_basis_index R M`. -/
lemma rank_eq_card_choose_basis_index : module.rank R M = #(choose_basis_index R M) :=
(choose_basis R M).mk_eq_dim''.symm

/-- The rank of `(ι →₀ R)` is `(# ι).lift`. -/
@[simp] lemma rank_finsupp {ι : Type v} : module.rank R (ι →₀ R) = (# ι).lift :=
by simpa [lift_id', lift_umax] using
  (basis.of_repr (linear_equiv.refl _ (ι →₀ R))).mk_eq_dim.symm

/-- If `R` and `ι` lie in the same universe, the rank of `(ι →₀ R)` is `# ι`. -/
lemma rank_finsupp' {ι : Type u} : module.rank R (ι →₀ R) = # ι := by simp

/-- The rank of `M × N` is `(module.rank R M).lift + (module.rank R N).lift`. -/
@[simp] lemma rank_prod :
  module.rank R (M × N) = lift.{w v} (module.rank R M) + lift.{v w} (module.rank R N) :=
by simpa [rank_eq_card_choose_basis_index R M, rank_eq_card_choose_basis_index R N,
  lift_umax, lift_umax'] using ((choose_basis R M).prod (choose_basis R N)).mk_eq_dim.symm

/-- If `M` and `N` lie in the same universe, the rank of `M × N` is
  `(module.rank R M) + (module.rank R N)`. -/
lemma rank_prod' (N : Type v) [add_comm_group N] [module R N] [module.free R N] :
  module.rank R (M × N) = (module.rank R M) + (module.rank R N) := by simp

/-- The rank of the direct sum is the sum of the ranks. -/
@[simp] lemma rank_direct_sum  {ι : Type v} (M : ι → Type w) [Π (i : ι), add_comm_group (M i)]
  [Π (i : ι), module R (M i)] [Π (i : ι), module.free R (M i)] :
  module.rank R (⨁ i, M i) = cardinal.sum (λ i, module.rank R (M i)) :=
begin
  let B := λ i, choose_basis R (M i),
  let b : basis _ R (⨁ i, M i) := dfinsupp.basis (λ i, B i),
  simp [← b.mk_eq_dim'', λ i, (B i).mk_eq_dim''],
end

/-- The rank of a finite product is the sum of the ranks. -/
@[simp] lemma rank_pi_fintype {ι : Type v} [fintype ι] {M : ι → Type w}
  [Π (i : ι), add_comm_group (M i)] [Π (i : ι), module R (M i)] [Π (i : ι), module.free R (M i)] :
  module.rank R (Π i, M i) = cardinal.sum (λ i, module.rank R (M i)) :=
by { rw [← (direct_sum.linear_equiv_fun_on_fintype _ _ M).dim_eq, rank_direct_sum] }

/-- If `n` and `m` are `fintype`, the rank of `n × m` matrices is `(# n).lift * (# m).lift`. -/
@[simp] lemma rank_matrix (n : Type v) [fintype n] (m : Type w) [fintype m] :
  module.rank R (matrix n m R) = (lift.{(max v w u) v} (# n)) * (lift.{(max v w u) w} (# m)) :=
begin
  have h := (matrix.std_basis R n m).mk_eq_dim,
  rw [← lift_lift.{(max v w u) (max v w)}, lift_inj] at h,
  simpa using h.symm,
end

/-- If `n` and `m` are `fintype` that lie in the same universe, the rank of `n × m` matrices is
  `(# n * # m).lift`. -/
@[simp] lemma rank_matrix' (n : Type v) [fintype n] (m : Type v) [fintype m] :
  module.rank R (matrix n m R) =  (# n * # m).lift :=
by rw [rank_matrix, lift_mul, lift_umax]

/-- If `n` and `m` are `fintype` that lie in the same universe as `R`, the rank of `n × m` matrices
  is `# n * # m`. -/
@[simp] lemma rank_matrix'' (n : Type u) [fintype n] (m : Type u) [fintype m] :
  module.rank R (matrix n m R) =  # n * # m := by simp

end ring

section comm_ring

variables [comm_ring R] [strong_rank_condition R]
variables [add_comm_group M] [module R M] [module.free R M]
variables [add_comm_group N] [module R N] [module.free R N]

/-- The rank of `M ⊗[R] N` is `(module.rank R M).lift * (module.rank R N).lift`. -/
@[simp] lemma rank_tensor_product : module.rank R (M ⊗[R] N) = lift.{w v} (module.rank R M) *
  lift.{v w} (module.rank R N) :=
begin
  let ιM := choose_basis_index R M,
  let ιN := choose_basis_index R N,

  have h₁ := linear_equiv.lift_dim_eq (tensor_product.congr (repr R M) (repr R N)),
  let b : basis (ιM × ιN) R (_ →₀ R) := finsupp.basis_single_one,
  rw [linear_equiv.dim_eq (finsupp_tensor_finsupp' R ιM ιN), ← b.mk_eq_dim, mk_prod] at h₁,
  rw [lift_inj.1 h₁, rank_eq_card_choose_basis_index R M, rank_eq_card_choose_basis_index R N],
end

/-- If `M` and `N` lie in the same universe, the rank of `M ⊗[R] N` is
  `(module.rank R M) * (module.rank R N)`. -/
lemma rank_tensor_product' (N : Type v) [add_comm_group N] [module R N] [module.free R N] :
  module.rank R (M ⊗[R] N) = (module.rank R M) * (module.rank R N) := by simp

end comm_ring

end module.free
