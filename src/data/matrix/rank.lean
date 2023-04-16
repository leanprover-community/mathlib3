/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import linear_algebra.free_module.finite.rank
import linear_algebra.matrix.to_lin
import linear_algebra.finite_dimensional
import linear_algebra.matrix.dot_product
import data.complex.module

/-!
# Rank of matrices

The rank of a matrix `A` is defined to be the rank of range of the linear map corresponding to `A`.
This definition does not depend on the choice of basis, see `matrix.rank_eq_finrank_range_to_lin`.

## Main declarations

* `matrix.rank`: the rank of a matrix

## TODO

* Show that `matrix.rank` is equal to the row-rank, and that `rank Aᵀ = rank A`.

-/

open_locale matrix

namespace matrix

open finite_dimensional

variables {l m n o R : Type*} [m_fin : fintype m] [fintype n] [fintype o]

section comm_ring
variables [comm_ring R]

/-- The rank of a matrix is the rank of its image. -/
noncomputable def rank (A : matrix m n R) : ℕ := finrank R A.mul_vec_lin.range

@[simp] lemma rank_one [strong_rank_condition R] [decidable_eq n] :
  rank (1 : matrix n n R) = fintype.card n :=
by rw [rank, mul_vec_lin_one, linear_map.range_id, finrank_top, finrank_pi]

@[simp] lemma rank_zero [nontrivial R] : rank (0 : matrix m n R) = 0 :=
by rw [rank, mul_vec_lin_zero, linear_map.range_zero, finrank_bot]

lemma rank_le_card_width [strong_rank_condition R] (A : matrix m n R) : A.rank ≤ fintype.card n :=
begin
  haveI : module.finite R (n → R) := module.finite.pi,
  haveI : module.free R (n → R) := module.free.pi _ _,
  exact A.mul_vec_lin.finrank_range_le.trans_eq (finrank_pi _)
end

lemma rank_le_width [strong_rank_condition R] {m n : ℕ} (A : matrix (fin m) (fin n) R) :
  A.rank ≤ n :=
A.rank_le_card_width.trans $ (fintype.card_fin n).le

lemma rank_mul_le_left [strong_rank_condition R] (A : matrix m n R) (B : matrix n o R) :
  (A ⬝ B).rank ≤ A.rank :=
begin
  rw [rank, rank, mul_vec_lin_mul],
  exact cardinal.to_nat_le_of_le_of_lt_aleph_0
    (rank_lt_aleph_0 _ _) (linear_map.rank_comp_le_left _ _),
end

include m_fin

lemma rank_mul_le_right [strong_rank_condition R] (A : matrix l m R) (B : matrix m n R) :
  (A ⬝ B).rank ≤ B.rank :=
begin
  rw [rank, rank, mul_vec_lin_mul],
  exact finrank_le_finrank_of_rank_le_rank
    (linear_map.lift_rank_comp_le_right _ _) (rank_lt_aleph_0 _ _),
end

omit m_fin

lemma rank_mul_le [strong_rank_condition R] (A : matrix m n R) (B : matrix n o R) :
  (A ⬝ B).rank ≤ min A.rank B.rank :=
le_min (rank_mul_le_left _ _) (rank_mul_le_right _ _)

lemma rank_unit [strong_rank_condition R] [decidable_eq n] (A : (matrix n n R)ˣ) :
  (A : matrix n n R).rank = fintype.card n :=
begin
  refine le_antisymm (rank_le_card_width A) _,
  have := rank_mul_le_left (A : matrix n n R) (↑A⁻¹ : matrix n n R),
  rwa [← mul_eq_mul, ← units.coe_mul, mul_inv_self, units.coe_one, rank_one] at this,
end

lemma rank_of_is_unit [strong_rank_condition R] [decidable_eq n] (A : matrix n n R)
  (h : is_unit A) :
  A.rank = fintype.card n :=
by { obtain ⟨A, rfl⟩ := h, exact rank_unit A }

/-- Taking a subset of the rows and permuting the columns reduces the rank. -/
lemma rank_submatrix_le [strong_rank_condition R] [fintype m] (f : n → m) (e : n ≃ m)
  (A : matrix m m R) :
  rank (A.submatrix f e) ≤ rank A :=
begin
  rw [rank, rank, mul_vec_lin_submatrix, linear_map.range_comp, linear_map.range_comp,
    (show linear_map.fun_left R R e.symm = linear_equiv.fun_congr_left R R e.symm, from rfl),
    linear_equiv.range, submodule.map_top],
  -- TODO: generalize `finite_dimensional.finrank_map_le` and use it here
  exact finrank_le_finrank_of_rank_le_rank (lift_rank_map_le _ _) (rank_lt_aleph_0 _ _),
end

lemma rank_reindex [fintype m] (e₁ e₂ : m ≃ n) (A : matrix m m R) :
  rank (reindex e₁ e₂ A) = rank A :=
by rw [rank, rank, mul_vec_lin_reindex, linear_map.range_comp, linear_map.range_comp,
    linear_equiv.range, submodule.map_top, linear_equiv.finrank_map_eq]

@[simp] lemma rank_submatrix [fintype m] (A : matrix m m R) (e₁ e₂ : n ≃ m) :
  rank (A.submatrix e₁ e₂) = rank A :=
by simpa only [reindex_apply] using rank_reindex e₁.symm e₂.symm A

include m_fin

lemma rank_eq_finrank_range_to_lin [decidable_eq n]
  {M₁ M₂ : Type*} [add_comm_group M₁] [add_comm_group M₂]
  [module R M₁] [module R M₂] (A : matrix m n R) (v₁ : basis m R M₁) (v₂ : basis n R M₂) :
  A.rank = finrank R (to_lin v₂ v₁ A).range :=
begin
  let e₁ := (pi.basis_fun R m).equiv v₁ (equiv.refl _),
  let e₂ := (pi.basis_fun R n).equiv v₂ (equiv.refl _),
  have range_e₂ : (e₂ : (n → R) →ₗ[R] M₂).range = ⊤,
  { rw linear_map.range_eq_top, exact e₂.surjective },
  refine linear_equiv.finrank_eq (e₁.of_submodules _ _ _),
  rw [← linear_map.range_comp, ← linear_map.range_comp_of_range_eq_top (to_lin v₂ v₁ A) range_e₂],
  congr' 1,
  apply linear_map.pi_ext', rintro i, apply linear_map.ext_ring,
  have aux₁ := to_lin_self (pi.basis_fun R n) (pi.basis_fun R m) A i,
  have aux₂ := basis.equiv_apply (pi.basis_fun R n) i v₂,
  rw [to_lin_eq_to_lin', to_lin'_apply'] at aux₁,
  rw [pi.basis_fun_apply, linear_map.coe_std_basis] at aux₁ aux₂,
  simp only [linear_map.comp_apply, e₁, e₂, linear_equiv.coe_coe, equiv.refl_apply, aux₁, aux₂,
    linear_map.coe_single, to_lin_self, linear_equiv.map_sum, linear_equiv.map_smul,
    basis.equiv_apply],
end

lemma rank_le_card_height [strong_rank_condition R] (A : matrix m n R) :
  A.rank ≤ fintype.card m :=
begin
  haveI : module.finite R (m → R) := module.finite.pi,
  haveI : module.free R (m → R) := module.free.pi _ _,
  exact (submodule.finrank_le _).trans (finrank_pi R).le
end

omit m_fin

lemma rank_le_height [strong_rank_condition R] {m n : ℕ} (A : matrix (fin m) (fin n) R) :
  A.rank ≤ m :=
A.rank_le_card_height.trans $ (fintype.card_fin m).le

/-- The rank of a matrix is the rank of the space spanned by its columns. -/
lemma rank_eq_finrank_span_cols (A : matrix m n R) :
  A.rank = finrank R (submodule.span R (set.range Aᵀ)) :=
by rw [rank, matrix.range_mul_vec_lin]

end comm_ring

section field
variables [fintype m]

lemma rank_conj_transpose_mul_self [field R] [partial_order R] [star_ordered_ring R]
  (A : matrix m n R) :
  (Aᴴ ⬝ A).rank = A.rank :=
begin
  have : linear_map.ker (mul_vec_lin A) = linear_map.ker (Aᴴ ⬝ A).mul_vec_lin,
  { ext x,
    simp only [linear_map.mem_ker, mul_vec_lin_apply, ←mul_vec_mul_vec],
    split,
    { intro h, rw [h, mul_vec_zero] },
    { intro h,
      replace h := congr_arg (dot_product (star x)) h,
      rwa [dot_product_mul_vec, dot_product_zero, vec_mul_conj_transpose, star_star,
        dot_product_star_self_eq_zero] at h } },
  dunfold rank,
  refine add_left_injective (finrank R (A.mul_vec_lin).ker) _,
  dsimp only,
  rw [linear_map.finrank_range_add_finrank_ker,
    ←((Aᴴ ⬝ A).mul_vec_lin).finrank_range_add_finrank_ker],
  congr' 1,
  rw this,
end

lemma rank_transpose_mul_self [linear_ordered_field R] (A : matrix m n R) :
  (Aᵀ ⬝ A).rank = A.rank :=
begin
  have : linear_map.ker (mul_vec_lin A) = linear_map.ker (Aᵀ ⬝ A).mul_vec_lin,
  { ext x,
    simp only [linear_map.mem_ker, mul_vec_lin_apply, ←mul_vec_mul_vec],
    split,
    { intro h, rw [h, mul_vec_zero] },
    { intro h,
      replace h := congr_arg (dot_product x) h,
      rwa [dot_product_mul_vec, dot_product_zero, vec_mul_transpose,
        dot_product_self_eq_zero] at h } },
  dunfold rank,
  refine add_left_injective (finrank R (A.mul_vec_lin).ker) _,
  dsimp only,
  rw [linear_map.finrank_range_add_finrank_ker,
    ←((Aᵀ ⬝ A).mul_vec_lin).finrank_range_add_finrank_ker],
  congr' 1,
  rw this,
end


lemma rank_transpose [linear_ordered_field R] (A : matrix m n R) :
  Aᵀ.rank = A.rank :=
begin
  apply le_antisymm,
  sorry,
  sorry,
end

end field

end matrix
