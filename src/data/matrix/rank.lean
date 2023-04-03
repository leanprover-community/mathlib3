/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import linear_algebra.free_module.finite.rank
import linear_algebra.matrix.to_lin

/-!
# Rank of matrices

The rank of a matrix `A` is defined to be the rank of range of the linear map corresponding to `A`.
This definition does not depend on the choice of basis, see `matrix.rank_eq_finrank_range_to_lin`.

## Main declarations

* `matrix.rank`: the rank of a matrix

## TODO

* Show that `matrix.rank` is equal to the row-rank and column-rank
* Generalize more results away from fields

-/

open_locale matrix

namespace matrix

open finite_dimensional

variables {m n o R K : Type*} [m_fin : fintype m] [fintype n] [fintype o]
variables [decidable_eq n] [decidable_eq o] [comm_ring R] [field K]

/-- The rank of a matrix is the rank of its image. -/
noncomputable def rank (A : matrix m n R) : ℕ := finrank R A.to_lin'.range

@[simp] lemma rank_one [strong_rank_condition R] : rank (1 : matrix n n R) = fintype.card n :=
by rw [rank, to_lin'_one, linear_map.range_id, finrank_top, module.free.finrank_pi]

@[simp] lemma rank_zero [nontrivial R] : rank (0 : matrix m n R) = 0 :=
by rw [rank, linear_equiv.map_zero, linear_map.range_zero, finrank_bot]

lemma rank_le_card_width [strong_rank_condition R] (A : matrix m n R) : A.rank ≤ fintype.card n :=
begin
  haveI : module.finite R (n → R) := module.finite.pi,
  haveI : module.free R (n → R) := module.free.pi _ _,
  exact A.to_lin'.finrank_range_le.trans_eq (module.free.finrank_pi _)
end

lemma rank_le_width [strong_rank_condition R] {m n : ℕ} (A : matrix (fin m) (fin n) R) :
  A.rank ≤ n :=
A.rank_le_card_width.trans $ (fintype.card_fin n).le

lemma rank_mul_le (A : matrix m n K) (B : matrix n o K) :
  (A ⬝ B).rank ≤ A.rank :=
begin
  refine linear_map.finrank_le_finrank_of_injective (submodule.of_le_injective _),
  rw [to_lin'_mul],
  exact linear_map.range_comp_le_range _ _,
end

lemma rank_unit (A : (matrix n n K)ˣ) :
  (A : matrix n n K).rank = fintype.card n :=
begin
  refine le_antisymm (rank_le_card_width A) _,
  have := rank_mul_le (A : matrix n n K) (↑A⁻¹ : matrix n n K),
  rwa [← mul_eq_mul, ← units.coe_mul, mul_inv_self, units.coe_one, rank_one] at this,
end

lemma rank_of_is_unit (A : matrix n n K) (h : is_unit A) :
  A.rank = fintype.card n :=
by { obtain ⟨A, rfl⟩ := h, exact rank_unit A }

include m_fin

lemma rank_eq_finrank_range_to_lin
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
  rw [to_lin_eq_to_lin'] at aux₁,
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
  exact (submodule.finrank_le _).trans (module.free.finrank_pi R).le
end

omit m_fin

lemma rank_le_height [strong_rank_condition R] {m n : ℕ} (A : matrix (fin m) (fin n) R) :
  A.rank ≤ m :=
A.rank_le_card_height.trans $ (fintype.card_fin m).le

end matrix
