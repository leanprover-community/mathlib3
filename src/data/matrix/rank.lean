import linear_algebra.free_module.finite.rank

/-!
# Rank of matrices
-/

namespace matrix

open finite_dimensional

variables {m n K : Type*} [fintype m] [fintype n] [decidable_eq n] [field K]
variables (A : matrix m n K)

/-- The rank of a matrix is the rank of its image. -/
noncomputable def rank : ℕ := finrank K A.to_lin'.range

lemma rank_eq_finrank_range_to_lin
  {M₁ M₂ : Type*} [add_comm_group M₁] [add_comm_group M₂]
  [module K M₁] [module K M₂] (v₁ : basis m K M₁) (v₂ : basis n K M₂) :
  A.rank = finrank K (to_lin v₂ v₁ A).range :=
begin
  let e₁ := (pi.basis_fun K m).equiv v₁ (equiv.refl _),
  let e₂ := (pi.basis_fun K n).equiv v₂ (equiv.refl _),
  have range_e₂ : (e₂ : (n → K) →ₗ[K] M₂).range = ⊤,
  { rw linear_map.range_eq_top, exact e₂.surjective },
  refine linear_equiv.finrank_eq (e₁.of_submodules _ _ _),
  rw [← linear_map.range_comp, ← linear_map.range_comp_of_range_eq_top (to_lin v₂ v₁ A) range_e₂],
  congr' 1,
  apply linear_map.pi_ext', rintro i, apply linear_map.ext_ring,
  have aux₁ := to_lin_self (pi.basis_fun K n) (pi.basis_fun K m) A i,
  have aux₂ := basis.equiv_apply (pi.basis_fun K n) i v₂,
  rw [to_lin_eq_to_lin'] at aux₁,
  rw [pi.basis_fun_apply, linear_map.coe_std_basis] at aux₁ aux₂,
  simp only [linear_map.comp_apply, e₁, e₂, linear_equiv.coe_coe, equiv.refl_apply, aux₁, aux₂,
    linear_map.coe_single, to_lin_self, linear_equiv.map_sum, linear_equiv.map_smul,
    basis.equiv_apply],
end

lemma rank_le_card_height : A.rank ≤ fintype.card m :=
(submodule.finrank_le _).trans (module.free.finrank_pi K).le

lemma rank_le_card_width : A.rank ≤ fintype.card n :=
begin
  convert nat.le_of_add_le_left (A.to_lin'.finrank_range_add_finrank_ker).le,
  exact (module.free.finrank_pi K).symm,
end

lemma rank_le_height {m n : ℕ} (A : matrix (fin m) (fin n) K) : A.rank ≤ m :=
A.rank_le_card_height.trans $ (fintype.card_fin m).le

lemma rank_le_width {m n : ℕ} (A : matrix (fin m) (fin n) K) : A.rank ≤ n :=
A.rank_le_card_width.trans $ (fintype.card_fin n).le

end matrix
