import analysis.normed_space.matrix_exponential

variables (𝕂 : Type*) {m n p : Type*} {n' : m → Type*} {𝔸 : Type*}

variables [is_R_or_C 𝕂]
  [fintype m] [decidable_eq m]
  [fintype n] [decidable_eq n]
  [Π i, fintype (n' i)] [Π i, decidable_eq (n' i)]
  [normed_comm_ring 𝔸] [normed_algebra 𝕂 𝔸] [complete_space 𝔸]

namespace matrix

open_locale matrix big_operators

lemma det_exp' (m : ℕ) (A : matrix (fin m) (fin m) 𝔸) :
  det (exp 𝕂 A) = exp 𝕂 (trace A) :=
begin
  simp_rw [trace, exp_sum, det_apply],
  induction m with m ih generalizing A,
  { simp_rw [fintype.prod_empty, fintype.sum_unique, equiv.perm.default_eq, equiv.perm.sign_one,
      one_smul], },
  { simp_rw [fin.prod_univ_succ],
    have := ih (A.submatrix fin.succ fin.succ),
    erw ←this,
    rw [finset.univ_perm_fin_succ, finset.sum_map, ←finset.univ_product_univ, finset.sum_product,
      fin.sum_univ_succ],
    simp_rw [equiv.to_embedding_apply, equiv.perm.decompose_fin_symm_apply_zero,
      equiv.perm.decompose_fin_symm_apply_succ,
      ←mul_smul_comm, matrix.diag, ←finset.mul_sum],

      }
end

#check perm.univ

lemma det_exp (A : matrix m m 𝔸) : det (exp 𝕂 A : matrix m m 𝔸) = exp 𝕂 (trace A) :=
begin
  have : ∀ (A : matrix m m 𝔸) (k : 𝕂) i j, (k • A) i j = k • A i j := λ _ _ _ _, rfl,
  simp_rw [trace, exp_sum, exp_eq_tsum, det_apply],
  rw tsum_mul_tsum
end

end matrix

#check matrix.has_smul
