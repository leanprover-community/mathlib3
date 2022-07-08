import analysis.inner_product_space.gram_schmidt_ortho
import linear_algebra.matrix.pos_def

namespace matrix

open_locale matrix
open matrix

--TODO: move
variables {m n α : Type*} [fintype n] [decidable_eq n] (A : matrix n n α) [comm_ring α] [star_ring α]

noncomputable lemma invertible_conj_transpose [invertible A] : invertible Aᴴ :=
by apply_instance

noncomputable lemma invertible_transpose [invertible A] : invertible Aᵀ :=
begin
  haveI : invertible Aᵀ.det, {
    simp,
    apply det_invertible_of_invertible,
  },
  exact invertible_of_det_invertible Aᵀ
end

noncomputable lemma invertible_of_invertible_conj_transpose [invertible Aᴴ] : invertible A :=
begin
  rw ←conj_transpose_conj_transpose A,
  exact matrix.invertible_conj_transpose Aᴴ
end


lemma mul_mul_apply (A B C : matrix n n α) (i j : n) : (A ⬝ B ⬝ C) i j = A i ⬝ᵥ (B.mul_vec (Cᵀ j)) :=
by { rw matrix.mul_assoc, simpa only [mul_apply, dot_product, mul_vec] }

end matrix


namespace basis
open matrix

variables {ι ι' : Type*} {R : Type*} {M : Type*} [comm_ring R] [add_comm_monoid M] [module R M]
noncomputable lemma invertible_to_matrix (b : basis ι R M) (b' : basis ι R M) [decidable_eq ι] [fintype ι]  :
  invertible (b.to_matrix b') :=
invertible_of_left_inverse _ _ (basis.to_matrix_mul_to_matrix_flip _ _)

end basis

variables {𝕜 : Type*} [is_R_or_C 𝕜]
  {n : Type*} [linear_order n] [is_well_order n (<)] [locally_finite_order_bot n]

local notation `⟪`x`, `y`⟫` := @inner 𝕜 (n → 𝕜) (pi_Lp.inner_product_space (λ _, 𝕜)).to_has_inner x y
open matrix
open_locale matrix
variables {S : matrix n n 𝕜} [fintype n] (hS : S.pos_def)



#check basis.mk

noncomputable def LDL.L_inv : matrix n n 𝕜 :=
  @gram_schmidt
    𝕜 (n → 𝕜) _ (inner_product_space.of_matrix hS.transpose) n _ _ _ (λ k, pi.basis_fun 𝕜 n k)


lemma LDL.L_inv_eq_gram_schmidt_basis :
  LDL.L_inv hS = ((pi.basis_fun 𝕜 n).to_matrix
    (@gram_schmidt_basis 𝕜 (n → 𝕜) _
    (inner_product_space.of_matrix hS.transpose) n _ _ _ (pi.basis_fun 𝕜 n)))ᵀ :=
begin
  ext i j,
  rw [LDL.L_inv, basis.coe_pi_basis_fun.to_matrix_eq_transpose, coe_gram_schmidt_basis],
  refl
end

noncomputable instance LDL.invertible_L_inv : invertible (LDL.L_inv hS) :=
begin
  rw [LDL.L_inv_eq_gram_schmidt_basis],
  haveI := basis.invertible_to_matrix (pi.basis_fun 𝕜 n)
    (@gram_schmidt_basis 𝕜 (n → 𝕜) _ (inner_product_space.of_matrix hS.transpose) n _ _ _ (pi.basis_fun 𝕜 n)),
  apply invertible_transpose,
end

lemma LDL.L_inv_orthogonal₀ {i j : n} (h₀ : i ≠ j) : @inner 𝕜 (n → 𝕜) (inner_product_space.of_matrix hS.transpose).to_has_inner
    (LDL.L_inv hS i)
    (LDL.L_inv hS j) = 0 :=
  by apply gram_schmidt_orthogonal _ _ h₀

lemma LDL.L_inv_orthogonal {i j : n} (h₀ : i ≠ j) :
  ⟪(LDL.L_inv hS i), Sᵀ.mul_vec (LDL.L_inv hS j)⟫ = 0 :=
show @inner 𝕜 (n → 𝕜) (inner_product_space.of_matrix hS.transpose).to_has_inner
    (LDL.L_inv hS i)
    (LDL.L_inv hS j) = 0,
by apply gram_schmidt_orthogonal _ _ h₀

noncomputable def LDL.diag_entries : n → 𝕜 :=
  λ i, ⟪star (LDL.L_inv hS i), S.mul_vec (star (LDL.L_inv hS i))⟫

noncomputable def LDL.diag : matrix n n 𝕜 := matrix.diagonal (LDL.diag_entries hS)

lemma LDL.orthogonal_basis_triangular [succ_order n] {i j : n} (hij : i < j) :
  LDL.L_inv hS i j = 0 :=
by rw [← @gram_schmidt_triangular 𝕜 (n → 𝕜) _ (inner_product_space.of_matrix hS.transpose) n _ _ _
    i j hij (pi.basis_fun 𝕜 n), pi.basis_fun_repr, LDL.L_inv]


lemma ldl_decomposition₀ : LDL.diag hS = LDL.L_inv hS ⬝ S ⬝ (LDL.L_inv hS)ᴴ :=
begin
  ext i j,
  by_cases hij : i = j,
  { simpa only [hij, LDL.diag, diagonal_apply_eq, LDL.diag_entries, matrix.mul_assoc, inner,
      pi.star_apply, is_R_or_C.star_def, star_ring_end_self_apply],
  },
  { simp only [LDL.diag, hij, diagonal_apply_ne, ne.def, not_false_iff, mul_mul_apply],
    rw [conj_transpose, transpose_map, transpose_transpose, dot_product_mul_vec],
    rw [(LDL.L_inv_orthogonal hS (λ h : j = i, hij h.symm)).symm,
      ← inner_conj_sym],
    rw [mul_vec_transpose],
    show star (dot_product _ _) = _,
    rw [← star_dot_product_star, dot_product_comm],
    congr',
    rw ← is_R_or_C.star_def,
    unfold star,
    simp only [star_star], }
end

noncomputable def LDL.L := (LDL.L_inv hS)⁻¹

theorem ldl_decomposition :
  S = LDL.L hS ⬝ LDL.diag hS ⬝ (LDL.L hS)ᴴ :=
begin
  haveI : invertible (LDL.L_inv hS) := LDL.invertible_L_inv hS,
  haveI : invertible (LDL.L_inv hS)ᴴ := invertible_conj_transpose _,
  have := ldl_decomposition₀ hS,
  have := congr_arg (λ A, LDL.L hS ⬝ A) this,
  have := congr_arg (λ A, A ⬝ (LDL.L hS)ᴴ) this,
  simp [LDL.L, (matrix.mul_assoc _ _ _).symm] at this,
  have blah := (conj_transpose_nonsing_inv (LDL.L_inv hS)).symm,
  simp [(conj_transpose_nonsing_inv (LDL.L_inv hS)), matrix.mul_assoc] at this,
  simp [(conj_transpose_nonsing_inv (LDL.L_inv hS)).symm] at this,
  simp [matrix.mul_assoc, LDL.L, (conj_transpose_nonsing_inv (LDL.L_inv hS)).symm, this]
end
