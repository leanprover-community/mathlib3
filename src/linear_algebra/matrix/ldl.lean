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

lemma inv_mul_eq_iff_eq_mul (A B C : matrix n n α) [invertible A]  : A⁻¹ ⬝ B = C ↔ B = A ⬝ C :=
⟨ λ h, calc B = A ⬝ A⁻¹ ⬝ B : by simp only [mul_inv_of_invertible A, matrix.one_mul]
    ... = A ⬝ C : by rw [matrix.mul_assoc, h],
  λ h, calc A⁻¹ ⬝ B = A⁻¹ ⬝ A ⬝ C : by rw [matrix.mul_assoc, h]
    ... = C : by simp only [inv_mul_of_invertible A, matrix.one_mul]⟩

lemma mul_inv_eq_iff_eq_mul (A B C : matrix n n α) [invertible A]  : B ⬝ A⁻¹ = C ↔ B = C ⬝ A :=
⟨ λ h, calc B = B ⬝ A⁻¹ ⬝ A : by simp only [matrix.mul_assoc, inv_mul_of_invertible A, matrix.mul_one]
    ... = C ⬝ A : by rw [h],
  λ h, calc B ⬝ A⁻¹ = C ⬝ A ⬝ A⁻¹ : by rw [h]
    ... = C : by simp only [matrix.mul_assoc, mul_inv_of_invertible A, matrix.mul_one]⟩

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

/-- The inverse of the lower triangular matrix `L` of the LDL-decomposition. It is obtained by
applying Gram-Schmidt-Orthogonalization w.r.t. the inner product induced by `Sᵀ` on the standard
basis vectors `pi.basis_fun`. -/
noncomputable def LDL.lower_inv : matrix n n 𝕜 :=
  @gram_schmidt
    𝕜 (n → 𝕜) _ (inner_product_space.of_matrix hS.transpose) n _ _ _ (λ k, pi.basis_fun 𝕜 n k)

lemma LDL.lower_inv_gram_schmidt_basis :
  LDL.lower_inv hS = ((pi.basis_fun 𝕜 n).to_matrix
    (@gram_schmidt_basis 𝕜 (n → 𝕜) _
    (inner_product_space.of_matrix hS.transpose) n _ _ _ (pi.basis_fun 𝕜 n)))ᵀ :=
begin
  ext i j,
  rw [LDL.lower_inv, basis.coe_pi_basis_fun.to_matrix_eq_transpose, coe_gram_schmidt_basis],
  refl
end

noncomputable instance LDL.invertible_lower_inv : invertible (LDL.lower_inv hS) :=
begin
  rw [LDL.lower_inv_gram_schmidt_basis],
  haveI := basis.invertible_to_matrix (pi.basis_fun 𝕜 n)
    (@gram_schmidt_basis 𝕜 (n → 𝕜) _ (inner_product_space.of_matrix hS.transpose)
      n _ _ _ (pi.basis_fun 𝕜 n)),
  apply invertible_transpose,
end

lemma LDL.lower_inv_orthogonal {i j : n} (h₀ : i ≠ j) :
  ⟪(LDL.lower_inv hS i), Sᵀ.mul_vec (LDL.lower_inv hS j)⟫ = 0 :=
show @inner 𝕜 (n → 𝕜) (inner_product_space.of_matrix hS.transpose).to_has_inner
    (LDL.lower_inv hS i)
    (LDL.lower_inv hS j) = 0,
by apply gram_schmidt_orthogonal _ _ h₀

/-- The entries of the diagonal matrix `D` of the LDL decomposition. -/
noncomputable def LDL.diag_entries : n → 𝕜 :=
  λ i, ⟪star (LDL.lower_inv hS i), S.mul_vec (star (LDL.lower_inv hS i))⟫

/-- The diagonal matrix `D` of the LDL decomposition. -/
noncomputable def LDL.diag : matrix n n 𝕜 := matrix.diagonal (LDL.diag_entries hS)

lemma LDL.lower_inv_triangular [succ_order n] {i j : n} (hij : i < j) :
  LDL.lower_inv hS i j = 0 :=
by rw [← @gram_schmidt_triangular 𝕜 (n → 𝕜) _ (inner_product_space.of_matrix hS.transpose) n _ _ _
    i j hij (pi.basis_fun 𝕜 n), pi.basis_fun_repr, LDL.lower_inv]

lemma ldl_decomposition₀ : LDL.diag hS = LDL.lower_inv hS ⬝ S ⬝ (LDL.lower_inv hS)ᴴ :=
begin
  ext i j,
  by_cases hij : i = j,
  { simpa only [hij, LDL.diag, diagonal_apply_eq, LDL.diag_entries, matrix.mul_assoc, inner,
      pi.star_apply, is_R_or_C.star_def, star_ring_end_self_apply] },
  { simp only [LDL.diag, hij, diagonal_apply_ne, ne.def, not_false_iff, mul_mul_apply],
    rw [conj_transpose, transpose_map, transpose_transpose, dot_product_mul_vec,
      (LDL.lower_inv_orthogonal hS (λ h : j = i, hij h.symm)).symm,
      ← inner_conj_sym, mul_vec_transpose, euclidean_space.inner_eq_star_dot_product,
      ← is_R_or_C.star_def, ← star_dot_product_star, dot_product_comm, star_star],
    refl }
end

/-- The lower triangular matrix `L` of the LDL decomposition. -/
noncomputable def LDL.lower := (LDL.lower_inv hS)⁻¹

theorem ldl_decomposition :
  LDL.lower hS ⬝ LDL.diag hS ⬝ (LDL.lower hS)ᴴ = S :=
begin
  rw [LDL.lower, conj_transpose_nonsing_inv, matrix.mul_assoc,
    matrix.inv_mul_eq_iff_eq_mul (LDL.lower_inv hS), matrix.mul_inv_eq_iff_eq_mul],
  exact ldl_decomposition₀ hS,
end
