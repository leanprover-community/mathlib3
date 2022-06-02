import analysis.inner_product_space.pi_L2
import analysis.inner_product_space.gram_schmidt_ortho
import linear_algebra.matrix.bilinear_form
-- import linear_algebra.matrix.pos_def


namespace basis
variables {ι : Type*} {R : Type*} {M : Type*} {v : ι → M} [ring R] [add_comm_group M] [module R M]

open submodule

def basis.of_linear_independent
  (h : linear_independent R v) (h_span : span R (set.range v) = ⊤) :
  basis ι R M :=
begin
  have := (basis.span h).repr,
  have := (linear_equiv.of_top _ h_span).symm.trans this,
  exact basis.mk this,
end

end basis

namespace matrix


#check basis.span

variables {n : Type*} [fintype n] [decidable_eq n] [nonempty n] {R : Type*} [field R]

noncomputable lemma xxx (M : matrix n n R) (h : linear_independent R M) : invertible M :=
begin
  apply invertible_of_left_inverse,
  have := h.repr,
  have := span_eq_top_of_linear_independent_of_card_eq_finrank h,
end

end matrix

variables {𝕜 : Type*} [is_R_or_C 𝕜] {n : Type*} [linear_order n]
  [is_well_order n (<)] [locally_finite_order n] [order_bot n]

local notation `⟪`x`, `y`⟫` := @inner 𝕜 (n → 𝕜) (pi_Lp.inner_product_space (λ _, 𝕜)).to_has_inner x y
open matrix
open_locale matrix

noncomputable def inner_product_space.of_matrix [fintype n]
  (A : matrix n n 𝕜) : inner_product_space 𝕜 (n → 𝕜) := -- (hA : A.pos_def)
inner_product_space.of_core
{ inner := λ x y, ⟪x, A.mul_vec y⟫,
  conj_sym := sorry,
  nonneg_re := sorry,
  definite := sorry,
  add_left := sorry,
  smul_left := sorry }

variables (S : matrix n n 𝕜) [fintype n]

noncomputable def LDL.L_inv : matrix n n 𝕜 :=
  λ i j, @gram_schmidt 𝕜 (n → 𝕜) _ (inner_product_space.of_matrix S) n _ _ _ _
    (λ k, pi.basis_fun 𝕜 n k) j i

lemma LDL.L_inv_orthogonal₀ {i j : n} (h₀ : i ≠ j) :
  @inner 𝕜 (n → 𝕜) (inner_product_space.of_matrix S).to_has_inner
    (λ k, LDL.L_inv S k i)
    (λ k, LDL.L_inv S k j) = 0 :=
by apply gram_schmidt_orthogonal _ _ h₀

lemma LDL.L_inv_orthogonal₁ {i j : n} (h₀ : i ≠ j) :
  ⟪(LDL.L_inv S)ᵀ i, S.mul_vec ((LDL.L_inv S)ᵀ j)⟫ = 0 :=
LDL.L_inv_orthogonal₀ S h₀

noncomputable def LDL.diag_entries : n → 𝕜 :=
  λ i, ⟪(LDL.L_inv S)ᵀ i, S.mul_vec ((LDL.L_inv S)ᵀ i)⟫

noncomputable def LDL.diag : matrix n n 𝕜 := matrix.diagonal (LDL.diag_entries S)

lemma LDL.orthogonal_basis_triangular [succ_order n] {i j : n} (hij : i < j) :
  LDL.L_inv S j i = 0 :=
by rw [← @gram_schmidt_triangular 𝕜 (n → 𝕜) _ (inner_product_space.of_matrix S) n _ _ _ _ _ _
    i j hij (pi.basis_fun 𝕜 n), pi.basis_fun_repr, LDL.L_inv]


lemma ldl_decomposition₀ : LDL.diag S = (LDL.L_inv S)ᴴ ⬝ S ⬝ LDL.L_inv S :=
begin
  ext i j,
  by_cases hij : i = j,
  { simpa only [hij, LDL.diag, diagonal_apply_eq, LDL.diag_entries, matrix.mul_assoc] },
  { simp only [LDL.diag, hij, diagonal_apply_ne, ne.def, not_false_iff, matrix.mul_assoc],
    exact (LDL.L_inv_orthogonal₁ S hij).symm }
end

noncomputable def LDL.L := ((LDL.L_inv S)ᴴ)⁻¹

theorem ldl_decomposition :
  S = LDL.L S ⬝ LDL.diag S ⬝ (LDL.L S)ᴴ :=
begin
  haveI : invertible (LDL.L_inv S)ᴴ := sorry,
  haveI : invertible (LDL.L_inv S) := sorry,
  have := ldl_decomposition₀ S,
  have := congr_arg (λ A, LDL.L S ⬝ A) this,
  have := congr_arg (λ A, A ⬝ (LDL.L S)ᴴ) this,
  simp [LDL.L, (matrix.mul_assoc _ _ _).symm] at this,
  simp [(conj_transpose_nonsing_inv (LDL.L_inv S)).symm, matrix.mul_assoc] at this,
  simp [matrix.mul_assoc, LDL.L, (conj_transpose_nonsing_inv (LDL.L_inv S)).symm, this]
end
