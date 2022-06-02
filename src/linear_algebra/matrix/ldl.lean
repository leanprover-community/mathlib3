import analysis.inner_product_space.pi_L2
import analysis.inner_product_space.gram_schmidt_ortho
import linear_algebra.matrix.bilinear_form
-- import linear_algebra.matrix.pos_def

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

theorem ldl_decomposition :
  A = hA.ldl_lower ⬝ hA.ldl_diag ⬝ hA.ldl_lowerᴴ := sorry
