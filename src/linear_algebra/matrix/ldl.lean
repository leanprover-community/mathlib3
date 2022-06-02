import analysis.inner_product_space.pi_L2
import analysis.inner_product_space.gram_schmidt_ortho
import linear_algebra.matrix.bilinear_form
import linear_algebra.matrix.pos_def

variables {𝕜 : Type*} [is_R_or_C 𝕜] {n : Type*} [linear_order n]
  [is_well_order n (<)] [locally_finite_order n] [order_bot n]

local notation `⟪`x`, `y`⟫` := @inner 𝕜 (n → 𝕜) (pi_Lp.inner_product_space (λ _, 𝕜)).to_has_inner x y

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

noncomputable def LDL.orthogonal_basis : n → n → 𝕜 :=
  @gram_schmidt 𝕜 (n → 𝕜) _ (inner_product_space.of_matrix S) n _ _ _ _ (λ i, pi.basis_fun 𝕜 n i)

lemma LDL.orthogonal_basis_orthogonal₀ {a b : n} (h₀ : a ≠ b) :
  @inner 𝕜 (n → 𝕜) (inner_product_space.of_matrix S).to_has_inner
    (LDL.orthogonal_basis S a)
    (LDL.orthogonal_basis S b) = 0 :=
by apply gram_schmidt_orthogonal _ _ h₀

lemma LDL.orthogonal_basis_orthogonal {a b : n} (h₀ : a ≠ b) :
  ⟪LDL.orthogonal_basis S a, S.mul_vec (LDL.orthogonal_basis S b)⟫ = 0 :=
LDL.orthogonal_basis_orthogonal₀ S h₀

lemma LDL.orthogonal_basis_triangular [succ_order n] {i j : n} (hij : i < j) :
  LDL.orthogonal_basis S i j = 0 :=
by rw [← @gram_schmidt_triangular 𝕜 (n → 𝕜) _ (inner_product_space.of_matrix S) n _ _ _ _ _ _
    i j hij (pi.basis_fun 𝕜 n), pi.basis_fun_repr, LDL.orthogonal_basis]


theorem ldl_decomposition :
  A = hA.ldl_lower ⬝ hA.ldl_diag ⬝ hA.ldl_lowerᴴ := sorry
