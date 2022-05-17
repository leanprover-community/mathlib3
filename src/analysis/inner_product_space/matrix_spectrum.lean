import analysis.inner_product_space.spectrum


#check @inner_product_space.is_self_adjoint.diagonalization_basis_apply_self_apply

namespace matrix

variables {𝕜 : Type*} [is_R_or_C 𝕜] [decidable_eq 𝕜]
  {n : Type*} [fintype n] [decidable_eq n]
  {A : matrix n n 𝕜}

open_locale matrix

local notation `⟪`x`, `y`⟫` := @inner 𝕜 (pi_Lp 2 (λ (_ : n), 𝕜)) _ x y

def is_hermitian (A : matrix n n 𝕜) : Prop := Aᴴ = A

-- TODO: move
@[simp] lemma euclidean_space.mul_vec_single (i j : n) :
  A.mul_vec (euclidean_space.single j 1) i = A i j :=
matrix.mul_vec_std_basis A i j

-- TODO: move
@[simp] lemma euclidean_space.vec_mul_single (i j : n) :
  A.vec_mul (euclidean_space.single i 1) j = A i j :=
matrix.vec_mul_std_basis A i j

-- TODO: move
lemma star_mul_vec (A : matrix n n 𝕜) (v : n → 𝕜) :
  star (A.mul_vec v) = (star A).vec_mul (star v) :=
begin
  ext i,
  calc star (A.mul_vec v) i = star (A i ⬝ᵥ v) :
    by simp only [mul_vec, pi.star_apply]
  ... = star v ⬝ᵥ star (λ j, A i j) :
    by rw [← star_dot_product_star]
  ... = star v ⬝ᵥ λ (i_1 : n), Aᴴ i_1 i :
    by simp only [conj_transpose_apply, star]
  ... = (star A).vec_mul (star v) i :
    by simp only [vec_mul, (star_apply _ _ _).symm, conj_transpose_apply]
end

lemma pi_Lp.inner_eq_star_dot_product (x y : n → 𝕜) : ⟪x, y⟫ = star x ⬝ᵥ y := rfl

lemma is_hermitian_iff_is_self_adjoint {A : matrix n n 𝕜} :
  is_hermitian A ↔ @inner_product_space.is_self_adjoint 𝕜 (pi_Lp 2 (λ (_ : n), 𝕜)) _ _ A.to_lin' :=
begin
  split,
  show A.is_hermitian → ∀ x y, ⟪A.mul_vec x, y⟫ = ⟪x, A.mul_vec y⟫,
  { intros h x y,
    unfold is_hermitian at h,
    simp only [pi_Lp.inner_eq_star_dot_product, star_mul_vec, matrix.dot_product_mul_vec,
      h, star_eq_conj_transpose] },
  show (∀ x y, ⟪A.mul_vec x, y⟫ = ⟪x, A.mul_vec y⟫) → A.is_hermitian,
  { intro h,
    ext i j,
    have := h (euclidean_space.single i 1) (euclidean_space.single j 1),
    simpa [euclidean_space.inner_single_right, euclidean_space.inner_single_left] using this}
end

namespace is_hermitian

variables (hA : A.is_hermitian)

noncomputable def eigenvalues : fin (fintype.card n) → ℝ :=
@inner_product_space.is_self_adjoint.eigenvalues 𝕜 _ _ (pi_Lp 2 (λ (_ : n), 𝕜)) _ A.to_lin'
  (is_hermitian_iff_is_self_adjoint.1 hA) _ (fintype.card n) finrank_euclidean_space

noncomputable def diagonalization_basis : basis (fin (fintype.card n)) 𝕜 (n → 𝕜) :=
basis.of_equiv_fun (@inner_product_space.is_self_adjoint.diagonalization_basis 𝕜 _ _
  (pi_Lp 2 (λ (_ : n), 𝕜)) _ A.to_lin' (is_hermitian_iff_is_self_adjoint.1 hA) _ (fintype.card n)
    finrank_euclidean_space).to_linear_equiv

#check (diagonalization_basis hA).to_matrix
#check (diagonalization_basis hA).to_matrix⁻¹
#check matrix.det_diagonal

#check linear_map.to_matrix

#check inner_product_space.is_self_adjoint.diagonalization_basis

#check  @inner_product_space.is_self_adjoint.diagonalization_basis_apply_self_apply

end is_self_adjoint

end matrix
