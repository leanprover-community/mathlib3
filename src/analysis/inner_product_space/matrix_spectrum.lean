import analysis.inner_product_space.spectrum


namespace basis

variables {ι ι' κ κ' : Type*}
variables {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]

open_locale big_operators

/-- From a basis `e : ι → M`, build a linear equivalence between families of vectors `v : ι → M`,
and matrices, making the matrix whose columns are the vectors `v i` written in the basis `e`. -/
noncomputable def to_matrix_equiv' [fintype ι] (e : basis ι R M) : (ι' → M) ≃ₗ[R] matrix ι ι' R :=
{ to_fun := e.to_matrix,
  map_add' := λ v w, begin
    ext i j,
    change _ = _ + _,
    rw [e.to_matrix_apply, pi.add_apply, linear_equiv.map_add],
    refl
  end,
  map_smul' := begin
    intros c v,
    ext i j,
    rw [e.to_matrix_apply, pi.smul_apply, linear_equiv.map_smul],
    refl
  end,
  inv_fun := λ m j, ∑ i, (m i j) • e i,
  left_inv := begin
    intro v,
    ext j,
    exact e.sum_to_matrix_smul_self v j
  end,
  right_inv := begin
    intros m,
    ext k l,
    simp only [e.to_matrix_apply, ← e.equiv_fun_apply, ← e.equiv_fun_symm_apply,
               linear_equiv.apply_symm_apply],
  end }

end basis

#check @inner_product_space.is_self_adjoint.diagonalization_basis_apply_self_apply

namespace matrix

variables {𝕜 : Type*} [is_R_or_C 𝕜] [decidable_eq 𝕜]
  {n : Type*} [fintype n] [decidable_eq n]
  {A : matrix n n 𝕜}

open_locale matrix

local notation `⟪`x`, `y`⟫` := @inner 𝕜 (pi_Lp 2 (λ (_ : n), 𝕜)) _ x y

def is_hermitian (A : matrix n n 𝕜) : Prop := Aᴴ = A

-- TODO: move
@[simp] lemma euclidean_space.mul_vec_single_apply (i j : n) :
  A.mul_vec (euclidean_space.single j 1) i = A i j :=
matrix.mul_vec_std_basis A i j

@[simp] lemma euclidean_space.mul_vec_single (j : n) :
  A.mul_vec (euclidean_space.single j 1) = λ i, A i j :=
by ext; apply euclidean_space.mul_vec_single_apply

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

noncomputable def eigenvalues₀ : fin (fintype.card n) → ℝ :=
@inner_product_space.is_self_adjoint.eigenvalues 𝕜 _ _ (pi_Lp 2 (λ (_ : n), 𝕜)) _ A.to_lin'
  (is_hermitian_iff_is_self_adjoint.1 hA) _ (fintype.card n) finrank_euclidean_space

noncomputable def eigenvalues : n → ℝ :=
  λ i, hA.eigenvalues₀ $ fintype.equiv_of_card_eq (fintype.card_fin _).symm i

noncomputable def diagonalization_basis : basis n 𝕜 (n → 𝕜) :=
  (@inner_product_space.is_self_adjoint.eigenvector_basis 𝕜 _ _
  (pi_Lp 2 (λ (_ : n), 𝕜)) _ A.to_lin' (is_hermitian_iff_is_self_adjoint.1 hA) _ (fintype.card n)
  finrank_euclidean_space).reindex (fintype.equiv_of_card_eq (fintype.card_fin _))

noncomputable def diagonalization_matrix : matrix n n 𝕜 :=
  (pi.basis_fun 𝕜 n).to_matrix (diagonalization_basis hA)

noncomputable def diagonalization_matrix_inv : matrix n n 𝕜 :=
  (diagonalization_basis hA).to_matrix (pi.basis_fun 𝕜 n)

lemma diagonalization_matrix_mul_inv :
  hA.diagonalization_matrix ⬝ hA.diagonalization_matrix_inv = 1 :=
by apply basis.to_matrix_mul_to_matrix_flip

local notation `𝓚` := algebra_map ℝ _

-- TODO: move
lemma basis_to_matrix_mul (b₁ : basis n 𝕜 (n → 𝕜)) (b₂ : basis n 𝕜 (n → 𝕜)) (b₃ : basis n 𝕜 (n → 𝕜)) :
  b₁.to_matrix b₂ ⬝ A = linear_map.to_matrix b₃ b₁ (to_lin b₃ b₂ A) :=
begin
  have := basis_to_matrix_mul_linear_map_to_matrix b₃ b₁ b₂ (matrix.to_lin b₃ b₂ A),
  rwa [linear_map.to_matrix_to_lin] at this
end

-- TODO: move
lemma basis_to_matrix_basis_fun_mul (b : basis n 𝕜 (n → 𝕜)) :
  b.to_matrix (pi.basis_fun 𝕜 n) ⬝ A = (λ i j, b.repr (Aᵀ j) i) :=
begin
  rw [basis_to_matrix_mul _ _ (pi.basis_fun 𝕜 n), matrix.to_lin_eq_to_lin'],
  ext i j,
  have : A.mul_vec ((linear_map.std_basis 𝕜 (λ (i : n), 𝕜) j) 1) = Aᵀ j :=
    funext (λ x, matrix.mul_vec_std_basis A x j),
  rw [linear_map.to_matrix_apply, matrix.to_lin'_apply, pi.basis_fun_apply, this]
end

lemma spectral_theorem_1 :
  hA.diagonalization_matrix_inv ⬝ A
    = diagonal (𝓚 ∘ hA.eigenvalues) ⬝ hA.diagonalization_matrix_inv :=
begin
  rw [diagonalization_matrix_inv, basis_to_matrix_basis_fun_mul],
  ext i j,
  convert @inner_product_space.is_self_adjoint.diagonalization_basis_apply_self_apply 𝕜 _ _
    (pi_Lp 2 (λ (_ : n), 𝕜)) _ A.to_lin' (is_hermitian_iff_is_self_adjoint.1 hA) _ (fintype.card n)
    finrank_euclidean_space (euclidean_space.single j 1)
    ((fintype.equiv_of_card_eq (fintype.card_fin _)).symm i),
  { simp only [inner_product_space.is_self_adjoint.diagonalization_basis, diagonalization_basis,
      basis.coe_to_orthonormal_basis_repr, basis.equiv_fun_apply, to_lin'_apply, basis.to_matrix],
    rw [basis.reindex_repr, euclidean_space.mul_vec_single],
    congr' },
  { sorry }
end

theorem spectral_theorem : A =
       hA.diagonalization_matrix⁻¹
        ⬝ diagonal (𝓚 ∘ hA.eigenvalues)
        ⬝ hA.diagonalization_matrix := sorry

#check matrix.det_diagonal

end is_hermitian

end matrix
