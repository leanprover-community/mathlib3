/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import analysis.inner_product_space.spectrum

/-! # Hermitian matrices

This file defines hermitian matrices and some basic results about them.

## Main definition

 * `matrix.is_hermitian `: a matrix `A : matrix n n 𝕜` is hermitian if `Aᴴ = A`.

## Tags

self-adjoint matrix, hermitian matrix

-/

namespace matrix

variables {𝕜 : Type*} [is_R_or_C 𝕜] {n : Type*} {A : matrix n n 𝕜}

open_locale matrix

local notation `⟪`x`, `y`⟫` := @inner 𝕜 (pi_Lp 2 (λ (_ : n), 𝕜)) _ x y

/-- A matrix is hermitian if it is equal to its conjugate transpose. On the reals, this definition
captures symmetric matrices. -/
def is_hermitian (A : matrix n n 𝕜) : Prop := Aᴴ = A

variables [decidable_eq 𝕜] [fintype n] [decidable_eq n]

/-- A matrix is hermitian iff the corresponding linear map is self adjoint. -/
lemma is_hermitian_iff_is_self_adjoint {A : matrix n n 𝕜} :
  is_hermitian A ↔ @inner_product_space.is_self_adjoint 𝕜 (pi_Lp 2 (λ (_ : n), 𝕜)) _ _ A.to_lin' :=
begin
  split,
  show A.is_hermitian → ∀ x y, ⟪A.mul_vec x, y⟫ = ⟪x, A.mul_vec y⟫,
  { intros h x y,
    unfold is_hermitian at h,
    simp only [euclidean_space.inner_eq_star_dot_product, star_mul_vec, matrix.dot_product_mul_vec,
      h, star_eq_conj_transpose] },
  show (∀ x y, ⟪A.mul_vec x, y⟫ = ⟪x, A.mul_vec y⟫) → A.is_hermitian,
  { intro h,
    ext i j,
    have := h (euclidean_space.single i 1) (euclidean_space.single j 1),
    simpa [euclidean_space.inner_single_right, euclidean_space.inner_single_left] using this}
end

end matrix
