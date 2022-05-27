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

variables [fintype n] [decidable_eq n]

/-- A matrix is hermitian iff the corresponding linear map is self adjoint. -/
lemma is_hermitian_iff_is_self_adjoint {A : matrix n n 𝕜} :
  is_hermitian A ↔ inner_product_space.is_self_adjoint
    ((pi_Lp.linear_equiv 𝕜 (λ _ : n, 𝕜)).symm.conj A.to_lin' : module.End 𝕜 (pi_Lp 2 _)) :=
begin
  rw [inner_product_space.is_self_adjoint, (pi_Lp.equiv 2 (λ _ : n, 𝕜)).symm.surjective.forall₂],
  simp only [linear_equiv.conj_apply, linear_map.comp_apply, linear_equiv.coe_coe,
    pi_Lp.linear_equiv_apply, pi_Lp.linear_equiv_symm_apply, linear_equiv.symm_symm],
  simp_rw [euclidean_space.inner_eq_star_dot_product, equiv.apply_symm_apply, to_lin'_apply,
    star_mul_vec, dot_product_mul_vec],
  split,
  { rintro (h : Aᴴ = A) x y,
    rw h },
  { intro h,
    ext i j,
    simpa only [matrix.star_single, map_one, vec_mul_single, one_smul,
      dot_product_single, mul_one, star_one] using h (pi.single i 1) (pi.single j 1) }
end

end matrix
