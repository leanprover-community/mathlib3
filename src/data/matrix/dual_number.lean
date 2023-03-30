/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.dual_number
import data.matrix.basic

/-!
# Matrices of dual numbers are isomorphic to dual numbers over matrices

Showing this for the more general case of `triv_sq_zero_ext R M` would require an action between
`matrix n n R` and `matrix n n M`, which would risk causing diamonds.
-/

variables {R n : Type} [comm_semiring R] [fintype n] [decidable_eq n]

open matrix triv_sq_zero_ext

/-- Matrices over dual numbers and dual numbers over matrices are isomorphic. -/
@[simps]
def matrix.dual_number_equiv : matrix n n (dual_number R) ≃ₐ[R] dual_number (matrix n n R) :=
{ to_fun := λ A, ⟨of (λ i j, (A i j).fst), of (λ i j, (A i j).snd)⟩,
  inv_fun := λ d, of (λ i j, (d.fst i j, d.snd i j)),
  left_inv := λ A, matrix.ext $ λ i j, triv_sq_zero_ext.ext rfl rfl,
  right_inv := λ d, triv_sq_zero_ext.ext (matrix.ext $ λ i j, rfl) (matrix.ext $ λ i j, rfl),
  map_mul' := λ A B, begin
    ext; dsimp [mul_apply],
    { simp_rw [fst_sum, fst_mul] },
    { simp_rw [snd_sum, snd_mul, smul_eq_mul, op_smul_eq_mul, finset.sum_add_distrib] },
  end,
  map_add' := λ A B, triv_sq_zero_ext.ext rfl rfl,
  commutes' := λ r, begin
    simp_rw [algebra_map_eq_inl', algebra_map_eq_diagonal, pi.algebra_map_def,
      algebra.id.map_eq_self, algebra_map_eq_inl, ←diagonal_map (inl_zero R), map_apply,
      fst_inl, snd_inl],
    refl,
  end }
