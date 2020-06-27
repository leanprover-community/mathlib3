/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import ring_theory.matrix_algebra
import ring_theory.polynomial_algebra
import data.polynomial_cayley_hamilton
import linear_algebra.nonsingular_inverse

noncomputable theory

universes u v w

open polynomial matrix
open_locale big_operators

variables {R : Type u} [comm_ring R]
variables {n : Type w} [fintype n] [decidable_eq n]

def characteristic_matrix (m : matrix n n R) : matrix n n (polynomial R) :=
matrix.scalar n (X : polynomial R) - (λ i j, C (m i j))

@[simp] lemma characteristic_matrix_apply_eq (m : matrix n n R) (i : n) :
  characteristic_matrix m i i = (X : polynomial R) - C (m i i) :=
by simp only [characteristic_matrix, sub_left_inj, pi.sub_apply, scalar_apply_eq]

@[simp] lemma characteristic_matrix_apply_ne (m : matrix n n R) (i j : n) (h : i ≠ j) :
  characteristic_matrix m i j = - C (m i j) :=
by simp only [characteristic_matrix, pi.sub_apply, scalar_apply_ne _ _ _ h, zero_sub]


lemma q (m : matrix n n R) :
  matrix_polynomial_equiv_polynomial_matrix (characteristic_matrix m) = X - C m :=
begin
  ext k i j,
  simp only [matrix_polynomial_equiv_polynomial_matrix_coeff_apply, coeff_sub, pi.sub_apply],
  by_cases h : i = j,
  { subst h, rw [characteristic_matrix_apply_eq, coeff_sub],
    simp only [coeff_X, coeff_C],
    split_ifs; simp, },
  { rw [characteristic_matrix_apply_ne _ _ _ h, coeff_X, coeff_neg, coeff_C, coeff_C],
    split_ifs; simp [h], }
end

def characteristic_polynomial (m : matrix n n R) : polynomial R :=
(characteristic_matrix m).det

theorem cayley_hamilton (m : matrix n n R) :
  (characteristic_polynomial m).eval₂ (algebra_map R (matrix n n R)) m = 0 :=
begin
  have := calc
    (characteristic_polynomial m) • (1 : matrix n n (polynomial R))
         = (characteristic_matrix m).det • (1 : matrix n n (polynomial R)) : rfl
     ... = adjugate (characteristic_matrix m) * (characteristic_matrix m)  : (adjugate_mul _).symm,
  apply_fun matrix_polynomial_equiv_polynomial_matrix at this,
  change _ = matrix_polynomial_equiv_polynomial_matrix (_ * _) at this,
  simp only [matrix_polynomial_equiv_polynomial_matrix.map_mul] at this,
  rw q at this,
  apply_fun (λ p, p.eval₂ (ring_hom.id _) m) at this,
  rw eval₂_mul_X_sub_C at this,
  rw matrix_polynomial_equiv_polynomial_matrix_smul_one at this,
  rw eval₂_eq_eval_map at this ⊢,
  simp at this,
  exact this,
end
