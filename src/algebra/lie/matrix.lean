/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.of_associative
import linear_algebra.matrix.reindex
import linear_algebra.matrix.to_linear_equiv

/-!
# Lie algebras of matrices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

An important class of Lie algebras are those arising from the associative algebra structure on
square matrices over a commutative ring. This file provides some very basic definitions whose
primary value stems from their utility when constructing the classical Lie algebras using matrices.

## Main definitions

  * `lie_equiv_matrix'`
  * `matrix.lie_conj`
  * `matrix.reindex_lie_equiv`

## Tags

lie algebra, matrix
-/

universes u v w w₁ w₂

section matrices
open_locale matrix

variables {R : Type u} [comm_ring R]
variables {n : Type w} [decidable_eq n] [fintype n]

/-- The natural equivalence between linear endomorphisms of finite free modules and square matrices
is compatible with the Lie algebra structures. -/
def lie_equiv_matrix' : module.End R (n → R) ≃ₗ⁅R⁆ matrix n n R :=
{ map_lie' := λ T S,
  begin
    let f := @linear_map.to_matrix' R _ n n _ _,
    change f (T.comp S - S.comp T) = (f T) * (f S) - (f S) * (f T),
    have h : ∀ (T S : module.End R _), f (T.comp S) = (f T) ⬝ (f S) := linear_map.to_matrix'_comp,
    rw [linear_equiv.map_sub, h, h, matrix.mul_eq_mul, matrix.mul_eq_mul],
  end,
  ..linear_map.to_matrix' }

@[simp] lemma lie_equiv_matrix'_apply (f : module.End R (n → R)) :
  lie_equiv_matrix' f = f.to_matrix' := rfl

@[simp] lemma lie_equiv_matrix'_symm_apply (A : matrix n n R) :
  (@lie_equiv_matrix' R _ n _ _).symm A = A.to_lin' := rfl

/-- An invertible matrix induces a Lie algebra equivalence from the space of matrices to itself. -/
def matrix.lie_conj (P : matrix n n R) (h : invertible P) :
  matrix n n R ≃ₗ⁅R⁆ matrix n n R :=
((@lie_equiv_matrix' R _ n _ _).symm.trans (P.to_linear_equiv' h).lie_conj).trans lie_equiv_matrix'

@[simp] lemma matrix.lie_conj_apply (P A : matrix n n R) (h : invertible P) :
  P.lie_conj h A = P ⬝ A ⬝ P⁻¹ :=
by simp [linear_equiv.conj_apply, matrix.lie_conj, linear_map.to_matrix'_comp,
         linear_map.to_matrix'_to_lin']

@[simp] lemma matrix.lie_conj_symm_apply (P A : matrix n n R) (h : invertible P) :
  (P.lie_conj h).symm A = P⁻¹ ⬝ A ⬝ P :=
by simp [linear_equiv.symm_conj_apply, matrix.lie_conj, linear_map.to_matrix'_comp,
         linear_map.to_matrix'_to_lin']

variables {m : Type w₁} [decidable_eq m] [fintype m] (e : n ≃ m)

/-- For square matrices, the natural map that reindexes a matrix's rows and columns with equivalent
types, `matrix.reindex`, is an equivalence of Lie algebras. -/
def matrix.reindex_lie_equiv : matrix n n R ≃ₗ⁅R⁆ matrix m m R :=
{ to_fun := matrix.reindex e e,
  map_lie' := λ M N, by simp only [lie_ring.of_associative_ring_bracket, matrix.reindex_apply,
    matrix.submatrix_mul_equiv, matrix.mul_eq_mul, matrix.submatrix_sub, pi.sub_apply],
  ..(matrix.reindex_linear_equiv R R e e) }

@[simp] lemma matrix.reindex_lie_equiv_apply (M : matrix n n R) :
  matrix.reindex_lie_equiv e M = matrix.reindex e e M := rfl

@[simp] lemma matrix.reindex_lie_equiv_symm :
  (matrix.reindex_lie_equiv e : _ ≃ₗ⁅R⁆ _).symm = matrix.reindex_lie_equiv e.symm := rfl

end matrices
