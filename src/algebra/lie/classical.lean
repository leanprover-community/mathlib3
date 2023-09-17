/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.invertible
import data.matrix.basis
import data.matrix.dmatrix
import algebra.lie.abelian
import linear_algebra.matrix.trace
import algebra.lie.skew_adjoint
import linear_algebra.symplectic_group

/-!
# Classical Lie algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file is the place to find definitions and basic properties of the classical Lie algebras:
  * Aₗ = sl(l+1)
  * Bₗ ≃ so(l+1, l) ≃ so(2l+1)
  * Cₗ = sp(l)
  * Dₗ ≃ so(l, l) ≃ so(2l)

## Main definitions

  * `lie_algebra.special_linear.sl`
  * `lie_algebra.symplectic.sp`
  * `lie_algebra.orthogonal.so`
  * `lie_algebra.orthogonal.so'`
  * `lie_algebra.orthogonal.so_indefinite_equiv`
  * `lie_algebra.orthogonal.type_D`
  * `lie_algebra.orthogonal.type_B`
  * `lie_algebra.orthogonal.type_D_equiv_so'`
  * `lie_algebra.orthogonal.type_B_equiv_so'`

## Implementation notes

### Matrices or endomorphisms

Given a finite type and a commutative ring, the corresponding square matrices are equivalent to the
endomorphisms of the corresponding finite-rank free module as Lie algebras, see `lie_equiv_matrix'`.
We can thus define the classical Lie algebras as Lie subalgebras either of matrices or of
endomorphisms. We have opted for the former. At the time of writing (August 2020) it is unclear
which approach should be preferred so the choice should be assumed to be somewhat arbitrary.

### Diagonal quadratic form or diagonal Cartan subalgebra

For the algebras of type `B` and `D`, there are two natural definitions. For example since the
the `2l × 2l` matrix:
$$
  J = \left[\begin{array}{cc}
              0_l & 1_l\\
              1_l & 0_l
            \end{array}\right]
$$
defines a symmetric bilinear form equivalent to that defined by the identity matrix `I`, we can
define the algebras of type `D` to be the Lie subalgebra of skew-adjoint matrices either for `J` or
for `I`. Both definitions have their advantages (in particular the `J`-skew-adjoint matrices define
a Lie algebra for which the diagonal matrices form a Cartan subalgebra) and so we provide both.
We thus also provide equivalences `type_D_equiv_so'`, `so_indefinite_equiv` which show the two
definitions are equivalent. Similarly for the algebras of type `B`.

## Tags

classical lie algebra, special linear, symplectic, orthogonal
-/

universes u₁ u₂

namespace lie_algebra
open matrix
open_locale matrix

variables (n p q l : Type*) (R : Type u₂)
variables [decidable_eq n] [decidable_eq p] [decidable_eq q] [decidable_eq l]
variables [comm_ring R]

@[simp] lemma matrix_trace_commutator_zero [fintype n] (X Y : matrix n n R) :
  matrix.trace ⁅X, Y⁆ = 0 :=
calc _ = matrix.trace (X ⬝ Y) - matrix.trace (Y ⬝ X) : trace_sub _ _
   ... = matrix.trace (X ⬝ Y) - matrix.trace (X ⬝ Y) :
     congr_arg (λ x, _ - x) (matrix.trace_mul_comm Y X)
   ... = 0 : sub_self _

namespace special_linear

/-- The special linear Lie algebra: square matrices of trace zero. -/
def sl [fintype n] : lie_subalgebra R (matrix n n R) :=
{ lie_mem' := λ X Y _ _, linear_map.mem_ker.2 $ matrix_trace_commutator_zero _ _ _ _,
  ..linear_map.ker (matrix.trace_linear_map n R R) }

lemma sl_bracket [fintype n] (A B : sl n R) : ⁅A, B⁆.val = A.val ⬝ B.val - B.val ⬝ A.val := rfl

section elementary_basis

variables {n} [fintype n] (i j : n)

/-- When j ≠ i, the elementary matrices are elements of sl n R, in fact they are part of a natural
basis of sl n R. -/
def Eb (h : j ≠ i) : sl n R :=
⟨matrix.std_basis_matrix i j (1 : R),
  show matrix.std_basis_matrix i j (1 : R) ∈ linear_map.ker (matrix.trace_linear_map n R R),
  from matrix.std_basis_matrix.trace_zero i j (1 : R) h⟩

@[simp] lemma Eb_val (h : j ≠ i) : (Eb R i j h).val = matrix.std_basis_matrix i j 1 := rfl

end elementary_basis

lemma sl_non_abelian [fintype n] [nontrivial R] (h : 1 < fintype.card n) :
  ¬is_lie_abelian ↥(sl n R) :=
begin
  rcases fintype.exists_pair_of_one_lt_card h with ⟨j, i, hij⟩,
  let A := Eb R i j hij,
  let B := Eb R j i hij.symm,
  intros c,
  have c' : A.val ⬝ B.val = B.val ⬝ A.val, by { rw [← sub_eq_zero, ← sl_bracket, c.trivial], refl },
  simpa [std_basis_matrix, matrix.mul_apply, hij] using   congr_fun (congr_fun c' i) i,
end

end special_linear

namespace symplectic

/-- The symplectic Lie algebra: skew-adjoint matrices with respect to the canonical skew-symmetric
bilinear form. -/
def sp [fintype l] : lie_subalgebra R (matrix (l ⊕ l) (l ⊕ l) R) :=
  skew_adjoint_matrices_lie_subalgebra (matrix.J l R)

end symplectic

namespace orthogonal

/-- The definite orthogonal Lie subalgebra: skew-adjoint matrices with respect to the symmetric
bilinear form defined by the identity matrix. -/
def so [fintype n] : lie_subalgebra R (matrix n n R) :=
  skew_adjoint_matrices_lie_subalgebra (1 : matrix n n R)

@[simp] lemma mem_so [fintype n] (A : matrix n n R) : A ∈ so n R ↔ Aᵀ = -A :=
begin
  erw mem_skew_adjoint_matrices_submodule,
  simp only [matrix.is_skew_adjoint, matrix.is_adjoint_pair, matrix.mul_one, matrix.one_mul],
end

/-- The indefinite diagonal matrix with `p` 1s and `q` -1s. -/
def indefinite_diagonal : matrix (p ⊕ q) (p ⊕ q) R :=
  matrix.diagonal $ sum.elim (λ _, 1) (λ _, -1)

/-- The indefinite orthogonal Lie subalgebra: skew-adjoint matrices with respect to the symmetric
bilinear form defined by the indefinite diagonal matrix. -/
def so' [fintype p] [fintype q] : lie_subalgebra R (matrix (p ⊕ q) (p ⊕ q) R) :=
  skew_adjoint_matrices_lie_subalgebra $ indefinite_diagonal p q R

/-- A matrix for transforming the indefinite diagonal bilinear form into the definite one, provided
the parameter `i` is a square root of -1. -/
def Pso (i : R) : matrix (p ⊕ q) (p ⊕ q) R :=
  matrix.diagonal $ sum.elim (λ _, 1) (λ _, i)

variables [fintype p] [fintype q]

lemma Pso_inv {i : R} (hi : i*i = -1) : (Pso p q R i) * (Pso p q R (-i)) = 1 :=
begin
  ext x y, rcases x; rcases y,
  { -- x y : p
    by_cases h : x = y; simp [Pso, indefinite_diagonal, h], },
  { -- x : p, y : q
    simp [Pso, indefinite_diagonal], },
  { -- x : q, y : p
    simp [Pso, indefinite_diagonal], },
  { -- x y : q
    by_cases h : x = y; simp [Pso, indefinite_diagonal, h, hi], },
end

/-- There is a constructive inverse of `Pso p q R i`. -/
def invertible_Pso {i : R} (hi : i*i = -1) : invertible (Pso p q R i) :=
invertible_of_right_inverse _ _ (Pso_inv p q R hi)

lemma indefinite_diagonal_transform {i : R} (hi : i*i = -1) :
  (Pso p q R i)ᵀ ⬝ (indefinite_diagonal p q R) ⬝ (Pso p q R i) = 1 :=
begin
  ext x y, rcases x; rcases y,
  { -- x y : p
    by_cases h : x = y; simp [Pso, indefinite_diagonal, h], },
  { -- x : p, y : q
    simp [Pso, indefinite_diagonal], },
  { -- x : q, y : p
    simp [Pso, indefinite_diagonal], },
  { -- x y : q
    by_cases h : x = y; simp [Pso, indefinite_diagonal, h, hi], },
end

/-- An equivalence between the indefinite and definite orthogonal Lie algebras, over a ring
containing a square root of -1. -/
def so_indefinite_equiv {i : R} (hi : i*i = -1) : so' p q R ≃ₗ⁅R⁆ so (p ⊕ q) R :=
begin
  apply (skew_adjoint_matrices_lie_subalgebra_equiv
    (indefinite_diagonal p q R) (Pso p q R i) (invertible_Pso p q R hi)).trans,
  apply lie_equiv.of_eq,
  ext A, rw indefinite_diagonal_transform p q R hi, refl,
end

lemma so_indefinite_equiv_apply {i : R} (hi : i*i = -1) (A : so' p q R) :
  (so_indefinite_equiv p q R hi A : matrix (p ⊕ q) (p ⊕ q) R) =
    (Pso p q R i)⁻¹ ⬝ (A : matrix (p ⊕ q) (p ⊕ q) R) ⬝ (Pso p q R i) :=
by erw [lie_equiv.trans_apply, lie_equiv.of_eq_apply,
        skew_adjoint_matrices_lie_subalgebra_equiv_apply]

/-- A matrix defining a canonical even-rank symmetric bilinear form.

It looks like this as a `2l x 2l` matrix of `l x l` blocks:

   [ 0 1 ]
   [ 1 0 ]
-/
def JD : matrix (l ⊕ l) (l ⊕ l) R := matrix.from_blocks 0 1 1 0

/-- The classical Lie algebra of type D as a Lie subalgebra of matrices associated to the matrix
`JD`. -/
def type_D [fintype l] := skew_adjoint_matrices_lie_subalgebra (JD l R)

/-- A matrix transforming the bilinear form defined by the matrix `JD` into a split-signature
diagonal matrix.

It looks like this as a `2l x 2l` matrix of `l x l` blocks:

   [ 1 -1 ]
   [ 1  1 ]
-/
def PD : matrix (l ⊕ l) (l ⊕ l) R := matrix.from_blocks 1 (-1) 1 1

/-- The split-signature diagonal matrix. -/
def S := indefinite_diagonal l l R

lemma S_as_blocks : S l R = matrix.from_blocks 1 0 0 (-1) :=
begin
  rw [← matrix.diagonal_one, matrix.diagonal_neg, matrix.from_blocks_diagonal],
  refl,
end

lemma JD_transform [fintype l] : (PD l R)ᵀ ⬝ (JD l R) ⬝ (PD l R) = (2 : R) • (S l R) :=
begin
  have h : (PD l R)ᵀ ⬝ (JD l R) = matrix.from_blocks 1 1 1 (-1) := by
  { simp [PD, JD, matrix.from_blocks_transpose, matrix.from_blocks_multiply], },
  erw [h, S_as_blocks, matrix.from_blocks_multiply, matrix.from_blocks_smul],
  congr; simp [two_smul],
end

lemma PD_inv [fintype l] [invertible (2 : R)] : (PD l R) * (⅟(2 : R) • (PD l R)ᵀ) = 1 :=
begin
  have h : ⅟(2 : R) • (1 : matrix l l R) + ⅟(2 : R) • 1 = 1 := by
    rw [← smul_add, ← (two_smul R _), smul_smul, inv_of_mul_self, one_smul],
  erw [matrix.from_blocks_transpose, matrix.from_blocks_smul, matrix.mul_eq_mul,
    matrix.from_blocks_multiply],
  simp [h],
end

instance invertible_PD [fintype l] [invertible (2 : R)] : invertible (PD l R) :=
invertible_of_right_inverse _ _ (PD_inv l R)

/-- An equivalence between two possible definitions of the classical Lie algebra of type D. -/
def type_D_equiv_so' [fintype l] [invertible (2 : R)] :
  type_D l R ≃ₗ⁅R⁆ so' l l R :=
begin
  apply (skew_adjoint_matrices_lie_subalgebra_equiv (JD l R) (PD l R) (by apply_instance)).trans,
  apply lie_equiv.of_eq,
  ext A,
  rw [JD_transform, ← coe_unit_of_invertible (2 : R), ←units.smul_def, lie_subalgebra.mem_coe,
      mem_skew_adjoint_matrices_lie_subalgebra_unit_smul],
  refl,
end

/-- A matrix defining a canonical odd-rank symmetric bilinear form.

It looks like this as a `(2l+1) x (2l+1)` matrix of blocks:

   [ 2 0 0 ]
   [ 0 0 1 ]
   [ 0 1 0 ]

where sizes of the blocks are:

   [`1 x 1` `1 x l` `1 x l`]
   [`l x 1` `l x l` `l x l`]
   [`l x 1` `l x l` `l x l`]
-/
def JB := matrix.from_blocks ((2 : R) • 1 : matrix unit unit R) 0 0 (JD l R)

/-- The classical Lie algebra of type B as a Lie subalgebra of matrices associated to the matrix
`JB`. -/
def type_B  [fintype l] := skew_adjoint_matrices_lie_subalgebra(JB l R)

/-- A matrix transforming the bilinear form defined by the matrix `JB` into an
almost-split-signature diagonal matrix.

It looks like this as a `(2l+1) x (2l+1)` matrix of blocks:

   [ 1 0  0 ]
   [ 0 1 -1 ]
   [ 0 1  1 ]

where sizes of the blocks are:

   [`1 x 1` `1 x l` `1 x l`]
   [`l x 1` `l x l` `l x l`]
   [`l x 1` `l x l` `l x l`]
-/
def PB := matrix.from_blocks (1 : matrix unit unit R) 0 0 (PD l R)

variable [fintype l]

lemma PB_inv [invertible (2 : R)] : PB l R * matrix.from_blocks 1 0 0 (⅟(PD l R)) = 1 :=
begin
  rw [PB, matrix.mul_eq_mul, matrix.from_blocks_multiply, matrix.mul_inv_of_self],
  simp only [matrix.mul_zero, matrix.mul_one, matrix.zero_mul, zero_add, add_zero,
    matrix.from_blocks_one]
end

instance invertible_PB [invertible (2 : R)] : invertible (PB l R) :=
invertible_of_right_inverse _ _ (PB_inv l R)

lemma JB_transform : (PB l R)ᵀ ⬝ (JB l R) ⬝ (PB l R) = (2 : R) • matrix.from_blocks 1 0 0 (S l R) :=
by simp [PB, JB, JD_transform, matrix.from_blocks_transpose, matrix.from_blocks_multiply,
         matrix.from_blocks_smul]

lemma indefinite_diagonal_assoc :
  indefinite_diagonal (unit ⊕ l) l R =
  matrix.reindex_lie_equiv (equiv.sum_assoc unit l l).symm
    (matrix.from_blocks 1 0 0 (indefinite_diagonal l l R)) :=
begin
  ext i j,
  rcases i with ⟨⟨i₁ | i₂⟩ | i₃⟩;
  rcases j with ⟨⟨j₁ | j₂⟩ | j₃⟩;
  simp only [indefinite_diagonal, matrix.diagonal_apply, equiv.sum_assoc_apply_inl_inl,
    matrix.reindex_lie_equiv_apply, matrix.submatrix_apply, equiv.symm_symm, matrix.reindex_apply,
    sum.elim_inl, if_true, eq_self_iff_true, matrix.one_apply_eq, matrix.from_blocks_apply₁₁,
    dmatrix.zero_apply, equiv.sum_assoc_apply_inl_inr, if_false, matrix.from_blocks_apply₁₂,
    matrix.from_blocks_apply₂₁, matrix.from_blocks_apply₂₂, equiv.sum_assoc_apply_inr,
    sum.elim_inr];
  congr,
end

/-- An equivalence between two possible definitions of the classical Lie algebra of type B. -/
def type_B_equiv_so' [invertible (2 : R)] :
  type_B l R ≃ₗ⁅R⁆ so' (unit ⊕ l) l R :=
begin
  apply (skew_adjoint_matrices_lie_subalgebra_equiv (JB l R) (PB l R) (by apply_instance)).trans,
  symmetry,
  apply (skew_adjoint_matrices_lie_subalgebra_equiv_transpose
    (indefinite_diagonal (unit ⊕ l) l R)
    (matrix.reindex_alg_equiv _ (equiv.sum_assoc punit l l)) (matrix.transpose_reindex _ _)).trans,
  apply lie_equiv.of_eq,
  ext A,
  rw [JB_transform, ← coe_unit_of_invertible (2 : R), ←units.smul_def, lie_subalgebra.mem_coe,
      lie_subalgebra.mem_coe, mem_skew_adjoint_matrices_lie_subalgebra_unit_smul],
  simpa [indefinite_diagonal_assoc],
end

end orthogonal

end lie_algebra
