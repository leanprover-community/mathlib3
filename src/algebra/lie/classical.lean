/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.invertible
import algebra.lie.skew_adjoint
import algebra.lie.abelian
import linear_algebra.matrix.trace

/-!
# Classical Lie algebras

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
open_locale matrix

variables (n p q l : Type*) (R : Type u₂)
variables [fintype n] [fintype l] [fintype p] [fintype q]
variables [decidable_eq n] [decidable_eq p] [decidable_eq q] [decidable_eq l]
variables [comm_ring R]

@[simp] lemma matrix_trace_commutator_zero (X Y : matrix n n R) : matrix.trace n R R ⁅X, Y⁆ = 0 :=
calc _ = matrix.trace n R R (X ⬝ Y) - matrix.trace n R R (Y ⬝ X) : linear_map.map_sub _ _ _
   ... = matrix.trace n R R (X ⬝ Y) - matrix.trace n R R (X ⬝ Y) :
     congr_arg (λ x, _ - x) (matrix.trace_mul_comm X Y)
   ... = 0 : sub_self _

namespace special_linear

/-- The special linear Lie algebra: square matrices of trace zero. -/
def sl : lie_subalgebra R (matrix n n R) :=
{ lie_mem' := λ X Y _ _, linear_map.mem_ker.2 $ matrix_trace_commutator_zero _ _ _ _,
  ..linear_map.ker (matrix.trace n R R) }

lemma sl_bracket (A B : sl n R) : ⁅A, B⁆.val = A.val ⬝ B.val - B.val ⬝ A.val := rfl

section elementary_basis

variables {n} (i j : n)

/-- It is useful to define these matrices for explicit calculations in sl n R. -/
abbreviation E : matrix n n R := λ i' j', if i = i' ∧ j = j' then 1 else 0

@[simp] lemma E_apply_one : E R i j i j = 1 := if_pos (and.intro rfl rfl)

@[simp] lemma E_apply_zero (i' j' : n) (h : ¬(i = i' ∧ j = j')) : E R i j i' j' = 0 := if_neg h

@[simp] lemma E_diag_zero (h : j ≠ i) : matrix.diag n R R (E R i j) = 0 :=
funext $ λ k, if_neg $ λ ⟨e₁, e₂⟩, h (e₂.trans e₁.symm)

lemma E_trace_zero (h : j ≠ i) : matrix.trace n R R (E R i j) = 0 := by simp [h]

@[simp] lemma E_mul (k : n) : E R i j ⬝ E R j k = E R i k :=
begin
  ext a b,
  simp only [matrix.mul_apply, boole_mul],
  by_cases h₁ : i = a; by_cases h₂ : k = b;
  simp [h₁, h₂],
end

@[simp] lemma E_mul_of_ne {k l : n} (h : j ≠ k) : E R i j ⬝ E R k l = 0 :=
begin
  ext a b,
  simp only [matrix.mul_apply, dmatrix.zero_apply, boole_mul],
  by_cases h₁ : i = a;
  simp [h₁, h, h.symm],
end


/-- When j ≠ i, the elementary matrices are elements of sl n R, in fact they are part of a natural
basis of sl n R. -/
def Eb (h : j ≠ i) : sl n R :=
⟨E R i j, show E R i j ∈ linear_map.ker (matrix.trace n R R), from E_trace_zero R i j h⟩

@[simp] lemma Eb_val (h : j ≠ i) : (Eb R i j h).val = E R i j := rfl

variable {R}

def transvection (c : R) : matrix n n R := 1 + c • E R i j

lemma transvection_mul (h : i ≠ j) (c d : R) :
  transvection i j c ⬝ transvection i j d = transvection i j (c + d) :=
by simp [transvection, matrix.add_mul, matrix.mul_add, h, h.symm, add_smul, add_assoc]

end elementary_basis

section

variable {R}
variable {r : ℕ}

def is_last_diag (M : matrix (fin r.succ) (fin r.succ) R) :=
∀ (i : fin r.succ), (i : ℕ) < r → (M i (fin.last r) = 0 ∧ M (fin.last r) i = 0)

universe u𝕜
variables {𝕜 : Type u𝕜 } [field 𝕜]
open fin

def Lrow (M : matrix (fin r.succ) (fin r.succ) 𝕜) : list (matrix (fin r.succ) (fin r.succ) 𝕜) :=
list.of_fn $ λ i : fin r, transvection (cast_succ i) (last r) $
  -M (cast_succ i) (last r) / M (last r) (last r)

lemma zoug (M : matrix (fin r.succ) (fin r.succ) 𝕜) (hM : M (last r) (last r) ≠ 0)
  (i : fin r) : ((Lrow M).prod ⬝ M) (fin.cast_succ i) (fin.last r) = 0 :=
begin
  have : ∀ (k : ℕ), k ≤ r → (((Lrow M).drop k).prod ⬝ M) (fin.cast_succ i) (fin.last r) =
    if k ≤ i then 0 else M (fin.cast_succ i) (fin.last r),
  { assume k hk,
    apply nat.decreasing_induction _ hk,
    { simp only [lie_algebra.special_linear.Lrow, list.length_of_fn, matrix.one_mul,
        list.drop_eq_nil_of_le, list.prod_nil],
      rw if_neg,
      simpa only [not_le] using i.2 },
    { assume n hn,
      have : n < (Lrow M).length := sorry,
      rw ← list.cons_nth_le_drop_succ this,
      simp [matrix.mul_assoc],

    }

  }
end


#exit

lemma exists_is_last_diag_transvec_self_transvec_aux (M : matrix (fin r.succ) (fin r.succ) 𝕜)
  (hM : M (fin.last r) (fin.last r) ≠ 0) (j : ℕ) (hj : j < r.succ) :
  ∃ (L : list (matrix (fin r.succ) (fin r.succ) 𝕜)), ∀ i, i < j → (L.prod ⬝ M) i (fin.last r) = 0 :=
begin
  induction j with j IH,
  { refine ⟨list.nil, by simp⟩ },

end

#exit

  is_last_diag (L.prod ⬝ M ⬝ L'.prod) :=
begin
  let L := list.of_fn (λ i : fin r, transvection 𝕜 (fin.cast_succ i) (fin.last r)
    (-M (fin.cast_succ i) (fin.last r) / M (fin.last r) (fin.last r)),
end


#exit

lemma exists_is_last_diag_transvec_self_transvec (M : matrix (fin r.succ) (fin r.succ) R) :
  ∃ (L L' : list (matrix (fin r.succ) (fin r.succ) R)),
  is_last_diag (L.prod ⬝ M ⬝ L'.prod) :=
begin
  by_cases H : is_last_diag M, { refine ⟨list.nil, list.nil, by simpa using H⟩ },
  by_cases h : ∃ (i : fin r.succ), (i : ℕ) < r ∧ M i (fin.last r) ≠ 0,
  { rcases h with ⟨i, i_lt, hi⟩,

  }
end



end


#exit

lemma sl_non_abelian [nontrivial R] (h : 1 < fintype.card n) : ¬is_lie_abelian ↥(sl n R) :=
begin
  rcases fintype.exists_pair_of_one_lt_card h with ⟨j, i, hij⟩,
  let A := Eb R i j hij,
  let B := Eb R j i hij.symm,
  intros c,
  have c' : A.val ⬝ B.val = B.val ⬝ A.val, by { rw [← sub_eq_zero, ← sl_bracket, c.trivial], refl },
  have : (1 : R) = 0 := by simpa [matrix.mul_apply, hij] using (congr_fun (congr_fun c' i) i),
  exact one_ne_zero this,
end

end special_linear

namespace symplectic

/-- The matrix defining the canonical skew-symmetric bilinear form. -/
def J : matrix (l ⊕ l) (l ⊕ l) R := matrix.from_blocks 0 (-1) 1 0

/-- The symplectic Lie algebra: skew-adjoint matrices with respect to the canonical skew-symmetric
bilinear form. -/
def sp : lie_subalgebra R (matrix (l ⊕ l) (l ⊕ l) R) :=
  skew_adjoint_matrices_lie_subalgebra (J l R)

end symplectic

namespace orthogonal

/-- The definite orthogonal Lie subalgebra: skew-adjoint matrices with respect to the symmetric
bilinear form defined by the identity matrix. -/
def so : lie_subalgebra R (matrix n n R) :=
  skew_adjoint_matrices_lie_subalgebra (1 : matrix n n R)

@[simp] lemma mem_so (A : matrix n n R) : A ∈ so n R ↔ Aᵀ = -A :=
begin
  erw mem_skew_adjoint_matrices_submodule,
  simp only [matrix.is_skew_adjoint, matrix.is_adjoint_pair, matrix.mul_one, matrix.one_mul],
end

/-- The indefinite diagonal matrix with `p` 1s and `q` -1s. -/
def indefinite_diagonal : matrix (p ⊕ q) (p ⊕ q) R :=
  matrix.diagonal $ sum.elim (λ _, 1) (λ _, -1)

/-- The indefinite orthogonal Lie subalgebra: skew-adjoint matrices with respect to the symmetric
bilinear form defined by the indefinite diagonal matrix. -/
def so' : lie_subalgebra R (matrix (p ⊕ q) (p ⊕ q) R) :=
  skew_adjoint_matrices_lie_subalgebra $ indefinite_diagonal p q R

/-- A matrix for transforming the indefinite diagonal bilinear form into the definite one, provided
the parameter `i` is a square root of -1. -/
def Pso (i : R) : matrix (p ⊕ q) (p ⊕ q) R :=
  matrix.diagonal $ sum.elim (λ _, 1) (λ _, i)

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

lemma is_unit_Pso {i : R} (hi : i*i = -1) : is_unit (Pso p q R i) :=
⟨{ val     := Pso p q R i,
   inv     := Pso p q R (-i),
   val_inv := Pso_inv p q R hi,
   inv_val := by { apply matrix.nonsing_inv_left_right, exact Pso_inv p q R hi, }, },
rfl⟩

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
noncomputable def so_indefinite_equiv {i : R} (hi : i*i = -1) : so' p q R ≃ₗ⁅R⁆ so (p ⊕ q) R :=
begin
  apply (skew_adjoint_matrices_lie_subalgebra_equiv
    (indefinite_diagonal p q R) (Pso p q R i) (is_unit_Pso p q R hi)).trans,
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
def type_D := skew_adjoint_matrices_lie_subalgebra (JD l R)

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

lemma JD_transform : (PD l R)ᵀ ⬝ (JD l R) ⬝ (PD l R) = (2 : R) • (S l R) :=
begin
  have h : (PD l R)ᵀ ⬝ (JD l R) = matrix.from_blocks 1 1 1 (-1) := by
  { simp [PD, JD, matrix.from_blocks_transpose, matrix.from_blocks_multiply], },
  erw [h, S_as_blocks, matrix.from_blocks_multiply, matrix.from_blocks_smul],
  congr; simp [two_smul],
end

lemma PD_inv [invertible (2 : R)] : (PD l R) * (⅟(2 : R) • (PD l R)ᵀ) = 1 :=
begin
  have h : ⅟(2 : R) • (1 : matrix l l R) + ⅟(2 : R) • 1 = 1 := by
    rw [← smul_add, ← (two_smul R _), smul_smul, inv_of_mul_self, one_smul],
  erw [matrix.from_blocks_transpose, matrix.from_blocks_smul, matrix.mul_eq_mul,
    matrix.from_blocks_multiply],
  simp [h],
end

lemma is_unit_PD [invertible (2 : R)] : is_unit (PD l R) :=
⟨{ val     := PD l R,
   inv     := ⅟(2 : R) • (PD l R)ᵀ,
   val_inv := PD_inv l R,
   inv_val := by { apply matrix.nonsing_inv_left_right, exact PD_inv l R, }, },
rfl⟩

/-- An equivalence between two possible definitions of the classical Lie algebra of type D. -/
noncomputable def type_D_equiv_so' [invertible (2 : R)] :
  type_D l R ≃ₗ⁅R⁆ so' l l R :=
begin
  apply (skew_adjoint_matrices_lie_subalgebra_equiv (JD l R) (PD l R) (is_unit_PD l R)).trans,
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
def type_B := skew_adjoint_matrices_lie_subalgebra (JB l R)

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

lemma PB_inv [invertible (2 : R)] : (PB l R) * (matrix.from_blocks 1 0 0 (PD l R)⁻¹) = 1 :=
begin
  simp [PB, matrix.from_blocks_multiply, (PD l R).mul_nonsing_inv, is_unit_PD,
        ← (PD l R).is_unit_iff_is_unit_det]
end

lemma is_unit_PB [invertible (2 : R)] : is_unit (PB l R) :=
⟨{ val     := PB l R,
   inv     := matrix.from_blocks 1 0 0 (PD l R)⁻¹,
   val_inv := PB_inv l R,
   inv_val := by { apply matrix.nonsing_inv_left_right, exact PB_inv l R, }, },
rfl⟩

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
  simp only [indefinite_diagonal, matrix.diagonal, equiv.sum_assoc_apply_in1,
    matrix.reindex_lie_equiv_apply, matrix.minor_apply, equiv.symm_symm, matrix.reindex_apply,
    sum.elim_inl, if_true, eq_self_iff_true, matrix.one_apply_eq, matrix.from_blocks_apply₁₁,
    dmatrix.zero_apply, equiv.sum_assoc_apply_in2, if_false, matrix.from_blocks_apply₁₂,
    matrix.from_blocks_apply₂₁, matrix.from_blocks_apply₂₂, equiv.sum_assoc_apply_in3,
    sum.elim_inr];
  congr,
end

/-- An equivalence between two possible definitions of the classical Lie algebra of type B. -/
noncomputable def type_B_equiv_so' [invertible (2 : R)] :
  type_B l R ≃ₗ⁅R⁆ so' (unit ⊕ l) l R :=
begin
  apply (skew_adjoint_matrices_lie_subalgebra_equiv (JB l R) (PB l R) (is_unit_PB l R)).trans,
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
