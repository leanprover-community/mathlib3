/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import data.matrix.basic
import data.pequiv

/-!
# partial equivalences for matrices

Using partial equivalences to represent matrices.
This file introduces the function `pequiv.to_matrix`, which returns a matrix containing ones and
zeros. For any partial equivalence `f`, `f.to_matrix i j = 1 ↔ f i = some j`.

The following important properties of this function are proved
`to_matrix_trans : (f.trans g).to_matrix = f.to_matrix ⬝ g.to_matrix`
`to_matrix_symm  : f.symm.to_matrix = f.to_matrixᵀ`
`to_matrix_refl : (pequiv.refl n).to_matrix = 1`
`to_matrix_bot : ⊥.to_matrix = 0`

This theory gives the matrix representation of projection linear maps, and their right inverses.
For example, the matrix `(single (0 : fin 1) (i : fin n)).to_matrix` corresponds to the ith
projection map from R^n to R.

Any injective function `fin m → fin n` gives rise to a `pequiv`, whose matrix is the projection
map from R^m → R^n represented by the same function. The transpose of this matrix is the right
inverse of this map, sending anything not in the image to zero.

## notations

This file uses the notation ` ⬝ ` for `matrix.mul` and `ᵀ` for `matrix.transpose`.
-/

namespace pequiv
open matrix

universes u v

variables {k l m n : Type*}
variables {α : Type v}

open_locale matrix

/-- `to_matrix` returns a matrix containing ones and zeros. `f.to_matrix i j` is `1` if
  `f i = some j` and `0` otherwise -/
def to_matrix [decidable_eq n] [has_zero α] [has_one α] (f : m ≃. n) : matrix m n α
| i j := if j ∈ f i then 1 else 0

lemma mul_matrix_apply [fintype m] [decidable_eq m] [semiring α] (f : l ≃. m) (M : matrix m n α)
  (i j) : (f.to_matrix ⬝ M) i j = option.cases_on (f i) 0 (λ fi, M fi j) :=
begin
  dsimp [to_matrix, matrix.mul_apply],
  cases h : f i with fi,
  { simp [h] },
  { rw finset.sum_eq_single fi;
    simp [h, eq_comm] {contextual := tt} }
end

lemma to_matrix_symm [decidable_eq m] [decidable_eq n] [has_zero α] [has_one α] (f : m ≃. n) :
  (f.symm.to_matrix : matrix n m α) = f.to_matrixᵀ :=
by ext; simp only [transpose, mem_iff_mem f, to_matrix]; congr

@[simp] lemma to_matrix_refl [decidable_eq n] [has_zero α] [has_one α] :
  ((pequiv.refl n).to_matrix : matrix n n α) = 1 :=
by ext; simp [to_matrix, one_apply]; congr

lemma matrix_mul_apply [fintype m] [semiring α] [decidable_eq n] (M : matrix l m α) (f : m ≃. n)
  (i j) : (M ⬝ f.to_matrix) i j = option.cases_on (f.symm j) 0 (λ fj, M i fj) :=
begin
  dsimp [to_matrix, matrix.mul_apply],
  cases h : f.symm j with fj,
  { simp [h, ← f.eq_some_iff] },
  { rw finset.sum_eq_single fj,
    { simp [h, ← f.eq_some_iff], },
    { intros b H n, simp [h, ← f.eq_some_iff, n.symm], },
    { simp, } }
end

lemma to_pequiv_mul_matrix [fintype m] [decidable_eq m] [semiring α] (f : m ≃ m)
  (M : matrix m n α) : (f.to_pequiv.to_matrix ⬝ M) = λ i, M (f i) :=
by { ext i j, rw [mul_matrix_apply, equiv.to_pequiv_apply] }

lemma to_matrix_trans [fintype m] [decidable_eq m] [decidable_eq n] [semiring α]
  (f : l ≃. m) (g : m ≃. n) : ((f.trans g).to_matrix : matrix l n α) = f.to_matrix ⬝ g.to_matrix :=
begin
  ext i j,
  rw [mul_matrix_apply],
  dsimp [to_matrix, pequiv.trans],
  cases f i; simp
end

@[simp] lemma to_matrix_bot [decidable_eq n] [has_zero α] [has_one α] :
  ((⊥ : pequiv m n).to_matrix : matrix m n α) = 0 := rfl

lemma to_matrix_injective [decidable_eq n] [monoid_with_zero α] [nontrivial α] :
  function.injective (@to_matrix m n α _ _ _) :=
begin
  classical,
  assume f g,
  refine not_imp_not.1 _,
  simp only [matrix.ext_iff.symm, to_matrix, pequiv.ext_iff,
    not_forall, exists_imp_distrib],
  assume i hi,
  use i,
  cases hf : f i with fi,
  { cases hg : g i with gi,
    { cc },
    { use gi,
      simp, } },
  { use fi,
    simp [hf.symm, ne.symm hi] }
end

lemma to_matrix_swap [decidable_eq n] [ring α] (i j : n) :
  (equiv.swap i j).to_pequiv.to_matrix =
  (1 : matrix n n α) - (single i i).to_matrix - (single j j).to_matrix + (single i j).to_matrix +
    (single j i).to_matrix :=
begin
  ext,
  dsimp [to_matrix, single, equiv.swap_apply_def, equiv.to_pequiv, one_apply],
  split_ifs; simp * at *
end

@[simp] lemma single_mul_single [fintype n] [decidable_eq k] [decidable_eq m] [decidable_eq n]
  [semiring α] (a : m) (b : n) (c : k) :
  ((single a b).to_matrix : matrix _ _ α) ⬝ (single b c).to_matrix = (single a c).to_matrix :=
by rw [← to_matrix_trans, single_trans_single]

lemma single_mul_single_of_ne [fintype n] [decidable_eq n] [decidable_eq k]
  [decidable_eq m] [semiring α] {b₁ b₂ : n} (hb : b₁ ≠ b₂) (a : m) (c : k) :
  ((single a b₁).to_matrix : matrix _ _ α) ⬝ (single b₂ c).to_matrix = 0 :=
by rw [← to_matrix_trans, single_trans_single_of_ne hb, to_matrix_bot]

/-- Restatement of `single_mul_single`, which will simplify expressions in `simp` normal form,
  when associativity may otherwise need to be carefully applied. -/
@[simp] lemma single_mul_single_right [fintype n] [fintype k] [decidable_eq n] [decidable_eq k]
  [decidable_eq m] [semiring α] (a : m) (b : n) (c : k) (M : matrix k l α) :
  (single a b).to_matrix ⬝ ((single b c).to_matrix ⬝ M) = (single a c).to_matrix ⬝ M :=
by rw [← matrix.mul_assoc, single_mul_single]

/-- We can also define permutation matrices by permuting the rows of the identity matrix. -/
lemma equiv_to_pequiv_to_matrix [decidable_eq n] [has_zero α] [has_one α] (σ : equiv n n)
  (i j : n) :
  σ.to_pequiv.to_matrix i j = (1 : matrix n n α) (σ i) j :=
if_congr option.some_inj rfl rfl

end pequiv
