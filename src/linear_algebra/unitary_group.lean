/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Shing Tak Lam
-/
import linear_algebra.matrix
import linear_algebra.nonsingular_inverse
import data.complex.basic

/-!
# The Unitrary Group O(n)

This file defines elements of the unitary group `unitary_group n`, also written `U(n)`,
consisting of all `n` by `n` complex matrices where the conjugate transpose is the inverse.
In addition, we define the group structure on `unitary_group n` and the embedding into the
general linear group `general_linear_group ℂ (n → ℂ)`.

## Main Definitions

 * `matrix.unitary_group` is the type of matrices where the transpose is the inverse
 * `matrix.unitary_group.group` is the group structure (under multiplication)
 * `matrix.unitary_group.embedding_GL` is the embedding `U(n) → GLₙ(ℝ)`

## References

 * https://en.wikipedia.org/wiki/Unitary_group

## Tags

matrix group, group, unitary group

-/

namespace matrix
universe u
open linear_map

section

variables {n m : Type*} [fintype n] [fintype m] [decidable_eq n] [decidable_eq m]

def conj_transpose (M : matrix n m ℂ) : matrix m n ℂ :=
  M.transpose.map complex.conj

localized "postfix `†`:1500 := conj_transpose" in matrix

lemma conj_transpose_eq_transpose_map_conj (M : matrix n m ℂ) : M† = (M.map complex.conj).transpose :=
begin
  ext; simp only [conj_transpose, map_apply, transpose_apply],
end

@[simp]
lemma conj_transpose_mul {p : Type*} [fintype p] [decidable_eq p] (M : matrix n m ℂ) (N : matrix m p ℂ) :
  (matrix.mul M N)† = matrix.mul N† M† := by simp [conj_transpose]

@[simp]
lemma conj_transpose_one : (1 : matrix n n ℂ)† = 1 := by simp [conj_transpose]

-- @[simp]
-- lemma conj_transpose_conj_transpose (M : matrix n m ℂ) : M†† = M := by simp [conj_transpose]

end

open_locale matrix

section

variables (n : Type u) [fintype n] [decidable_eq n]

def unitary_group := {M : matrix n n ℂ // M† * M = 1}

end

namespace unitary_group

variables {n : Type u} [decidable_eq n] [fintype n]

instance coe_matrix : has_coe (unitary_group n) (matrix n n ℂ) := ⟨subtype.val⟩

instance coe_fun : has_coe_to_fun (unitary_group n) :=
{ F   := λ _, n → n → ℂ,
  coe := λ A, A.val }

/--
  `to_lin' A` is matrix multiplication of vectors by `A`, as a linear map.

  After the group structure on `unitary_group n` is defined,
  we show in `to_linear_equiv` that this gives a linear equivalence.
-/
def to_lin' (A : unitary_group n) := matrix.to_lin' A

lemma ext_iff (A B : unitary_group n) : A = B ↔ ∀ i j, A i j = B i j :=
iff.trans subtype.ext_iff_val ⟨(λ h i j, congr_fun (congr_fun h i) j), matrix.ext⟩

@[ext] lemma ext (A B : unitary_group n) : (∀ i j, A i j = B i j) → A = B :=
(unitary_group.ext_iff A B).mpr

instance : has_inv (unitary_group n) :=
⟨λ A, ⟨A†, _⟩⟩

end unitary_group

end matrix
