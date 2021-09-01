/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Lu-Ming Zhang.
-/
import data.matrix.notation
import linear_algebra.matrix.trace
import data.complex.basic

/-!
# Hadamard product of matrices

This file defines the Hadamard product `matrix.Hadamard`
and contains basic properties about them.

## Main definition

- `matrix.Hadamard`: defines the Hadamard product,
  which is the pointwise product of two matrices of the same size.

## Notation

* `⊙`: the Hadamard product `matrix.Hadamard`;

## References

*  <https://en.wikipedia.org/wiki/Hadamard_product_(matrices)>

## Tags

Hadamard product, Kronecker product, Hadamard, Kronecker
-/

variables {α β γ I J K L M N: Type*}
variables {R : Type*}
variables {m n p q r s t: ℕ}
variables [fintype I] [fintype J] [fintype K] [fintype L] [fintype M] [fintype N]

namespace matrix
open_locale matrix big_operators
open complex

def Hadamard [has_mul α] (A : matrix I J α) (B : matrix I J α) :
matrix I J α :=
λ i j, (A i j) * (B i j)

localized "infix `⊙`:100 := matrix.Hadamard" in matrix -- declares the notation

section basic_properties

variables (A : matrix I J α) (B : matrix I J α) (C : matrix I J α)

/- commutativity -/
lemma Hadamard_comm [comm_semigroup α] : A ⊙ B = B ⊙ A :=
by ext; simp [Hadamard, mul_comm]

/- associativity -/
lemma Hadamard_assoc [semigroup α] : A ⊙ B ⊙ C = A ⊙ (B ⊙ C) :=
by ext; simp [Hadamard, mul_assoc]

/- distributivity -/
lemma Hadamard_add [distrib α] : A ⊙ (B + C) = A ⊙ B + A ⊙ C :=
by ext; simp [Hadamard, left_distrib]

lemma add_Hadamard [distrib α] : (B + C) ⊙ A = B ⊙ A + C ⊙ A :=
by ext; simp [Hadamard, right_distrib]


/- scalar multiplication -/
section scalar

@[simp] lemma smul_Hadamard
[has_mul α] [has_scalar R α] [is_scalar_tower R α α] (k : R) :
(k • A) ⊙ B = k • A ⊙ B :=
by {ext, simp [Hadamard], exact smul_assoc _ (A i j) _}

@[simp] lemma Hadamard_smul
[has_mul α] [has_scalar R α] [smul_comm_class R α α] (k : R):
A ⊙ (k • B) = k • A ⊙ B :=
by {ext, simp [Hadamard], exact (smul_comm k (A i j) (B i j)).symm}

end scalar

section zero

variables [mul_zero_class α]

@[simp] lemma Hadamard_zero : A ⊙ (0 : matrix I J α) = 0 :=
by ext; simp [Hadamard]

@[simp] lemma zero_Hadamard : (0 : matrix I J α) ⊙ A = 0 :=
by ext; simp [Hadamard]

end zero

section trace

variables [semiring β] [semiring R] [comm_semiring α] [module β α] [module R ℂ]
variables [decidable_eq I] [decidable_eq J]

lemma trace_identity (v : I → α) (w : J → α):
dot_product (vec_mul  v  (A ⊙ B)) w =
trace I β α ((diagonal v)ᵀ ⬝ A ⬝ (diagonal w) ⬝ Bᵀ) :=
begin
  simp [dot_product, vec_mul, Hadamard, finset.sum_mul],
  rw finset.sum_comm,
  apply finset.sum_congr, refl, intros i hi,
  simp [diagonal, transpose, matrix.mul, dot_product],
  apply finset.sum_congr, refl, intros j hj,
  ring,
end

lemma sum_Hadamard_eq:
∑ (i : I) (j : J), (A ⊙ B) i j = trace I β α (A ⬝ Bᵀ) :=
begin
  have h:= trace_identity A B (λ i, 1 : I → α) (λ i, 1 : J → α),
  simp [vec_mul, dot_product] at h,
  rw finset.sum_comm at h,
  assumption,
  exact β, assumption, assumption,
end

lemma trace_identity_ℂ
(M₁ : matrix I J ℂ) (M₂ : matrix I J ℂ) (v : I → ℂ) (w : J → ℂ) :
dot_product (vec_mul (star v)  (M₁ ⊙ M₂)) w =
trace I R ℂ ((diagonal v)ᴴ ⬝ M₁ ⬝ (diagonal w) ⬝ M₂ᵀ) :=
begin
  simp [dot_product, vec_mul, Hadamard, finset.sum_mul],
  rw finset.sum_comm,
  apply finset.sum_congr, refl, intros i hi,
  simp [diagonal, transpose, conj_transpose, matrix.mul, dot_product],
  apply finset.sum_congr, refl, intros j hj,
  ring_nf,
end

end trace

end basic_properties

end matrix
