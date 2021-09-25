/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lu-Ming Zhang
-/
import data.matrix.notation
import linear_algebra.matrix.trace

/-!
# Hadamard product of matrices

This file defines the Hadamard product `matrix.hadamard`
and contains basic properties about them.

## Main definition

- `matrix.hadamard`: defines the Hadamard product,
  which is the pointwise product of two matrices of the same size.

## Notation

* `⊙`: the Hadamard product `matrix.hadamard`;

## References

*  <https://en.wikipedia.org/wiki/hadamard_product_(matrices)>

## Tags

hadamard product, hadamard
-/

variables {α β γ m n : Type*}
variables {R : Type*}

namespace matrix
open_locale matrix big_operators

/-- `matrix.hadamard` defines the Hadamard product,
    which is the pointwise product of two matrices of the same size.-/
@[simp]
def hadamard [has_mul α] (A : matrix m n α) (B : matrix m n α) : matrix m n α
| i j := A i j * B i j

localized "infix ` ⊙ `:100 := matrix.hadamard" in matrix

section basic_properties

variables (A : matrix m n α) (B : matrix m n α) (C : matrix m n α)

/- commutativity -/
lemma hadamard_comm [comm_semigroup α] : A ⊙ B = B ⊙ A :=
ext $ λ _ _, mul_comm _ _

/- associativity -/
lemma hadamard_assoc [semigroup α] : A ⊙ B ⊙ C = A ⊙ (B ⊙ C) :=
ext $ λ _ _, mul_assoc _ _ _

/- distributivity -/
lemma hadamard_add [distrib α] : A ⊙ (B + C) = A ⊙ B + A ⊙ C :=
ext $ λ _ _, left_distrib _ _ _

lemma add_hadamard [distrib α] : (B + C) ⊙ A = B ⊙ A + C ⊙ A :=
ext $ λ _ _, right_distrib _ _ _

/- scalar multiplication -/
section scalar

@[simp] lemma smul_hadamard [has_mul α] [has_scalar R α] [is_scalar_tower R α α] (k : R) :
  (k • A) ⊙ B = k • A ⊙ B :=
ext $ λ _ _, smul_mul_assoc _ _ _

@[simp] lemma hadamard_smul [has_mul α] [has_scalar R α] [smul_comm_class R α α] (k : R):
  A ⊙ (k • B) = k • A ⊙ B :=
ext $ λ _ _, mul_smul_comm _ _ _

end scalar

section zero

variables [mul_zero_class α]

@[simp] lemma hadamard_zero : A ⊙ (0 : matrix m n α) = 0 :=
ext $ λ _ _, mul_zero _

@[simp] lemma zero_hadamard : (0 : matrix m n α) ⊙ A = 0 :=
ext $ λ _ _, zero_mul _

end zero

section one

variables [decidable_eq n] [mul_zero_one_class α]
variables (M : matrix n n α)

lemma hadamard_one : M ⊙ (1 : matrix n n α) = diagonal (λ i, M i i) :=
by { ext, by_cases h : i = j; simp [h] }

lemma one_hadamard : (1 : matrix n n α) ⊙ M = diagonal (λ i, M i i) :=
by { ext, by_cases h : i = j; simp [h] }

end one

section diagonal

variables [decidable_eq n] [mul_zero_class α]

lemma diagonal_hadamard_diagonal (v : n → α) (w : n → α) :
  diagonal v ⊙ diagonal w = diagonal (v * w) :=
ext $ λ _ _, (apply_ite2 _ _ _ _ _ _).trans (congr_arg _ $ zero_mul 0)

end diagonal

section trace

variables [fintype m] [fintype n]
variables (R) [semiring α] [semiring R] [module R α]

lemma sum_hadamard_eq : ∑ (i : m) (j : n), (A ⊙ B) i j = trace m R α (A ⬝ Bᵀ) :=
rfl

lemma dot_product_vec_mul_hadamard [decidable_eq m] [decidable_eq n] (v : m → α) (w : n → α) :
  dot_product (vec_mul v (A ⊙ B)) w = trace m R α (diagonal v ⬝ A ⬝ (B ⬝ diagonal w)ᵀ) :=
begin
  rw [←sum_hadamard_eq, finset.sum_comm],
  simp [dot_product, vec_mul, finset.sum_mul, mul_assoc],
end

end trace

end basic_properties

end matrix
