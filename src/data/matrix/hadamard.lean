/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lu-Ming Zhang
-/
import data.matrix.notation
import linear_algebra.matrix.trace
import data.complex.basic

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
open complex

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
by ext; simp [hadamard, mul_assoc]

/- distributivity -/
lemma hadamard_add [distrib α] : A ⊙ (B + C) = A ⊙ B + A ⊙ C :=
by ext; simp [hadamard, left_distrib]

lemma add_hadamard [distrib α] : (B + C) ⊙ A = B ⊙ A + C ⊙ A :=
by ext; simp [hadamard, right_distrib]


/- scalar multiplication -/
section scalar

@[simp] lemma smul_hadamard [has_mul α] [has_scalar R α] [is_scalar_tower R α α] (k : R) :
  (k • A) ⊙ B = k • A ⊙ B :=
by {ext, simp [hadamard], exact smul_assoc _ (A i j) _}

@[simp] lemma hadamard_smul[has_mul α] [has_scalar R α] [smul_comm_class R α α] (k : R):
  A ⊙ (k • B) = k • A ⊙ B :=
by {ext, simp [hadamard], exact (smul_comm k (A i j) (B i j)).symm}

end scalar

section zero

variables [mul_zero_class α]

@[simp] lemma hadamard_zero : A ⊙ (0 : matrix m n α) = 0 :=
by ext; simp [hadamard]

@[simp] lemma zero_hadamard : (0 : matrix m n α) ⊙ A = 0 :=
by ext; simp [hadamard]

end zero

section trace

variables [fintype m] [fintype n]
variables [comm_semiring α] [comm_semiring γ] [star_ring γ]
variables [semiring β] [module β α] [semiring R] [module R γ]

lemma trace_identity [decidable_eq m] [decidable_eq n] (v : m → α) (w : n → α):
dot_product (vec_mul  v  (A ⊙ B)) w =
trace m β α ((diagonal v) ⬝ A ⬝ (diagonal w) ⬝ Bᵀ) :=
begin
  simp [dot_product, vec_mul, hadamard, finset.sum_mul],
  rw finset.sum_comm,
  apply finset.sum_congr, refl, intros i hi,
  simp [diagonal, transpose, matrix.mul, dot_product],
  apply finset.sum_congr, refl, intros j hj,
  ring,
end

lemma sum_hadamard_eq:
∑ (i : m) (j : n), (A ⊙ B) i j = trace m β α (A ⬝ Bᵀ) :=
begin
  classical,
  have h:= trace_identity A B (λ i, 1 : m → α) (λ i, 1 : n → α),
  simp [vec_mul, dot_product] at h,
  rw finset.sum_comm at h,
  assumption,
  exact β, assumption, assumption,
end

/-- the `star` version of `trace_identity` -/
lemma trace_identity' [decidable_eq m] [decidable_eq n]
(M₁ : matrix m n γ) (M₂ : matrix m n γ) (v : m → γ) (w : n → γ) :
dot_product (vec_mul (star v)  (M₁ ⊙ M₂)) w =
trace m R γ ((diagonal v)ᴴ ⬝ M₁ ⬝ (diagonal w) ⬝ M₂ᵀ) :=
begin
  convert trace_identity _ _ _ _,
  simp,
end

end trace

end basic_properties

end matrix
