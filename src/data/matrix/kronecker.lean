/-
Copyright (c) 2021 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio, Eric Wieser
-/

import data.matrix.basic
import linear_algebra.tensor_product

/-!
# Kronecker product of matrices

This defines the [Kronecker product](https://en.wikipedia.org/wiki/Kronecker_product).

## Main definitions

* `matrix.kronecker_map`: A generalization of the Kronecker product, defined such that
  `kronecker_map f A B (i₁, i₂) (j₁, j₂) = f (A i₁ j₁) (B i₁ j₂)`.
* `matrix.kronecker_map_linear`: when `f` is bilinear, so is `kronecker_map f`.
* `matrix.kronecker`: A version of `kronecker_map` for when `f = (*)`. We provide the notation
  `A ⊗ₖ B` for `A.kronecker B` behind the locale `kronecker`.
* `matrix.kronecker_linear`: A version of `kronecker_map` for when `f = (*)`. We provide the notation
  `A ⊗ₖ B` for `A.kronecker B` behind the locale `kronecker`.
-/

namespace matrix

open_locale matrix

variables {R α α' β β' γ γ' : Type*}
variables {l m n p : Type*} [fintype l] [fintype m] [fintype n] [fintype p]
variables {l' m' n' p' : Type*} [fintype l'] [fintype m'] [fintype n'] [fintype p']

section kronecker_map

/-- Produce a matrix with `f` applied to every pair of elements from `A` and `B`. -/
@[simp] def kronecker_map (f : α → β → γ) (A : matrix l m α) (B : matrix n p β) :
  matrix (l × n) (m × p) γ
| i j := f (A i.1 j.1) (B i.2 j.2)

lemma kronecker_map_transpose (f : α → β → γ)
  (A : matrix l m α) (B : matrix n p β) :
  kronecker_map f Aᵀ Bᵀ = (kronecker_map f A B)ᵀ :=
ext $ λ i j, rfl

lemma kronecker_map_map_left (f : α' → β → γ) (g : α → α')
  (A : matrix l m α) (B : matrix n p β) :
  kronecker_map f (A.map g) B = kronecker_map (λ a b, f (g a) b) A B :=
ext $ λ i j, rfl

lemma kronecker_map_map_right (f : α → β' → γ) (g : β → β')
  (A : matrix l m α) (B : matrix n p β) :
  kronecker_map f A (B.map g) = kronecker_map (λ a b, f a (g b)) A B :=
ext $ λ i j, rfl

lemma kronecker_map_map (f : α → β → γ) (g : γ → γ')
  (A : matrix l m α) (B : matrix n p β) :
  (kronecker_map f A B).map g = kronecker_map (λ a b, g (f a b)) A B :=
ext $ λ i j, rfl

lemma kronecker_map_zero_left [has_zero α] [has_zero γ] (f : α → β → γ) (hf : ∀ b, f 0 b = 0)
  (B : matrix n p β) :
  kronecker_map f (0 : matrix l m α) B = 0:=
ext $ λ i j,hf _

lemma kronecker_map_zero_right [has_zero β] [has_zero γ] (f : α → β → γ) (hf : ∀ a, f a 0 = 0)
  (A : matrix l m α) :
  kronecker_map f A (0 : matrix n p β) = 0 :=
ext $ λ i j, hf _

lemma kronecker_map_add_left [has_add α] [has_add γ] (f : α → β → γ)
  (hf : ∀ a₁ a₂ b, f (a₁ + a₂) b = f a₁ b + f a₂ b)
  (A₁ A₂ : matrix l m α) (B : matrix n p β) :
  kronecker_map f (A₁ + A₂) B = kronecker_map f A₁ B + kronecker_map f A₂ B :=
ext $ λ i j, hf _ _ _

lemma kronecker_map_add_right [has_add β] [has_add γ] (f : α → β → γ)
  (hf : ∀ a b₁ b₂, f a (b₁ + b₂) = f a b₁ + f a b₂)
  (A : matrix l m α) (B₁ B₂ : matrix n p β) :
  kronecker_map f A (B₁ + B₂) = kronecker_map f A B₁ + kronecker_map f A B₂ :=
ext $ λ i j, hf _ _ _

lemma kronecker_map_smul_left [has_scalar R α] [has_scalar R γ] (f : α → β → γ)
  (hf : ∀ (r : R) a b, f (r • a) b = r • f a b) (r : R)
  (A : matrix l m α) (B : matrix n p β) :
  kronecker_map f (r • A) B = r • kronecker_map f A B :=
ext $ λ i j, hf _ _ _

lemma kronecker_map_smul_right [has_scalar R β] [has_scalar R γ] (f : α → β → γ)
  (hf : ∀ (r : R) a b, f a (r • b) = r • f a b) (r : R)
  (A : matrix l m α) (B : matrix n p β) :
  kronecker_map f A (r • B) = r • kronecker_map f A B :=
ext $ λ i j, hf _ _ _

lemma kronecker_map_diagonal_diagonal [has_zero α] [has_zero β] [has_zero γ]
  [decidable_eq m] [decidable_eq n]
  (f : α → β → γ) (hf₁ : ∀ b, f 0 b = 0) (hf₂ : ∀ a, f a 0 = 0) (a : m → α) (b : n → β):
  kronecker_map f (diagonal a) (diagonal b) = diagonal (λ mn, f (a mn.1) (b mn.2)) :=
begin
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩,
  simp [diagonal, apply_ite f, ite_and, ite_apply, apply_ite (f (a i₁)), hf₁, hf₂],
end

lemma kronecker_map_one_one [has_zero α] [has_zero β] [has_zero γ]
  [has_one α] [has_one β] [has_one γ]
  [decidable_eq m] [decidable_eq n]
  (f : α → β → γ) (hf₁ : ∀ b, f 0 b = 0) (hf₂ : ∀ a, f a 0 = 0) (hf₃ : f 1 1 = 1) :
  kronecker_map f (1 : matrix m m α) (1 : matrix n n β) = 1 :=
(kronecker_map_diagonal_diagonal _ hf₁ hf₂ _ _).trans $ by simp only [hf₃, diagonal_one]

/-- When `f` is bilinear then `matrix.kronecker_map f` is also bilinear. -/
@[simps]
def kronecker_map_linear [comm_semiring R]
  [add_comm_monoid α] [add_comm_monoid β] [add_comm_monoid γ]
  [module R α] [module R β] [module R γ]
  (f : α →ₗ[R] β →ₗ[R] γ) :
  matrix l m α →ₗ[R] matrix n p β →ₗ[R] matrix (l × n) (m × p) γ :=
linear_map.mk₂ R
  (kronecker_map (λ r s, f r s))
  (kronecker_map_add_left _ $ f.map_add₂)
  (kronecker_map_smul_left _ $ f.map_smul₂)
  (kronecker_map_add_right _ $ λ a, (f a).map_add)
  (kronecker_map_smul_right _ $ λ r a, (f a).map_smul r)

/-- `matrix.kronecker_map_linear` commutes with `⬝` if `f` commutes with `*`.

This is primarily used with `R = ℕ` to prove `matrix.mul_kronecker_mul`. -/
lemma kronecker_map_linear_mul_mul [comm_semiring R]
  [non_unital_non_assoc_semiring α] [non_unital_non_assoc_semiring β]
  [non_unital_non_assoc_semiring γ]
  [module R α] [module R β] [module R γ]
  (f : α →ₗ[R] β →ₗ[R] γ) (h_comm : ∀ a b a' b', f (a * b) (a' * b') = f a a' * f b b')
  (A : matrix l m α) (B : matrix m n α) (A' : matrix l' m' β) (B' : matrix m' n' β) :
  kronecker_map_linear f (A ⬝ B) (A' ⬝ B') =
    (kronecker_map_linear f A A') ⬝ (kronecker_map_linear f B B') :=
begin
  ext ⟨i, i'⟩ ⟨j, j'⟩,
  simp only [kronecker_map_linear_apply_apply, mul_apply, ← finset.univ_product_univ,
    finset.sum_product, kronecker_map],
  simp_rw [f.map_sum, linear_map.sum_apply, linear_map.map_sum, h_comm],
end

end kronecker_map

/-! ### Specialization to `matrix.kronecker_map (*)` -/

section kronecker

variables (R)

open_locale matrix

/-- The Kronecker product, with notation `⊗ₖ`. -/
def kronecker [has_mul α] :  matrix l m α → matrix n p α → matrix (l × n) (m × p) α :=
kronecker_map (*)

localized "infix ` ⊗ₖ `:100 := kronecker_map (*)" in kronecker

@[simp]
lemma kronecker_apply [has_mul α] (A : matrix l m α) (B : matrix n p α) (i₁ i₂ j₁ j₂) :
  (A ⊗ₖ B) (i₁, i₂) (j₁, j₂) = A i₁ j₁ * B i₂ j₂ := rfl

/-- `matrix.kronecker` as a bilinear map. -/
lemma kronecker_linear [comm_semiring R] [semiring α] [algebra R α] :
  matrix l m α →ₗ[R] matrix n p α →ₗ[R] matrix (l × n) (m × p) α :=
kronecker_map_linear (algebra.lmul R α).to_linear_map

lemma zero_kronecker [mul_zero_class α] (B : matrix n p α) : (0 : matrix l m α) ⊗ₖ B = 0 :=
kronecker_map_zero_left _ zero_mul B

lemma kronecker_zero [mul_zero_class α] (A : matrix l m α) : A ⊗ₖ (0 : matrix n p α) = 0 :=
kronecker_map_zero_right _ mul_zero A

lemma add_kronecker [distrib α] (A₁ A₂ : matrix l m α) (B : matrix n p α) :
  (A₁ + A₂) ⊗ₖ B = A₁ ⊗ₖ B + A₂ ⊗ₖ B :=
kronecker_map_add_left _ add_mul _ _ _

lemma kronecker_add [distrib α] (A : matrix l m α) (B₁ B₂ : matrix n p α) :
  A ⊗ₖ (B₁ + B₂) = A ⊗ₖ B₁ + A ⊗ₖ B₂ :=
kronecker_map_add_right _ mul_add _ _ _

@[simp] lemma one_kronecker_one [mul_zero_one_class α] [decidable_eq m] [decidable_eq n] :
  (1 : matrix m m α) ⊗ₖ (1 : matrix n n α) = 1 :=
kronecker_map_one_one _ zero_mul mul_zero (one_mul _)

lemma mul_kronecker_mul [comm_semiring α]
  (A : matrix l m α) (B : matrix m n α) (A' : matrix l' m' α) (B' : matrix m' n' α) :
  (A ⬝ B) ⊗ₖ (A' ⬝ B') = (A ⊗ₖ A') ⬝ (B ⊗ₖ B') :=
kronecker_map_linear_mul_mul (algebra.lmul ℕ α).to_linear_map mul_mul_mul_comm A B A' B'

end kronecker

end matrix
