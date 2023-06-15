/-
Copyright (c) 2021 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio, Eric Wieser
-/

import data.matrix.basic
import data.matrix.block
import linear_algebra.matrix.determinant
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.tensor_product
import ring_theory.tensor_product

/-!
# Kronecker product of matrices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This defines the [Kronecker product](https://en.wikipedia.org/wiki/Kronecker_product).

## Main definitions

* `matrix.kronecker_map`: A generalization of the Kronecker product: given a map `f : α → β → γ`
  and matrices `A` and `B` with coefficients in `α` and `β`, respectively, it is defined as the
  matrix with coefficients in `γ` such that
  `kronecker_map f A B (i₁, i₂) (j₁, j₂) = f (A i₁ j₁) (B i₁ j₂)`.
* `matrix.kronecker_map_bilinear`: when `f` is bilinear, so is `kronecker_map f`.

## Specializations

* `matrix.kronecker`: An alias of `kronecker_map (*)`. Prefer using the notation.
* `matrix.kronecker_bilinear`: `matrix.kronecker` is bilinear

* `matrix.kronecker_tmul`: An alias of `kronecker_map (⊗ₜ)`. Prefer using the notation.
* `matrix.kronecker_tmul_bilinear`: `matrix.tmul_kronecker` is bilinear

## Notations

These require `open_locale kronecker`:

* `A ⊗ₖ B` for `kronecker_map (*) A B`. Lemmas about this notation use the token `kronecker`.
* `A ⊗ₖₜ B` and `A ⊗ₖₜ[R] B` for `kronecker_map (⊗ₜ) A B`.  Lemmas about this notation use the token
  `kronecker_tmul`.

-/

namespace matrix

open_locale matrix

variables {R α α' β β' γ γ' : Type*}
variables {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}

section kronecker_map

/-- Produce a matrix with `f` applied to every pair of elements from `A` and `B`. -/
def kronecker_map (f : α → β → γ) (A : matrix l m α) (B : matrix n p β) :
  matrix (l × n) (m × p) γ :=
of $ λ (i : l × n) (j : m × p), f (A i.1 j.1) (B i.2 j.2)

-- TODO: set as an equation lemma for `kronecker_map`, see mathlib4#3024
@[simp]
lemma kronecker_map_apply (f : α → β → γ) (A : matrix l m α) (B : matrix n p β) (i j) :
  kronecker_map f A B i j = f (A i.1 j.1) (B i.2 j.2) := rfl

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

@[simp] lemma kronecker_map_zero_left [has_zero α] [has_zero γ]
  (f : α → β → γ) (hf : ∀ b, f 0 b = 0) (B : matrix n p β) :
  kronecker_map f (0 : matrix l m α) B = 0:=
ext $ λ i j,hf _

@[simp] lemma kronecker_map_zero_right [has_zero β] [has_zero γ]
  (f : α → β → γ) (hf : ∀ a, f a 0 = 0) (A : matrix l m α) :
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

lemma kronecker_map_smul_left [has_smul R α] [has_smul R γ] (f : α → β → γ)
  (r : R) (hf : ∀ a b, f (r • a) b = r • f a b) (A : matrix l m α) (B : matrix n p β) :
  kronecker_map f (r • A) B = r • kronecker_map f A B :=
ext $ λ i j, hf _ _

lemma kronecker_map_smul_right [has_smul R β] [has_smul R γ] (f : α → β → γ)
  (r : R) (hf : ∀ a b, f a (r • b) = r • f a b) (A : matrix l m α) (B : matrix n p β) :
  kronecker_map f A (r • B) = r • kronecker_map f A B :=
ext $ λ i j, hf _ _

lemma kronecker_map_diagonal_diagonal [has_zero α] [has_zero β] [has_zero γ]
  [decidable_eq m] [decidable_eq n]
  (f : α → β → γ) (hf₁ : ∀ b, f 0 b = 0) (hf₂ : ∀ a, f a 0 = 0) (a : m → α) (b : n → β):
  kronecker_map f (diagonal a) (diagonal b) = diagonal (λ mn, f (a mn.1) (b mn.2)) :=
begin
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩,
  simp [diagonal, apply_ite f, ite_and, ite_apply, apply_ite (f (a i₁)), hf₁, hf₂],
end

lemma kronecker_map_diagonal_right [has_zero β] [has_zero γ] [decidable_eq n]
  (f : α → β → γ) (hf : ∀ a, f a 0 = 0) (A : matrix l m α) (b : n → β):
  kronecker_map f A (diagonal b) = block_diagonal (λ i, A.map (λ a, f a (b i))) :=
begin
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩,
  simp [diagonal, block_diagonal, apply_ite (f (A i₁ j₁)), hf],
end

lemma kronecker_map_diagonal_left [has_zero α] [has_zero γ] [decidable_eq l]
  (f : α → β → γ) (hf : ∀ b, f 0 b = 0) (a : l → α) (B : matrix m n β) :
  kronecker_map f (diagonal a) B =
    matrix.reindex (equiv.prod_comm _ _) (equiv.prod_comm _ _)
      (block_diagonal (λ i, B.map (λ b, f (a i) b))) :=
begin
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩,
  simp [diagonal, block_diagonal, apply_ite f, ite_apply, hf],
end

@[simp] lemma kronecker_map_one_one [has_zero α] [has_zero β] [has_zero γ]
  [has_one α] [has_one β] [has_one γ] [decidable_eq m] [decidable_eq n]
  (f : α → β → γ) (hf₁ : ∀ b, f 0 b = 0) (hf₂ : ∀ a, f a 0 = 0) (hf₃ : f 1 1 = 1) :
  kronecker_map f (1 : matrix m m α) (1 : matrix n n β) = 1 :=
(kronecker_map_diagonal_diagonal _ hf₁ hf₂ _ _).trans $ by simp only [hf₃, diagonal_one]

lemma kronecker_map_reindex (f : α → β → γ) (el : l ≃ l') (em : m ≃ m') (en : n ≃ n')
  (ep : p ≃ p') (M : matrix l m α) (N : matrix n p β) :
  kronecker_map f (reindex el em M) (reindex en ep N) =
    reindex (el.prod_congr en) (em.prod_congr ep) (kronecker_map f M N) :=
by { ext ⟨i, i'⟩ ⟨j, j'⟩, refl }

lemma kronecker_map_reindex_left (f : α → β → γ) (el : l ≃ l') (em : m ≃ m') (M : matrix l m α)
  (N : matrix n n' β) : kronecker_map f (matrix.reindex el em M) N =
  reindex (el.prod_congr (equiv.refl _)) (em.prod_congr (equiv.refl _)) (kronecker_map f M N) :=
kronecker_map_reindex _ _ _ (equiv.refl _) (equiv.refl _) _ _

lemma kronecker_map_reindex_right (f : α → β → γ) (em : m ≃ m') (en : n ≃ n') (M : matrix l l' α)
  (N : matrix m n β) : kronecker_map f M (reindex em en N) =
  reindex ((equiv.refl _).prod_congr em) ((equiv.refl _).prod_congr en) (kronecker_map f M N) :=
kronecker_map_reindex _ (equiv.refl _) (equiv.refl _) _ _ _ _

lemma kronecker_map_assoc {δ ξ ω ω' : Type*} (f : α → β → γ) (g : γ → δ → ω) (f' : α → ξ → ω')
  (g' : β → δ → ξ) (A : matrix l m α) (B : matrix n p β) (D : matrix q r δ) (φ : ω ≃ ω')
  (hφ : ∀ a b d, φ (g (f a b) d) = f' a (g' b d)) :
  (reindex (equiv.prod_assoc l n q) (equiv.prod_assoc m p r)).trans (equiv.map_matrix φ)
    (kronecker_map g (kronecker_map f A B) D) = kronecker_map f' A (kronecker_map g' B D) :=
ext $ λ i j, hφ _ _ _

lemma kronecker_map_assoc₁ {δ ξ ω : Type*} (f : α → β → γ) (g : γ → δ → ω) (f' : α → ξ → ω)
  (g' : β → δ → ξ) (A : matrix l m α) (B : matrix n p β) (D : matrix q r δ)
  (h : ∀ a b d, (g (f a b) d) = f' a (g' b d)) :
  reindex (equiv.prod_assoc l n q) (equiv.prod_assoc m p r)
    (kronecker_map g (kronecker_map f A B) D) = kronecker_map f' A (kronecker_map g' B D) :=
ext $ λ i j, h _ _ _

/-- When `f` is bilinear then `matrix.kronecker_map f` is also bilinear. -/
@[simps]
def kronecker_map_bilinear [comm_semiring R]
  [add_comm_monoid α] [add_comm_monoid β] [add_comm_monoid γ]
  [module R α] [module R β] [module R γ]
  (f : α →ₗ[R] β →ₗ[R] γ) :
  matrix l m α →ₗ[R] matrix n p β →ₗ[R] matrix (l × n) (m × p) γ :=
linear_map.mk₂ R
  (kronecker_map (λ r s, f r s))
  (kronecker_map_add_left _ $ f.map_add₂)
  (λ r, kronecker_map_smul_left _ _ $ f.map_smul₂ _)
  (kronecker_map_add_right _ $ λ a, (f a).map_add)
  (λ r, kronecker_map_smul_right _ _ $ λ a, (f a).map_smul r)

/-- `matrix.kronecker_map_bilinear` commutes with `⬝` if `f` commutes with `*`.

This is primarily used with `R = ℕ` to prove `matrix.mul_kronecker_mul`. -/
lemma kronecker_map_bilinear_mul_mul [comm_semiring R]
  [fintype m] [fintype m'] [non_unital_non_assoc_semiring α]
  [non_unital_non_assoc_semiring β] [non_unital_non_assoc_semiring γ]
  [module R α] [module R β] [module R γ]
  (f : α →ₗ[R] β →ₗ[R] γ) (h_comm : ∀ a b a' b', f (a * b) (a' * b') = f a a' * f b b')
  (A : matrix l m α) (B : matrix m n α) (A' : matrix l' m' β) (B' : matrix m' n' β) :
  kronecker_map_bilinear f (A ⬝ B) (A' ⬝ B') =
    (kronecker_map_bilinear f A A') ⬝ (kronecker_map_bilinear f B B') :=
begin
  ext ⟨i, i'⟩ ⟨j, j'⟩,
  simp only [kronecker_map_bilinear_apply_apply, mul_apply, ← finset.univ_product_univ,
    finset.sum_product, kronecker_map_apply],
  simp_rw [f.map_sum, linear_map.sum_apply, linear_map.map_sum, h_comm],
end

/-- `trace` distributes over `matrix.kronecker_map_bilinear`.

This is primarily used with `R = ℕ` to prove `matrix.trace_kronecker`. -/
lemma trace_kronecker_map_bilinear [comm_semiring R]
  [fintype m] [fintype n] [add_comm_monoid α] [add_comm_monoid β] [add_comm_monoid γ]
  [module R α] [module R β] [module R γ]
  (f : α →ₗ[R] β →ₗ[R] γ) (A : matrix m m α) (B : matrix n n β) :
  trace (kronecker_map_bilinear f A B) = f (trace A) (trace B) :=
by simp_rw [matrix.trace, matrix.diag, kronecker_map_bilinear_apply_apply,
  linear_map.map_sum₂, map_sum, ←finset.univ_product_univ, finset.sum_product, kronecker_map_apply]

/-- `determinant` of `matrix.kronecker_map_bilinear`.

This is primarily used with `R = ℕ` to prove `matrix.det_kronecker`. -/
lemma det_kronecker_map_bilinear [comm_semiring R]
  [fintype m] [fintype n] [decidable_eq m] [decidable_eq n] [comm_ring α]
  [comm_ring β] [comm_ring γ]
  [module R α] [module R β] [module R γ]
  (f : α →ₗ[R] β →ₗ[R] γ) (h_comm : ∀ a b a' b', f (a * b) (a' * b') = f a a' * f b b')
  (A : matrix m m α) (B : matrix n n β) :
  det (kronecker_map_bilinear f A B) =
    det (A.map (λ a, f a 1)) ^ fintype.card n * det (B.map (λ b, f 1 b)) ^ fintype.card m :=
calc det (kronecker_map_bilinear f A B)
      = det (kronecker_map_bilinear f A 1 ⬝ kronecker_map_bilinear f 1 B)
    : by rw [←kronecker_map_bilinear_mul_mul f h_comm, matrix.mul_one, matrix.one_mul]
... = det (block_diagonal (λ _, A.map (λ a, f a 1)))
    * det (block_diagonal (λ _, B.map (λ b, f 1 b)))
    : begin
        rw [det_mul, ←diagonal_one, ←diagonal_one,
          kronecker_map_bilinear_apply_apply, kronecker_map_diagonal_right _ (λ _, _),
          kronecker_map_bilinear_apply_apply, kronecker_map_diagonal_left  _ (λ _, _),
          det_reindex_self],
        { exact linear_map.map_zero₂ _ _ },
        { exact map_zero _ },
      end
... = _ : by simp_rw [det_block_diagonal, finset.prod_const, finset.card_univ]

end kronecker_map

/-! ### Specialization to `matrix.kronecker_map (*)` -/

section kronecker

open_locale matrix

/-- The Kronecker product. This is just a shorthand for `kronecker_map (*)`. Prefer the notation
`⊗ₖ` rather than this definition. -/
@[simp] def kronecker [has_mul α] : matrix l m α → matrix n p α → matrix (l × n) (m × p) α :=
kronecker_map (*)

localized "infix (name := matrix.kronecker_map.mul)
  ` ⊗ₖ `:100 := matrix.kronecker_map (*)" in kronecker

@[simp]
lemma kronecker_apply [has_mul α] (A : matrix l m α) (B : matrix n p α) (i₁ i₂ j₁ j₂) :
  (A ⊗ₖ B) (i₁, i₂) (j₁, j₂) = A i₁ j₁ * B i₂ j₂ := rfl

/-- `matrix.kronecker` as a bilinear map. -/
def kronecker_bilinear [comm_semiring R] [semiring α] [algebra R α] :
  matrix l m α →ₗ[R] matrix n p α →ₗ[R] matrix (l × n) (m × p) α :=
kronecker_map_bilinear (algebra.lmul R α)

/-! What follows is a copy, in order, of every `matrix.kronecker_map` lemma above that has
hypotheses which can be filled by properties of `*`. -/

@[simp] lemma zero_kronecker [mul_zero_class α] (B : matrix n p α) : (0 : matrix l m α) ⊗ₖ B = 0 :=
kronecker_map_zero_left _ zero_mul B

@[simp] lemma kronecker_zero [mul_zero_class α] (A : matrix l m α) : A ⊗ₖ (0 : matrix n p α) = 0 :=
kronecker_map_zero_right _ mul_zero A

lemma add_kronecker [distrib α] (A₁ A₂ : matrix l m α) (B : matrix n p α) :
  (A₁ + A₂) ⊗ₖ B = A₁ ⊗ₖ B + A₂ ⊗ₖ B :=
kronecker_map_add_left _ add_mul _ _ _

lemma kronecker_add [distrib α] (A : matrix l m α) (B₁ B₂ : matrix n p α) :
  A ⊗ₖ (B₁ + B₂) = A ⊗ₖ B₁ + A ⊗ₖ B₂ :=
kronecker_map_add_right _ mul_add _ _ _

lemma smul_kronecker [monoid R] [monoid α] [mul_action R α] [is_scalar_tower R α α]
  (r : R) (A : matrix l m α) (B : matrix n p α) :
  (r • A) ⊗ₖ B = r • (A ⊗ₖ B) :=
kronecker_map_smul_left _ _ (λ _ _, smul_mul_assoc _ _ _) _ _

lemma kronecker_smul [monoid R] [monoid α] [mul_action R α] [smul_comm_class R α α]
  (r : R) (A : matrix l m α) (B : matrix n p α) :
  A ⊗ₖ (r • B) = r • (A ⊗ₖ B) :=
kronecker_map_smul_right _ _ (λ _ _, mul_smul_comm _ _ _) _ _

lemma diagonal_kronecker_diagonal [mul_zero_class α]
  [decidable_eq m] [decidable_eq n]
  (a : m → α) (b : n → α):
  (diagonal a) ⊗ₖ (diagonal b) = diagonal (λ mn, (a mn.1) * (b mn.2)) :=
kronecker_map_diagonal_diagonal _ zero_mul mul_zero _ _

lemma kronecker_diagonal [mul_zero_class α] [decidable_eq n] (A : matrix l m α) (b : n → α):
  A ⊗ₖ diagonal b = block_diagonal (λ i, mul_opposite.op (b i) • A) :=
kronecker_map_diagonal_right _ mul_zero _ _

lemma diagonal_kronecker [mul_zero_class α] [decidable_eq l](a : l → α) (B : matrix m n α) :
  diagonal a ⊗ₖ B =
    matrix.reindex (equiv.prod_comm _ _) (equiv.prod_comm _ _) (block_diagonal (λ i, a i • B)) :=
kronecker_map_diagonal_left _ zero_mul _ _

@[simp] lemma one_kronecker_one [mul_zero_one_class α] [decidable_eq m] [decidable_eq n] :
  (1 : matrix m m α) ⊗ₖ (1 : matrix n n α) = 1 :=
kronecker_map_one_one _ zero_mul mul_zero (one_mul _)

lemma kronecker_one [mul_zero_one_class α] [decidable_eq n] (A : matrix l m α) :
  A ⊗ₖ (1 : matrix n n α) = block_diagonal (λ i, A) :=
(kronecker_diagonal _ _).trans $ congr_arg _ $ funext $ λ _, matrix.ext $ λ _ _, mul_one _

lemma one_kronecker [mul_zero_one_class α] [decidable_eq l] (B : matrix m n α) :
  (1 : matrix l l α) ⊗ₖ B =
    matrix.reindex (equiv.prod_comm _ _) (equiv.prod_comm _ _) (block_diagonal (λ i, B)) :=
(diagonal_kronecker _ _).trans $
  congr_arg _ $ congr_arg _ $ funext $ λ _, matrix.ext $ λ _ _, one_mul _

lemma mul_kronecker_mul [fintype m] [fintype m'] [comm_semiring α]
  (A : matrix l m α) (B : matrix m n α) (A' : matrix l' m' α) (B' : matrix m' n' α) :
  (A ⬝ B) ⊗ₖ (A' ⬝ B') = (A ⊗ₖ A') ⬝ (B ⊗ₖ B') :=
kronecker_map_bilinear_mul_mul (algebra.lmul ℕ α).to_linear_map mul_mul_mul_comm A B A' B'

@[simp] lemma kronecker_assoc [semigroup α] (A : matrix l m α) (B : matrix n p α)
  (C : matrix q r α) : reindex (equiv.prod_assoc l n q) (equiv.prod_assoc m p r) ((A ⊗ₖ B) ⊗ₖ C) =
  A ⊗ₖ (B ⊗ₖ C) :=
kronecker_map_assoc₁ _ _ _ _ A B C mul_assoc

lemma trace_kronecker [fintype m] [fintype n] [semiring α]
  (A : matrix m m α) (B : matrix n n α) :
  trace (A ⊗ₖ B) = trace A * trace B :=
trace_kronecker_map_bilinear (algebra.lmul ℕ α).to_linear_map _ _

lemma det_kronecker [fintype m] [fintype n] [decidable_eq m] [decidable_eq n] [comm_ring R]
  (A : matrix m m R) (B : matrix n n R) :
  det (A ⊗ₖ B) = det A ^ fintype.card n * det B ^ fintype.card m :=
begin
  refine
    (det_kronecker_map_bilinear (algebra.lmul ℕ R).to_linear_map mul_mul_mul_comm _ _).trans _,
  congr' 3,
  { ext i j, exact mul_one _},
  { ext i j, exact one_mul _},
end

lemma inv_kronecker [fintype m] [fintype n] [decidable_eq m] [decidable_eq n] [comm_ring R]
  (A : matrix m m R) (B : matrix n n R) :
  (A ⊗ₖ B)⁻¹ = A⁻¹ ⊗ₖ B⁻¹ :=
begin
  -- handle the special cases where either matrix is not invertible
  by_cases hA : is_unit A.det, swap,
  { casesI is_empty_or_nonempty n,
    { exact subsingleton.elim _ _ },
    have hAB : ¬is_unit (A ⊗ₖ B).det,
    { refine mt (λ hAB, _) hA,
      rw det_kronecker at hAB,
      exact (is_unit_pow_iff fintype.card_ne_zero).mp (is_unit_of_mul_is_unit_left hAB) },
    rw [nonsing_inv_apply_not_is_unit _ hA, zero_kronecker, nonsing_inv_apply_not_is_unit _ hAB] },
  by_cases hB : is_unit B.det, swap,
  { casesI is_empty_or_nonempty m,
    { exact subsingleton.elim _ _ },
    have hAB : ¬is_unit (A ⊗ₖ B).det,
    { refine mt (λ hAB, _) hB,
      rw det_kronecker at hAB,
      exact (is_unit_pow_iff fintype.card_ne_zero).mp (is_unit_of_mul_is_unit_right hAB) },
    rw [nonsing_inv_apply_not_is_unit _ hB, kronecker_zero,
      nonsing_inv_apply_not_is_unit _ hAB] },
  -- otherwise follows trivially from `mul_kronecker_mul`
  { apply inv_eq_right_inv,
    rw [←mul_kronecker_mul, ←one_kronecker_one, mul_nonsing_inv _ hA, mul_nonsing_inv _ hB] },
end

end kronecker

/-! ### Specialization to `matrix.kronecker_map (⊗ₜ)` -/

section kronecker_tmul

variables (R)
open tensor_product
open_locale matrix tensor_product

section module

variables [comm_semiring R] [add_comm_monoid α] [add_comm_monoid β] [add_comm_monoid γ]
variables [module R α] [module R β] [module R γ]

/-- The Kronecker tensor product. This is just a shorthand for `kronecker_map (⊗ₜ)`.
Prefer the notation `⊗ₖₜ` rather than this definition. -/
@[simp] def kronecker_tmul :
  matrix l m α → matrix n p β → matrix (l × n) (m × p) (α ⊗[R] β) :=
kronecker_map (⊗ₜ)

localized "infix (name := matrix.kronecker_map.tmul)
  ` ⊗ₖₜ `:100 := matrix.kronecker_map (⊗ₜ)" in kronecker
localized "notation (name := matrix.kronecker_map.tmul')
  x ` ⊗ₖₜ[`:100 R `] `:0 y:100 := matrix.kronecker_map (tensor_product.tmul R) x y" in kronecker

@[simp]
lemma kronecker_tmul_apply (A : matrix l m α) (B : matrix n p β) (i₁ i₂ j₁ j₂) :
  (A ⊗ₖₜ B) (i₁, i₂) (j₁, j₂) = A i₁ j₁ ⊗ₜ[R] B i₂ j₂ := rfl

/-- `matrix.kronecker` as a bilinear map. -/
def kronecker_tmul_bilinear :
  matrix l m α →ₗ[R] matrix n p β →ₗ[R] matrix (l × n) (m × p) (α ⊗[R] β) :=
kronecker_map_bilinear (tensor_product.mk R α β)

/-! What follows is a copy, in order, of every `matrix.kronecker_map` lemma above that has
hypotheses which can be filled by properties of `⊗ₜ`. -/

@[simp] lemma zero_kronecker_tmul (B : matrix n p β) : (0 : matrix l m α) ⊗ₖₜ[R] B = 0 :=
kronecker_map_zero_left _ (zero_tmul α) B

@[simp] lemma kronecker_tmul_zero (A : matrix l m α) : A ⊗ₖₜ[R] (0 : matrix n p β) = 0 :=
kronecker_map_zero_right _ (tmul_zero β) A

lemma add_kronecker_tmul (A₁ A₂ : matrix l m α) (B : matrix n p α) :
  (A₁ + A₂) ⊗ₖₜ[R] B = A₁ ⊗ₖₜ B + A₂ ⊗ₖₜ B :=
kronecker_map_add_left _ add_tmul _ _ _

lemma kronecker_tmul_add (A : matrix l m α) (B₁ B₂ : matrix n p α) :
  A ⊗ₖₜ[R] (B₁ + B₂) = A ⊗ₖₜ B₁ + A ⊗ₖₜ B₂ :=
kronecker_map_add_right _ tmul_add _ _ _

lemma smul_kronecker_tmul
  (r : R) (A : matrix l m α) (B : matrix n p α) :
  (r • A) ⊗ₖₜ[R] B = r • (A ⊗ₖₜ B) :=
kronecker_map_smul_left _ _ (λ _ _, smul_tmul' _ _ _) _ _

lemma kronecker_tmul_smul
  (r : R) (A : matrix l m α) (B : matrix n p α) :
  A ⊗ₖₜ[R] (r • B) = r • (A ⊗ₖₜ B) :=
kronecker_map_smul_right _ _ (λ _ _, tmul_smul _ _ _) _ _

lemma diagonal_kronecker_tmul_diagonal
  [decidable_eq m] [decidable_eq n]
  (a : m → α) (b : n → α):
  (diagonal a) ⊗ₖₜ[R] (diagonal b) = diagonal (λ mn, a mn.1 ⊗ₜ b mn.2) :=
kronecker_map_diagonal_diagonal _ (zero_tmul _) (tmul_zero _) _ _

lemma kronecker_tmul_diagonal [decidable_eq n] (A : matrix l m α) (b : n → α):
  A ⊗ₖₜ[R] (diagonal b) = block_diagonal (λ i, A.map (λ a, a ⊗ₜ[R] b i)) :=
kronecker_map_diagonal_right _ (tmul_zero _) _ _

lemma diagonal_kronecker_tmul [decidable_eq l](a : l → α) (B : matrix m n α) :
  diagonal a ⊗ₖₜ[R] B =
    matrix.reindex (equiv.prod_comm _ _) (equiv.prod_comm _ _)
      (block_diagonal (λ i, B.map (λ b, a i ⊗ₜ[R] b))) :=
kronecker_map_diagonal_left _ (zero_tmul _) _ _

@[simp] lemma kronecker_tmul_assoc (A : matrix l m α) (B : matrix n p β) (C : matrix q r γ) :
  reindex (equiv.prod_assoc l n q) (equiv.prod_assoc m p r)
    (((A ⊗ₖₜ[R] B) ⊗ₖₜ[R] C).map (tensor_product.assoc _ _ _ _)) = A ⊗ₖₜ[R] (B ⊗ₖₜ[R] C) :=
ext $ λ i j, assoc_tmul _ _ _

lemma trace_kronecker_tmul [fintype m] [fintype n] (A : matrix m m α) (B : matrix n n β) :
  trace (A ⊗ₖₜ[R] B) = trace A ⊗ₜ[R] trace B :=
trace_kronecker_map_bilinear (tensor_product.mk R α β) _ _

end module

section algebra
open_locale kronecker
open algebra.tensor_product

section semiring
variables [comm_semiring R] [semiring α] [semiring β] [algebra R α] [algebra R β]

@[simp] lemma one_kronecker_tmul_one [decidable_eq m] [decidable_eq n] :
  (1 : matrix m m α) ⊗ₖₜ[R] (1 : matrix n n α) = 1 :=
kronecker_map_one_one _ (zero_tmul _) (tmul_zero _) rfl

lemma mul_kronecker_tmul_mul [fintype m] [fintype m']
  (A : matrix l m α) (B : matrix m n α) (A' : matrix l' m' β) (B' : matrix m' n' β) :
  (A ⬝ B) ⊗ₖₜ[R] (A' ⬝ B') = (A ⊗ₖₜ A') ⬝ (B ⊗ₖₜ B') :=
kronecker_map_bilinear_mul_mul (tensor_product.mk R α β) tmul_mul_tmul A B A' B'

end semiring

section comm_ring
variables [comm_ring R] [comm_ring α] [comm_ring β] [algebra R α] [algebra R β]

lemma det_kronecker_tmul [fintype m] [fintype n] [decidable_eq m] [decidable_eq n]
  (A : matrix m m α) (B : matrix n n β) :
  det (A ⊗ₖₜ[R] B) = (det A ^ fintype.card n) ⊗ₜ[R] (det B ^ fintype.card m) :=
begin
  refine
    (det_kronecker_map_bilinear (tensor_product.mk R α β) tmul_mul_tmul _ _).trans _,
  simp only [mk_apply, ←include_left_apply, ←include_right_apply] {eta := ff},
  simp only [←alg_hom.map_matrix_apply, ←alg_hom.map_det],
  simp only [include_left_apply, include_right_apply, tmul_pow, tmul_mul_tmul,
    one_pow, _root_.mul_one, _root_.one_mul],
end

end comm_ring

end algebra

-- insert lemmas specific to `kronecker_tmul` below this line

end kronecker_tmul

end matrix
