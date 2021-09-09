/-
Copyright (c) 2020 Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jalex Stark, Scott Morrison, Eric Wieser
-/
import data.matrix.basic

/-!
# Matrices with a single non-zero element.

This file provides `matrix.std_basis_matrix`.
-/

variables {l m n : Type*}
variables {R α : Type*}

namespace matrix
open_locale matrix
open_locale big_operators

variables [decidable_eq l] [decidable_eq m] [decidable_eq n]

variables [semiring α]

/--
`std_basis_matrix i j a` is the matrix with `a` in the `i`-th row, `j`-th column,
and zeroes elsewhere.
-/
def std_basis_matrix (i : m) (j : n) (a : α) : matrix m n α :=
(λ i' j', if i' = i ∧ j' = j then a else 0)

@[simp] lemma smul_std_basis_matrix (i : m) (j : n) (a b : α) :
b • std_basis_matrix i j a = std_basis_matrix i j (b • a) :=
by { unfold std_basis_matrix, ext, simp }

@[simp] lemma std_basis_matrix_zero (i : m) (j : n) :
std_basis_matrix i j (0 : α) = 0 :=
by { unfold std_basis_matrix, ext, simp }

lemma std_basis_matrix_add (i : m) (j : n) (a b : α) :
std_basis_matrix i j (a + b) = std_basis_matrix i j a + std_basis_matrix i j b :=
begin
  unfold std_basis_matrix, ext,
  split_ifs with h; simp [h],
end

lemma matrix_eq_sum_std_basis (x : matrix n m α) [fintype n] [fintype m] :
  x = ∑ (i : n) (j : m), std_basis_matrix i j (x i j) :=
begin
  ext, symmetry,
  iterate 2 { rw finset.sum_apply },
  convert fintype.sum_eq_single i _,
  { simp [std_basis_matrix] },
  { intros j hj,
    simp [std_basis_matrix, hj.symm] }
end

-- TODO: tie this up with the `basis` machinery of linear algebra
-- this is not completely trivial because we are indexing by two types, instead of one

-- TODO: add `std_basis_vec`
lemma std_basis_eq_basis_mul_basis (i : m) (j : n) :
std_basis_matrix i j 1 = vec_mul_vec (λ i', ite (i = i') 1 0) (λ j', ite (j = j') 1 0) :=
begin
  ext, norm_num [std_basis_matrix, vec_mul_vec],
  split_ifs; tauto,
end

-- todo: the old proof used fintypes, I don't know `finsupp` but this feels generalizable
@[elab_as_eliminator] protected lemma induction_on' [fintype n]
  {X : Type*} [semiring X] {M : matrix n n X → Prop} (m : matrix n n X)
  (h_zero : M 0)
  (h_add : ∀p q, M p → M q → M (p + q))
  (h_std_basis : ∀ i j x, M (std_basis_matrix i j x)) :
  M m :=
begin
  rw [matrix_eq_sum_std_basis m, ← finset.sum_product'],
  apply finset.sum_induction _ _ h_add h_zero,
  { intros, apply h_std_basis, }
end

@[elab_as_eliminator] protected lemma induction_on [fintype n]
  [nonempty n] {X : Type*} [semiring X] {M : matrix n n X → Prop} (m : matrix n n X)
  (h_add : ∀p q, M p → M q → M (p + q))
  (h_std_basis : ∀ i j x, M (std_basis_matrix i j x)) :
  M m :=
matrix.induction_on' m
begin
  have i : n := classical.choice (by assumption),
  simpa using h_std_basis i i 0,
end
h_add h_std_basis

end matrix
