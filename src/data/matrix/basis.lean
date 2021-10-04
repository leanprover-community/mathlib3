/-
Copyright (c) 2020 Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jalex Stark, Scott Morrison, Eric Wieser, Oliver Nash
-/
import data.matrix.basic
import linear_algebra.matrix.trace

/-!
# Matrices with a single non-zero element.

This file provides `matrix.std_basis_matrix`. The matrix `matrix.std_basis_matrix i j c` has `c`
at position `(i, j)`, and zeroes elsewhere.
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
(λ i' j', if i = i' ∧ j = j' then a else 0)

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
    simp [std_basis_matrix, hj], }
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
@[elab_as_eliminator] protected lemma induction_on' [fintype m] [fintype n]
  {P : matrix m n α → Prop} (M : matrix m n α)
  (h_zero : P 0)
  (h_add : ∀ p q, P p → P q → P (p + q))
  (h_std_basis : ∀ (i : m) (j : n) (x : α), P (std_basis_matrix i j x)) :
  P M :=
begin
  rw [matrix_eq_sum_std_basis M, ← finset.sum_product'],
  apply finset.sum_induction _ _ h_add h_zero,
  { intros, apply h_std_basis, }
end

@[elab_as_eliminator] protected lemma induction_on [fintype m] [fintype n]
  [nonempty m] [nonempty n] {P : matrix m n α → Prop} (M : matrix m n α)
  (h_add : ∀ p q, P p → P q → P (p + q))
  (h_std_basis : ∀ i j x, P (std_basis_matrix i j x)) :
  P M :=
matrix.induction_on' M
begin
  inhabit m,
  inhabit n,
  simpa using h_std_basis (default m) (default n) 0,
end
h_add h_std_basis

namespace std_basis_matrix

section

variables (i : m) (j : n) (c : α) (i' : m) (j' : n)

@[simp] lemma apply_same : std_basis_matrix i j c i j = c := if_pos (and.intro rfl rfl)

@[simp] lemma apply_of_ne (h : ¬((i = i') ∧ (j = j'))) :
  std_basis_matrix i j c i' j' = 0 :=
by { simp only [std_basis_matrix, and_imp, ite_eq_right_iff], tauto }

@[simp] lemma apply_of_row_ne {i i' : m} (hi : i ≠ i') (j j' : n) (a : α) :
  std_basis_matrix i j a i' j' = 0 :=
by simp [hi]

@[simp] lemma apply_of_col_ne (i i' : m) {j j' : n} (hj : j ≠ j') (a : α) :
  std_basis_matrix i j a i' j' = 0 :=
by simp [hj]

end

section

variables (i j : n) (c : α) (i' j' : n)

@[simp] lemma diag_zero (h : j ≠ i) : diag n α α (std_basis_matrix i j c) = 0 :=
funext $ λ k, if_neg $ λ ⟨e₁, e₂⟩, h (e₂.trans e₁.symm)

variable [fintype n]

lemma trace_zero (h : j ≠ i) : trace n α α (std_basis_matrix i j c) = 0 := by simp [h]

@[simp] lemma mul_left_apply_same (b : n) (M : matrix n n α) :
  (std_basis_matrix i j c ⬝ M) i b = c * M j b :=
by simp [mul_apply, std_basis_matrix]

@[simp] lemma mul_right_apply_same (a : n) (M : matrix n n α) :
  (M ⬝ std_basis_matrix i j c) a j = M a i * c :=
by simp [mul_apply, std_basis_matrix, mul_comm]

@[simp] lemma mul_left_apply_of_ne (a b : n) (h : a ≠ i) (M : matrix n n α) :
  (std_basis_matrix i j c ⬝ M) a b = 0 :=
by simp [mul_apply, h.symm]

@[simp] lemma mul_right_apply_of_ne (a b : n) (hbj : b ≠ j) (M : matrix n n α) :
  (M ⬝ std_basis_matrix i j c) a b = 0 :=
by simp [mul_apply, hbj.symm]

@[simp] lemma mul_same (k : n) (d : α) :
  std_basis_matrix i j c ⬝ std_basis_matrix j k d = std_basis_matrix i k (c * d) :=
begin
  ext a b,
  simp only [mul_apply, std_basis_matrix, boole_mul],
  by_cases h₁ : i = a; by_cases h₂ : k = b;
  simp [h₁, h₂],
end

@[simp] lemma mul_of_ne {k l : n} (h : j ≠ k) (d : α) :
  std_basis_matrix i j c ⬝ std_basis_matrix k l d = 0 :=
begin
  ext a b,
  simp only [mul_apply, dmatrix.zero_apply, boole_mul, std_basis_matrix],
  by_cases h₁ : i = a;
  simp [h₁, h, h.symm],
end

end

end std_basis_matrix

end matrix
