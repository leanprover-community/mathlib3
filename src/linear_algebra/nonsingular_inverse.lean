/-
  Copyright (c) 2019 Tim Baanen. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Tim Baanen.

  Inverses for nonsingular square matrices.
-/
import algebra.big_operators
import data.matrix.basic
import linear_algebra.determinant

/-!
# Nonsingular inverses

In this file, we define an inverse for square matrices of invertible
determinant. For matrices that are not square or not of full rank, there is a
more general notion of pseudoinverses. Unfortunately, the definition of
pseudoinverses is typically in terms of inverses of nonsingular matrices, so we
need to define those first. The file also doesn't define a `has_inv` instance
for `matrix` so that can be used for the pseudoinverse instead.

The definition of inverse used in this file is the one given by Cramer's rule.
The vectors returned by Cramer's rule are given by the linear map `cramer`.
Using Cramer's rule, we can compute for each matrix `A` the matrix `adjugate A`,
which we then prove behaves like `det A • A⁻¹`. Finally, we show that dividing
the adjugate by `det A` (if possible), giving a matrix `nonsing_inv A`, will
result in a multiplicative inverse to `A`.

## References

  * https://en.wikipedia.org/wiki/Cramer's_rule#Finding_inverse_matrix

## Tags

matrix inverse, cramer, cramer's rule, adjugate
-/

namespace matrix
universes u v
variables {n : Type u} [fintype n] [decidable_eq n] {α : Type v}
open_locale matrix
open equiv equiv.perm finset

section replace

/-- Replace the `i`th column of matrix `A` with the values in `b`. -/
def replace_column (A : matrix n n α) (i : n) (b : n → α) : matrix n n α :=
function.update A i b

/-- Replace the `i`th row of matrix `A` with the values in `b`. -/
def replace_row (A : matrix n n α) (j : n) (b : n → α) : matrix n n α :=
λ i, function.update (A i) j (b i)

variables {A : matrix n n α} {i j : n} {b : n → α}

lemma replace_column_self : replace_column A i b i = b := function.update_same i b A
lemma replace_row_self : replace_row A j b i j = b i := function.update_same j (b i) (A i)

lemma replace_column_eq {i' : n} (h : i = i') : replace_column A i b i' = b :=
by {rw [h], apply replace_column_self}
lemma replace_row_eq {j' : n} (h : j = j') : replace_row A j b i j' = b i :=
by {rw [h], apply replace_row_self}

lemma replace_column_ne {i' : n} (i_ne : i' ≠ i) : replace_column A i b i' = A i' :=
function.update_noteq i_ne b A
lemma replace_row_ne {j' : n} (j_ne : j' ≠ j) : replace_row A j b i j' = A i j' :=
function.update_noteq j_ne (b i) (A i)

lemma replace_column_val {i' : n} : replace_column A i b i' j = if i' = i then b j else A i' j :=
begin
  by_cases i' = i,
  { rw [h, replace_column_self, if_pos rfl] },
  { rw [replace_column_ne h, if_neg h] }
end
lemma replace_row_val {j' : n} : replace_row A j b i j' = if j' = j then b i else A i j' :=
begin
  by_cases j' = j,
  { rw [h, replace_row_self, if_pos rfl] },
  { rw [replace_row_ne h, if_neg h] }
end

lemma replace_column_transpose : replace_column Aᵀ i b = (replace_row A i b)ᵀ :=
begin
  ext i' j,
  rw [transpose_val, replace_column_val, replace_row_val],
  refl
end
end replace

section cramer
/-!
  ### `cramer` section

  Introduce the linear map `cramer` with values defined by `cramer_map`.
  After defining `cramer_map` and showing it is linear,
  we will restrict our proofs to using `cramer`.
-/
variables [comm_ring α] (A : matrix n n α) (b : n → α)

/--
  The `cramer_map` sends a matrix `A` and vector `b` to the vector `x`,
  such that `A ⬝ x = b`.
-/
def cramer_map (i : n) : α := (A.replace_column i b).det

lemma cramer_map_is_linear (i : n) : is_linear_map α (λ b, cramer_map A b i) :=
begin
  have : Π {f : n → n} {i : n} (x : n → α),
    finset.prod univ (λ (i' : n), (replace_column A i x)ᵀ (f i') i')
    = finset.prod univ (λ (i' : n), if i' = i then x (f i') else A i' (f i')),
  { intros, congr, ext i', rw [transpose_val, replace_column_val] },
  split,
  { intros x y,
    repeat { rw [cramer_map, ←det_transpose, det] },
    rw [←sum_add_distrib],
    congr, ext σ,
    rw [←mul_add ↑↑(sign σ)],
    congr,
    repeat { erw [this, finset.prod_ite _ _ (id : α → α)] },
    erw [finset.filter_eq', if_pos (mem_univ i), prod_singleton, prod_singleton,
      prod_singleton, ←add_mul],
    refl
  },
  { intros c x,
    repeat { rw [cramer_map, ←det_transpose, det] },
    rw [smul_eq_mul, mul_sum],
    congr, ext σ,
    rw [←mul_assoc, mul_comm c, mul_assoc], congr,
    repeat { erw [this, finset.prod_ite _ _ (id : α → α)] },
    erw [finset.filter_eq', if_pos (mem_univ i),
      prod_singleton, prod_singleton, mul_assoc],
    refl
  }
end

lemma cramer_is_linear : is_linear_map α (cramer_map A) := begin
  split; intros; ext i,
  { apply (cramer_map_is_linear A i).1 },
  { apply (cramer_map_is_linear A i).2 }
end
/-- The linear map of vectors associated to Cramer's rule.

  To help the elaborator, we need to make the type `α` an explicit argument to
  `cramer`. Otherwise, the coercion `⇑(cramer A) : (n → α) → (n → α)` gives an
  error because it fails to infer the type (even though `α` can be inferred from
  `A : matrix n n α`).
-/
def cramer (α : Type v) [comm_ring α] (A : matrix n n α) : (n → α) →ₗ[α] (n → α) :=
is_linear_map.mk' (cramer_map A) (cramer_is_linear A)

lemma cramer_apply (i : n) : cramer α A b i = (A.replace_column i b).det := rfl

/-- Applying Cramer's rule to a column of the matrix gives a scaled basis vector. -/
lemma cramer_column_self (i : n) :
(@cramer _ _ _ α _ A) (A i) = (λ j, if i = j then A.det else 0) :=
begin
  ext j,
  rw cramer_apply,
  by_cases i = j,
  { -- i = j: this entry should be `A.det`
    rw [if_pos h, ←h],
    congr, ext i',
    by_cases h : i' = i, { rw [h, replace_column_self] }, { rw [replace_column_ne h]} },
  { -- i ≠ j: this entry should be 0
    rw [if_neg h],
    apply det_zero_of_column_eq h,
    rw [replace_column_self, replace_column_ne],
    apply h }
end

/-- Use linearity of `cramer` to take it out of a summation. -/
lemma sum_cramer {β} (s : finset β) (f : β → n → α) :
  s.sum (λ x, cramer α A (f x)) = cramer α A (sum s f) :=
(linear_map.map_sum (cramer α A)).symm

/-- Use linearity of `cramer` and vector evaluation to take `cramer A _ i` out of a summation. -/
lemma sum_cramer_apply {β} (s : finset β) (f : n → β → α) (i : n) :
s.sum (λ x, cramer α A (λ j, f j x) i) = cramer α A (λ (j : n), s.sum (f j)) i :=
calc s.sum (λ x, cramer α A (λ j, f j x) i)
    = s.sum (λ x, cramer α A (λ j, f j x)) i : (pi.finset_sum_apply i s _).symm
... = cramer α A (λ (j : n), s.sum (f j)) i :
  by { rw [sum_cramer, cramer_apply], congr, ext j, apply pi.finset_sum_apply }

end cramer

section adjugate
/-! ### `adjugate` section

Define the `adjugate` matrix and a few equations.
These will hold for any matrix over a commutative ring,
while the `inv` section is specifically for invertible matrices.
-/

variable [comm_ring α]
/-- The adjugate matrix is the transpose of the cofactor matrix.

  Typically, the cofactor matrix is defined by taking the determinant of minors,
  i.e. the matrix with a row and column removed. However, the proof of
  `adjugate_mul` becomes a lot easier if we replace the rows with others,
  exactly what the `cramer` map does.
-/
def adjugate (A : matrix n n α) : matrix n n α := λ i, cramer α A (λ j, if i = j then 1 else 0)

lemma adjugate_def (A : matrix n n α) :
  adjugate A = λ i, cramer α A (λ j, if i = j then 1 else 0) := rfl
lemma adjugate_val (A : matrix n n α) (i j : n) :
  adjugate A i j = (A.replace_column j (λ j, if i = j then 1 else 0)).det := rfl

lemma adjugate_transpose (A : matrix n n α) : (adjugate A)ᵀ = adjugate (Aᵀ) :=
begin
  ext i j,
  rw [transpose_val, adjugate_val, adjugate_val, replace_column_transpose, det_transpose],
  apply finset.sum_congr rfl,
  intros σ _,
  congr' 1,

  by_cases i = σ j,
  { -- Everything except `(i , j)` (= `(σ j , j)`) is given by A, and the rest is a single `1`.
    congr; ext j',
    have := (@equiv.injective _ _ σ j j' : σ j = σ j' → j = j'),
    rw [replace_column_val, replace_row_val],
    finish },
  { -- Otherwise, we need to show that there is a `0` somewhere in the product.
    have : univ.prod (λ (j' : n), replace_row A j (λ (i' : n), ite (i = i') 1 0) (σ j') j') = 0,
    { apply prod_eq_zero (mem_univ j),
      rw [replace_row_self],
      exact if_neg h
    },
    rw this,
    apply prod_eq_zero (mem_univ (σ⁻¹ i)),
    erw [replace_column_eq (apply_symm_apply σ i).symm],
    apply if_neg,
    intro h',
    exact h ((symm_apply_eq σ).mp h'.symm)
  }
end

lemma mul_adjugate_val (A : matrix n n α) (i j k) :
  A i k * adjugate A k j = cramer α A (λ j, if k = j then A i k else 0) j :=
begin
  erw [←smul_eq_mul, ←pi.smul_apply, ←linear_map.smul],
  congr, ext,
  rw [pi.smul_apply, smul_eq_mul, mul_ite]
end

lemma mul_adjugate (A : matrix n n α) : A ⬝ adjugate A = A.det • 1 := begin
  ext i j,
  rw [mul_val, smul_val, one_val, mul_ite],
  calc
    sum univ (λ (k : n), A i k * adjugate A k j)
        = sum univ (λ (k : n), cramer α A (λ j, if k = j then A i k else 0) j)
      : by {congr, ext k, apply mul_adjugate_val A i j k}
    ... = cramer α A (λ j, sum univ (λ (k : n), if k = j then A i k else 0)) j
      : sum_cramer_apply A univ (λ (j k : n), if k = j then A i k else 0) j
    ... = cramer α A (A i) j : by { rw [cramer_apply], congr, ext,
      rw [sum_ite_eq' univ x (A i), if_pos (mem_univ _)] }
    ... = if i = j then det A else 0 : by rw cramer_column_self
end

lemma adjugate_mul (A : matrix n n α) : adjugate A ⬝ A = A.det • 1 :=
calc adjugate A ⬝ A = (Aᵀ ⬝ (adjugate Aᵀ))ᵀ :
  by rw [←adjugate_transpose, ←transpose_mul, transpose_transpose]
... = A.det • 1 : by rw [mul_adjugate (Aᵀ), det_transpose, transpose_smul, transpose_one]

end adjugate

section inv
/-! ### `inv` section

Defines the matrix `nonsing_inv A` and proves it is the inverse matrix
of a square matrix `A` as long as `det A` has a multiplicative inverse.
-/

variables [comm_ring α] [has_inv α]

/-- The inverse of a nonsingular matrix.

  This is not the most general possible definition, so we don't instantiate `has_inv` (yet).
-/
def nonsing_inv (A : matrix n n α) : matrix n n α := (A.det)⁻¹ • adjugate A

lemma nonsing_inv_val (A : matrix n n α) (i j : n) :
  A.nonsing_inv i j = (A.det)⁻¹ * adjugate A i j := rfl

lemma transpose_nonsing_inv (A : matrix n n α) : (A.nonsing_inv)ᵀ = (Aᵀ).nonsing_inv :=
by {ext, simp [transpose_val, nonsing_inv_val, det_transpose, (adjugate_transpose A).symm]}

/-- The `nonsing_inv` of `A` is a right inverse. -/
theorem mul_nonsing_inv (A : matrix n n α) (inv_mul_cancel : A.det⁻¹ * A.det = 1) :
  A ⬝ nonsing_inv A = 1 :=
by erw [mul_smul, mul_adjugate, smul_smul, inv_mul_cancel, @one_smul _ _ _ (pi.mul_action _)]

/-- The `nonsing_inv` of `A` is a left inverse. -/
theorem nonsing_inv_mul (A : matrix n n α) (inv_mul_cancel : A.det⁻¹ * A.det = 1) :
  nonsing_inv A ⬝ A = 1 :=
have inv_mul_cancel' : (det Aᵀ)⁻¹ * det Aᵀ = 1 := by {rw det_transpose, assumption},
calc nonsing_inv A ⬝ A
    = (Aᵀ ⬝ nonsing_inv (Aᵀ))ᵀ : by rw [transpose_mul, transpose_nonsing_inv, transpose_transpose]
... = 1ᵀ                       : by rw [mul_nonsing_inv Aᵀ inv_mul_cancel']
... = 1                        : transpose_one

end inv
end matrix
