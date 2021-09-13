/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lu-Ming Zhang
-/
import linear_algebra.matrix.symmetric

/-!
# Circulant matrices

This file contains the definition and basic results about circulant matrices.
Given a vector `v : I → α` indexed by a type that is endowed with subtraction,
`matrix.circulant v` is the matrix whose `(i, j)`th entry is `v (i - j)`.

## Main results

- `matrix.circulant`: the circulant matrix generated by a given vector `v : I → α`.
- `matrix.circulant_mul`: the product of two circulant matrices `circulant v` and `circulant w` is
                          the circulant matrix generated by `mul_vec (circulant v) w`.
- `matrix.circulant_mul_comm`: multiplication of circulant matrices commutes when the elements do.

## Implementation notes

`matrix.fin.foo` is the `fin n` version of `matrix.foo`.
Namely, the index type of the circulant matrices in discussion is `fin n`.

## Tags

circulant, matrix
-/

variables {α β I J R : Type*} {n : ℕ}

namespace matrix

open function
open_locale matrix big_operators

/-- Given the condition `[has_sub I]` and a vector `v : I → α`,
    we define `circulant v` to be the circulant matrix generated by `v` of type `matrix I I α`.
    The `(i,j)`th entry is defined to be `v (i - j)`. -/
@[simp]
def circulant [has_sub I] (v : I → α) : matrix I I α
| i j := v (i - j)

lemma circulant_col_zero_eq [add_group I] (v : I → α) (i : I) : circulant v i 0 = v i :=
congr_arg v (sub_zero _)

lemma circulant_injective [add_group I] : injective (circulant : (I → α) → matrix I I α) :=
begin
  intros v w h,
  ext k,
  rw [← circulant_col_zero_eq v, ← circulant_col_zero_eq w, h]
end

lemma fin.circulant_injective : ∀ n, injective (λ v : fin n → α, circulant v)
| 0     := dec_trivial
| (n+1) := circulant_injective

@[simp] lemma circulant_inj [add_group I] {v w : I → α} :
  circulant v = circulant w ↔ v = w :=
circulant_injective.eq_iff

@[simp] lemma fin.circulant_inj {v w : fin n → α} :
  circulant v = circulant w ↔ v = w :=
(fin.circulant_injective n).eq_iff

lemma transpose_circulant [add_group I] (v : I → α) :
  (circulant v)ᵀ = circulant (λ i, v (-i)) :=
by ext; simp

lemma conj_transpose_circulant [has_star α] [add_group I] (v : I → α) :
  (circulant v)ᴴ = circulant (star (λ i, v (-i))) :=
by ext; simp

lemma fin.transpose_circulant : ∀ {n} (v : fin n → α), (circulant v)ᵀ =  circulant (λ i, v (-i))
| 0     := dec_trivial
| (n+1) := transpose_circulant

lemma fin.conj_transpose_circulant [has_star α] :
  ∀ {n} (v : fin n → α), (circulant v)ᴴ = circulant (star (λ i, v (-i)))
| 0     := dec_trivial
| (n+1) := conj_transpose_circulant

lemma map_circulant [has_sub I] (v : I → α) (f : α → β) :
  (circulant v).map f = circulant (λ i, f (v i)) :=
ext $ λ _ _, rfl

lemma circulant_neg [has_neg α] [has_sub I] (v : I → α) :
  circulant (- v) = - circulant v :=
ext $ λ _ _, rfl

@[simp] lemma circulant_zero (α I) [has_zero α] [has_sub I] :
  circulant 0 = (0 : matrix I I α) :=
ext $ λ _ _, rfl

lemma circulant_add [has_add α] [has_sub I] (v w : I → α) :
  circulant (v + w) = circulant v + circulant w :=
ext $ λ _ _, rfl

lemma circulant_sub [has_sub α] [has_sub I] (v w : I → α) :
  circulant (v - w) = circulant v - circulant w :=
ext $ λ _ _, rfl

/-- The product of two circulant matrices `circulant v` and `circulant w` is
    the circulant matrix generated by `mul_vec (circulant v) w`. -/
lemma circulant_mul [semiring α] [fintype I] [add_group I] (v w : I → α) :
  circulant v ⬝ circulant w = circulant (mul_vec (circulant v) w) :=
begin
  ext i j,
  simp only [mul_apply, mul_vec, circulant, dot_product],
  refine fintype.sum_equiv (equiv.sub_right j) _ _ _,
  intro x,
  simp only [equiv.sub_right_apply, sub_sub_sub_cancel_right],
end

lemma fin.circulant_mul [semiring α] :
  ∀ {n} (v w : fin n → α), circulant v ⬝ circulant w = circulant (mul_vec (circulant v) w)
| 0     := dec_trivial
| (n+1) := circulant_mul

/-- Multiplication of circulant matrices commutes when the elements do. -/
lemma circulant_mul_comm
  [comm_semigroup α] [add_comm_monoid α] [fintype I] [add_comm_group I] (v w : I → α) :
  circulant v ⬝ circulant w = circulant w ⬝ circulant v :=
begin
  ext i j,
  simp only [mul_apply, circulant, mul_comm],
  refine fintype.sum_equiv ((equiv.sub_left i).trans (equiv.add_right j)) _ _ _,
  intro x,
  congr' 2,
  { simp },
  { simp only [equiv.coe_add_right, function.comp_app,
               equiv.coe_trans, equiv.sub_left_apply],
    abel }
end

lemma fin.circulant_mul_comm [comm_semigroup α] [add_comm_monoid α] :
  ∀ {n} (v w : fin n → α), circulant v ⬝ circulant w = circulant w ⬝ circulant v
| 0     := dec_trivial
| (n+1) := circulant_mul_comm

/-- `k • circulant v` is another circulantcluant matrix `circulant (k • v)`. -/
lemma circulant_smul [has_sub I] [has_scalar R α] (k : R) (v : I → α) :
  circulant (k • v) = k • circulant v :=
by ext; simp

@[simp] lemma circulant_single_one (α I) [has_zero α] [has_one α] [decidable_eq I] [add_group I] :
  circulant (pi.single 0 1 : I → α) = (1 : matrix I I α) :=
by { ext i j, simp only [circulant, one_apply, pi.single_apply, sub_eq_zero], congr }

@[simp] lemma circulant_single [semiring α] (I) [decidable_eq I] [add_group I] [fintype I] (a : α) :
  circulant (pi.single 0 a : I → α) = scalar I a :=
begin
  ext i j,
  simp [pi.single_apply, one_apply, sub_eq_zero],
end

/-- Note we use `↑i = 0` instead of `i = 0` as `fin 0` has no `0`. This means that we cannot state this with
`pi.single` as we did with `matrix.circulant_single`. -/
lemma fin.circulant_ite (α) [has_zero α] [has_one α] :
  ∀ n, circulant (λ i, ite (↑i = 0) 1 0 : fin n → α) = 1
| 0     := dec_trivial
| (n+1) :=
begin
  rw [←circulant_single_one],
  congr' with j,
  simp only [pi.single_apply, fin.ext_iff],
  congr
end

/-- The circulant matrix `circulant v` is symmetric iff `∀ i j, v (j - i) = v (i - j)`. -/
lemma circulant_is_symm_iff' [has_sub I] {v : I → α} :
  (circulant v).is_symm ↔ ∀ i j, v (j - i) = v (i - j) :=
by simp [is_symm.ext_iff, circulant]

/-- The circulant matrix `circulant v` is symmetric iff `v (- i) = v i` if `[add_group I]`. -/
lemma circulant_is_symm_iff [add_group I] {v : I → α} :
  (circulant v).is_symm ↔ ∀ i, v (- i) = v i :=
begin
  rw [circulant_is_symm_iff'],
  split,
  { intros h i, convert h i 0; simp },
  { intros h i j, convert h (i - j), simp }
end

lemma fin.circulant_is_symm_iff :
  ∀ {n} {v : fin n → α}, (circulant v).is_symm ↔ ∀ i, v (- i) = v i
| 0     := λ v, by simp only [circulant_is_symm_iff', is_empty.forall_iff]
| (n+1) := λ v, circulant_is_symm_iff

/-- If `circulant v` is symmetric, `∀ i j : I, v (j - i) = v (i - j)`. -/
lemma circulant_is_symm_apply' [has_sub I] {v : I → α} (h : (circulant v).is_symm) (i j : I) :
  v (j - i) = v (i - j) :=
circulant_is_symm_iff'.1 h i j

/-- If `circulant v` is symmetric, `∀ i j : I, v (- i) = v i`. -/
lemma circulant_is_symm_apply [add_group I] {v : I → α} (h : (circulant v).is_symm) (i : I) :
  v (-i) = v i :=
circulant_is_symm_iff.1 h i

lemma fin.circulant_is_symm_apply {v : fin n → α} (h : (circulant v).is_symm) (i : fin n) :
  v (-i) = v i :=
fin.circulant_is_symm_iff.1 h i

end matrix
