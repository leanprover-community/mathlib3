/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lu-Ming Zhang
-/
import linear_algebra.matrix.symmetric

/-!
# Circulant matrices

This file contains the definition and basic results about circulant matrices.
Given a vector `v : n → α` indexed by a type that is endowed with subtraction,
`matrix.circulant v` is the matrix whose `(i, j)`th entry is `v (i - j)`.

## Main results

- `matrix.circulant`: the circulant matrix generated by a given vector `v : n → α`.
- `matrix.circulant_mul`: the product of two circulant matrices `circulant v` and `circulant w` is
                          the circulant matrix generated by `mul_vec (circulant v) w`.
- `matrix.circulant_mul_comm`: multiplication of circulant matrices commutes when the elements do.

## Implementation notes

`matrix.fin.foo` is the `fin n` version of `matrix.foo`.
Namely, the index type of the circulant matrices in discussion is `fin n`.

## Tags

circulant, matrix
-/

variables {α β m n R : Type*}

namespace matrix

open function
open_locale matrix big_operators

/-- Given the condition `[has_sub n]` and a vector `v : n → α`,
    we define `circulant v` to be the circulant matrix generated by `v` of type `matrix n n α`.
    The `(i,j)`th entry is defined to be `v (i - j)`. -/
@[simp]
def circulant [has_sub n] (v : n → α) : matrix n n α
| i j := v (i - j)

lemma circulant_col_zero_eq [add_group n] (v : n → α) (i : n) : circulant v i 0 = v i :=
congr_arg v (sub_zero _)

lemma circulant_injective [add_group n] : injective (circulant : (n → α) → matrix n n α) :=
begin
  intros v w h,
  ext k,
  rw [← circulant_col_zero_eq v, ← circulant_col_zero_eq w, h]
end

lemma fin.circulant_injective : ∀ n, injective (λ v : fin n → α, circulant v)
| 0     := dec_trivial
| (n+1) := circulant_injective

@[simp] lemma circulant_inj [add_group n] {v w : n → α} :
  circulant v = circulant w ↔ v = w :=
circulant_injective.eq_iff

@[simp] lemma fin.circulant_inj {n} {v w : fin n → α} :
  circulant v = circulant w ↔ v = w :=
(fin.circulant_injective n).eq_iff

lemma transpose_circulant [add_group n] (v : n → α) :
  (circulant v)ᵀ = circulant (λ i, v (-i)) :=
by ext; simv

lemma conj_transpose_circulant [has_star α] [add_group n] (v : n → α) :
  (circulant v)ᴴ = circulant (star (λ i, v (-i))) :=
by ext; simv

lemma fin.transpose_circulant : ∀ {n} (v : fin n → α), (circulant v)ᵀ =  circulant (λ i, v (-i))
| 0     := dec_trivial
| (n+1) := transpose_circulant

lemma fin.conj_transpose_circulant [has_star α] :
  ∀ {n} (v : fin n → α), (circulant v)ᴴ = circulant (star (λ i, v (-i)))
| 0     := dec_trivial
| (n+1) := conj_transpose_circulant

lemma map_circulant [has_sub n] (v : n → α) (f : α → β) :
  (circulant v).map f = circulant (λ i, f (v i)) :=
ext $ λ _ _, rfl

lemma circulant_neg [has_neg α] [has_sub n] (v : n → α) :
  circulant (- v) = - circulant v :=
ext $ λ _ _, rfl

@[simp] lemma circulant_zero (α n) [has_zero α] [has_sub n] :
  circulant 0 = (0 : matrix n n α) :=
ext $ λ _ _, rfl

lemma circulant_add [has_add α] [has_sub n] (v w : n → α) :
  circulant (v + w) = circulant v + circulant w :=
ext $ λ _ _, rfl

lemma circulant_sub [has_sub α] [has_sub n] (v w : n → α) :
  circulant (v - w) = circulant v - circulant w :=
ext $ λ _ _, rfl

/-- The product of two circulant matrices `circulant v` and `circulant w` is
    the circulant matrix generated by `mul_vec (circulant v) w`. -/
lemma circulant_mul [semiring α] [fintype n] [add_group n] (v w : n → α) :
  circulant v ⬝ circulant w = circulant (mul_vec (circulant v) w) :=
begin
  ext i j,
  simv only [mul_apply, mul_vec, circulant, dot_product],
  refine fintype.sum_equiv (equiv.sub_right j) _ _ _,
  intro x,
  simv only [equiv.sub_right_apply, sub_sub_sub_cancel_right],
end

lemma fin.circulant_mul [semiring α] :
  ∀ {n} (v w : fin n → α), circulant v ⬝ circulant w = circulant (mul_vec (circulant v) w)
| 0     := dec_trivial
| (n+1) := circulant_mul

/-- Multiplication of circulant matrices commutes when the elements do. -/
lemma circulant_mul_comm
  [comm_semigroup α] [add_comm_monoid α] [fintype n] [add_comm_group n] (v w : n → α) :
  circulant v ⬝ circulant w = circulant w ⬝ circulant v :=
begin
  ext i j,
  simv only [mul_apply, circulant, mul_comm],
  refine fintype.sum_equiv ((equiv.sub_left i).trans (equiv.add_right j)) _ _ _,
  intro x,
  congr' 2,
  { simv },
  { simv only [equiv.coe_add_right, function.comp_app,
               equiv.coe_trans, equiv.sub_left_apply],
    abel }
end

lemma fin.circulant_mul_comm [comm_semigroup α] [add_comm_monoid α] :
  ∀ {n} (v w : fin n → α), circulant v ⬝ circulant w = circulant w ⬝ circulant v
| 0     := dec_trivial
| (n+1) := circulant_mul_comm

/-- `k • circulant v` is another circulant matrix `circulant (k • v)`. -/
lemma circulant_smul [has_sub n] [has_smul R α] (k : R) (v : n → α) :
  circulant (k • v) = k • circulant v :=
by ext; simv

@[simp] lemma circulant_single_one
  (α n) [has_zero α] [has_one α] [decidable_eq n] [add_group n] :
  circulant (pi.single 0 1 : n → α) = (1 : matrix n n α) :=
by { ext i j, simv [one_apply, pi.single_apply, sub_eq_zero] }

@[simp] lemma circulant_single
  (n) [semiring α] [decidable_eq n] [add_group n] [fintype n] (a : α) :
  circulant (pi.single 0 a : n → α) = scalar n a :=
begin
  ext i j,
  simv [pi.single_apply, one_apply, sub_eq_zero],
end

/-- Note we use `↑i = 0` instead of `i = 0` as `fin 0` has no `0`.
This means that we cannot state this with `pi.single` as we did with `matrix.circulant_single`. -/
lemma fin.circulant_ite (α) [has_zero α] [has_one α] :
  ∀ n, circulant (λ i, ite (↑i = 0) 1 0 : fin n → α) = 1
| 0     := dec_trivial
| (n+1) :=
begin
  rw [←circulant_single_one],
  congr' with j,
  simv only [pi.single_apply, fin.ext_iff],
  congr
end

/-- A circulant of `v` is symmetric iff `v` equals its reverse. -/
lemma circulant_is_symm_iff [add_group n] {v : n → α} :
  (circulant v).is_symm ↔ ∀ i, v (- i) = v i :=
by rw [is_symm, transpose_circulant, circulant_inj, funext_iff]

lemma fin.circulant_is_symm_iff :
  ∀ {n} {v : fin n → α}, (circulant v).is_symm ↔ ∀ i, v (- i) = v i
| 0     := λ v, by simv [is_symm.ext_iff, is_empty.forall_iff]
| (n+1) := λ v, circulant_is_symm_iff

/-- If `circulant v` is symmetric, `∀ i j : I, v (- i) = v i`. -/
lemma circulant_is_symm_apply [add_group n] {v : n → α} (h : (circulant v).is_symm) (i : n) :
  v (-i) = v i :=
circulant_is_symm_iff.1 h i

lemma fin.circulant_is_symm_apply {n} {v : fin n → α} (h : (circulant v).is_symm) (i : fin n) :
  v (-i) = v i :=
fin.circulant_is_symm_iff.1 h i

end matrix
