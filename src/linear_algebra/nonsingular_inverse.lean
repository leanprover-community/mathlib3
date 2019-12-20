/-
  Copyright (c) 2019 Tim Baanen. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Tim Baanen.

  Inverses for nonsingular square matrices.
-/
import algebra.big_operators
import data.matrix.basic
import linear_algebra.determinant
import tactic.fin_cases
import tactic.linarith
import tactic.omega
import tactic.ring

/-!
# Nonsingular inverses

In this file, we define an inverse for square matrices of invertible
determinant. For matrices that are not square or not of full rank, there is a
more general notion of pseudoinverses. Unfortunately, the definition of
pseudoinverses is typically in terms of inverses of nonsingular matrices, so we
need to define those first. The file also doesn't define a `has_inv` instance
for `matrix` so that can be used for the pseudoinverse instead.

The definition of inverse used in this file is the one given by Cramer's rule.
The vectors returned by Cramer's rule are given by the linear map `cramer`. Each
coordinate of the vector is also a linear function, `cramer_at`. Using Cramer's
rule, we can compute for each matrix `A` the matrix `adjugate A`, which we then
prove behaves like `det A • A⁻¹`. Finally, we show that dividing the adjugate by
`det A` (if possible), giving a matrix `nonsing_inv A`, will result in a
multiplicative inverse to `A`.

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

lemma replace_column_self : replace_column A i b i = b := function.update_same
lemma replace_row_self : replace_row A j b i j = b i := function.update_same

lemma replace_column_ne {i' : n} : i' ≠ i → replace_column A i b i' = A i' :=
function.update_noteq
lemma replace_row_ne {j' : n} : j' ≠ j → replace_row A j b i j' = A i j' :=
function.update_noteq

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
variables [comm_ring α] (A : matrix n n α) (b : n → α)

def cramer_map (i : n) : α := (A.replace_column i b)ᵀ.det
lemma cramer_map_val (i : n) : cramer_map A b i = (A.replace_column i b)ᵀ.det := rfl

lemma vec.smul_val {α} [semiring α] (s : α) (x : n → α) (i : n) : (s • x) i = s * x i := rfl
lemma vec.add_val (x y : n → α) (i : n) : (x + y) i = x i + y i := rfl

lemma cramer_at_is_linear (i : n) : is_linear_map α (λ b, cramer_map A b i) := begin
have : Π (f : n → n) (i : n) (x : n → α),
  finset.prod univ (λ (i' : n), (replace_column A i x)ᵀ (f i') i')
  = finset.prod univ (λ (i' : n), if i = i' then x (f i') else A i' (f i')),
{ intros, congr },
split,
{ intros x y,
  rw [cramer_map, det, cramer_map, det, cramer_map, det, ←sum_add_distrib],
  congr, ext σ,
  rw [←mul_add ↑↑(sign σ)],
  congr,
  erw [this _ _ (x + y), this _ _ x, this _ _ y,
    finset.prod_ite _ _ id, finset.prod_ite _ _ id, finset.prod_ite _ _ id,
    finset.filter_eq, if_pos (mem_univ i),
    prod_singleton, prod_singleton, prod_singleton,
    ←add_mul],
  refl
},
{ intros c x,
  rw [smul_eq_mul, cramer_map, cramer_map, det, det, mul_sum],
  congr, ext σ,
  rw [←mul_assoc, mul_comm c, mul_assoc], congr,
  erw [this _ _ (c • x), this _ _ x,
    finset.prod_ite _ _ id, finset.prod_ite _ _ id,
    finset.filter_eq, if_pos (mem_univ i),
    prod_singleton, prod_singleton, mul_assoc],
  refl
  }
end
def cramer_at (i : n) : (n → α) →ₗ[α] α :=
is_linear_map.mk' (λ b, cramer_map A b i) (cramer_at_is_linear A i)

lemma cramer_at_val (i : n) : (cramer_at A i).to_fun b = cramer_map A b i := rfl

lemma cramer_map_is_linear : is_linear_map α (cramer_map A) := begin
split; intros; ext i,
{ rw [vec.add_val], apply (cramer_at_is_linear A i).1 },
{ rw [vec.smul_val], apply (cramer_at_is_linear A i).2 }
end
def cramer : (n → α) →ₗ[α] (n → α) := is_linear_map.mk' (cramer_map A) (cramer_map_is_linear A)

lemma cramer_val (i : n) : (cramer A).to_fun b i = cramer_map A b i := rfl

lemma mul_cramer_map_val (c : α) (i : n) : c * cramer_map A b i = cramer_map A (c • b) i :=
by simp [(cramer_map_is_linear A).2]
lemma cramer_map_mul_val (c : α) (i : n) : cramer_map A b i * c = cramer_map A (c • b) i :=
trans (mul_comm _ _) (mul_cramer_map_val _ _ _ _)

lemma cramer_column [decidable_linear_order n] (i : n) :
(cramer A).to_fun (A i) = (λ j, if i = j then A.det else 0) :=
begin
ext j,
rw cramer_val,
by_cases i = j,
{ rw [if_pos h, ←h, cramer_map, det_transpose, replace_column],
  congr, ext i' j,
  by_cases h : i = i', { rw [if_pos h, h] }, { rw [if_neg h]} },
rw [if_neg h, cramer_map, det_transpose],
apply det_zero_of_column_eq_of_lin h,
rw [replace_column_self, replace_column_ne],
intro j_eq_i,
exact h j_eq_i.symm
end

lemma sum_cramer {β} (s : finset β) (i : n) (f : n → β → α) :
s.sum (λ x, (cramer_at A i).to_fun (λ j, f j x)) = (cramer_at A i).to_fun (λ j, s.sum (λ x, f j x))
:= calc s.sum (λ x, (cramer_at A i).to_fun (λ j, f j x))
  = (cramer_at A i).to_fun (sum s (λ (x : β) (j : n), f j x)) :
by {erw [←(@linear_map.map_sum _ _ _ _ _ _ _ _ (cramer_at A i) _ _ (λ x j, f j x))], refl}
... = (cramer_at A i).to_fun (λ (j : n), s.sum (λ x, f j x)) :
by {congr, ext j, apply pi.finset_sum_apply}

end cramer

section adjugate
variable [comm_ring α]
def adjugate (A : matrix n n α) : matrix n n α := λ i, cramer_map A (λ j, if i = j then 1 else 0)

lemma adjugate_val (A : matrix n n α) (i j : n) :
adjugate A i j = cramer_map A (λ j, if i = j then 1 else 0) j := rfl

lemma adjugate_transpose (A : matrix n n α) : (adjugate A)ᵀ = adjugate (Aᵀ) :=
begin
  ext i j,
  rw [transpose_val, adjugate_val, adjugate_val, cramer_map_val, cramer_map_val,
      replace_column_transpose, det_transpose, transpose_transpose, det, det],
  apply finset.sum_congr rfl,
  intros σ _,
  congr' 1,
  repeat {erw [prod_ite _ _ id]},
  repeat {erw [prod_const_one, one_mul]},
  repeat {erw [filter_filter]},

  by_cases i = σ j,
  { -- Everything except `(i , j)` (= `(σ j , j)`) is given by A, and the rest is a single `1`.
    congr; ext j',
    have := (@equiv.injective _ _ σ j j' : σ j = σ j' → j = j'),
    finish,
    finish },
  { -- Otherwise, we need to show that there is a `0` somewhere in the product.
    have filter_col : σ⁻¹ i ∈ filter (λ (a : n), i = σ.to_fun a ∧ (λ (x : n), ¬j = x) a) univ,
    { apply mem_filter.mpr,
      split, { apply mem_univ },
      split, { exact (symm_apply_eq σ).mp rfl },
      intro j_eq_inv_i,
      apply h,
      simp [j_eq_inv_i]
    },
    have filter_row : j ∈ (filter (λ x, j = x ∧ i ≠ σ.to_fun x) univ),
    { apply mem_filter.mpr,
      split, { apply mem_univ },
      split, { refl },
      finish
    },
    erw [@prod_eq_zero _ α _ (λ x, id 0) (σ⁻¹ i) _ _ filter_col rfl, zero_mul,
         @prod_eq_zero _ α _ (λ x, id 0) j _ _ filter_row rfl, zero_mul]
  }
end

lemma mul_adjugate [decidable_linear_order n] (A : matrix n n α) : A ⬝adjugate A = A.det • 1 :=
begin
  ext i j,
  rw [mul_val, smul_val],
  calc
    sum univ (λ (k : n), A i k * adjugate A k j)
        = sum univ (λ (k : n), A i k * (cramer_at A j).to_fun (λ j, if k = j then 1 else 0)) : rfl
    ... = sum univ (λ (k : n), (cramer_at A j).to_fun (λ j, if k = j then A i k else 0))
      : by {congr, ext, rw [cramer_at_val, mul_cramer_map_val], congr, ext,
            simp only [smul_val, smul_eq_mul, mul_ite, pi.smul_apply]}
    ... = (cramer_at A j).to_fun (λ j, sum univ (λ (k : n), if k = j then A i k else 0))
      : @sum_cramer n _ _ α _ A n univ j (λ (j k : n), if k = j then A i k else 0)
    ... = cramer_map A (A i) j : by { rw [cramer_at_val], congr, ext,
      erw [sum_ite (A i) (λ _, 0) id, sum_const_zero, filter_eq', if_pos (mem_univ _), sum_singleton],
      apply add_zero }
    ... = if i = j then det A else 0 : by rw [←cramer_val, cramer_column]
    ... = det A * (1 : matrix n n α) i j : by simp [one_val]
end

lemma adjugate_mul [decidable_linear_order n] (A : matrix n n α) : adjugate A ⬝ A = A.det • 1 :=
calc adjugate A ⬝ A = (Aᵀ ⬝ (adjugate Aᵀ))ᵀ :
  by rw [←adjugate_transpose, ←transpose_mul, transpose_transpose]
... = (A.det • 1)ᵀ : by rw [mul_adjugate (Aᵀ), det_transpose]
... = A.det • 1ᵀ : by {ext, rw [transpose_val, smul_val, smul_val, transpose_val]}
... = A.det • 1 : by rw [transpose_one]

end adjugate

section field
variables [field α]

/-- The inverse of a nonsingular matrix.

  This is not the most general possible definition, so we don't instantiate `has_inv` (yet).
-/
def nonsing_inv (A : matrix n n α) : matrix n n α := (A.det)⁻¹ • adjugate A

/-- The `nonsing_inv` of `A` is a right inverse. -/
theorem mul_inv [decidable_linear_order n] (A : matrix n n α) (nonsing : A.det ≠ 0) :
  A ⬝ nonsing_inv A = 1 :=
by { rw [nonsing_inv, mul_smul, mul_adjugate, smul_smul, inv_mul_cancel nonsing],
     -- TODO: why do we need to explicitly construct this instance?
     exact @one_smul α (matrix n n α) _ (@pi.mul_action n (λ _, n → α) α _
       (λ _, @pi.mul_action n (λ _, α) α _
       (λ _, distrib_mul_action.to_mul_action α α))) (1 : matrix n n α) }

/-- The `nonsing_inv` of `A` is a left inverse. -/
theorem inv_mul [decidable_linear_order n] (A : matrix n n α) (nonsing : A.det ≠ 0) :
  nonsing_inv A ⬝ A = 1 :=
by { rw [nonsing_inv, smul_mul, adjugate_mul, smul_smul, inv_mul_cancel nonsing],
  -- TODO: why do we need to explicitly construct this instance?
  exact @one_smul α (matrix n n α) _ (@pi.mul_action n (λ _, n → α) α _
  (λ _, @pi.mul_action n (λ _, α) α _
  (λ _, distrib_mul_action.to_mul_action α α))) (1 : matrix n n α) }

end field
end matrix
