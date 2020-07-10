/-
Copyright (c) 2019 Tim Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Tim Baanen.
-/
import algebra.associated
import linear_algebra.determinant
import tactic.linarith
import tactic.ring_exp

/-!
# Nonsingular inverses

In this file, we define an inverse for square matrices of invertible
determinant. For matrices that are not square or not of full rank, there is a
more general notion of pseudoinverses. Unfortunately, the definition of
pseudoinverses is typically in terms of inverses of nonsingular matrices, so we
need to define those first. The file also doesn't define a `has_inv` instance
for `matrix` so that can be used for the pseudoinverse instead.

The definition of inverse used in this file is the adjugate divided by the determinant.
The adjugate is calculated with Cramer's rule, which we introduce first.
The vectors returned by Cramer's rule are given by the linear map `cramer`,
which sends a matrix `A` and vector `b` to the vector consisting of the
determinant of replacing the `i`th column of `A` with `b` at index `i`
(written as `(A.update_column i b).det`).
Using Cramer's rule, we can compute for each matrix `A` the matrix `adjugate A`.
The entries of the adjugate are the determinants of each minor of `A`.
Instead of defining a minor to be `A` with column `i` and row `j` deleted, we
replace the `i`th column of `A` with the `j`th basis vector; this has the same
determinant as the minor but more importantly equals Cramer's rule applied
to `A` and the `j`th basis vector, simplifying the subsequent proofs.
We prove the adjugate behaves like `det A • A⁻¹`. Finally, we show that dividing
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
open_locale matrix big_operators
open equiv equiv.perm finset


section update

/-- Update, i.e. replace the `i`th column of matrix `A` with the values in `b`. -/
def update_column (A : matrix n n α) (i : n) (b : n → α) : matrix n n α :=
function.update A i b

/-- Update, i.e. replace the `i`th row of matrix `A` with the values in `b`. -/
def update_row (A : matrix n n α) (j : n) (b : n → α) : matrix n n α :=
λ i, function.update (A i) j (b i)

variables {A : matrix n n α} {i j : n} {b : n → α}

@[simp] lemma update_column_self : update_column A i b i = b := function.update_same i b A

@[simp] lemma update_row_self : update_row A j b i j = b i := function.update_same j (b i) (A i)

@[simp] lemma update_column_ne {i' : n} (i_ne : i' ≠ i) : update_column A i b i' = A i' :=
function.update_noteq i_ne b A

@[simp] lemma update_row_ne {j' : n} (j_ne : j' ≠ j) : update_row A j b i j' = A i j' :=
function.update_noteq j_ne (b i) (A i)

lemma update_column_val {i' : n} : update_column A i b i' j = if i' = i then b j else A i' j :=
begin
  by_cases i' = i,
  { rw [h, update_column_self, if_pos rfl] },
  { rw [update_column_ne h, if_neg h] }
end

lemma update_row_val {j' : n} : update_row A j b i j' = if j' = j then b i else A i j' :=
begin
  by_cases j' = j,
  { rw [h, update_row_self, if_pos rfl] },
  { rw [update_row_ne h, if_neg h] }
end

lemma update_column_transpose : update_column Aᵀ i b = (update_row A i b)ᵀ :=
begin
  ext i' j,
  rw [transpose_val, update_column_val, update_row_val],
  refl
end
end update

section cramer
/-!
  ### `cramer` section

  Introduce the linear map `cramer` with values defined by `cramer_map`.
  After defining `cramer_map` and showing it is linear,
  we will restrict our proofs to using `cramer`.
-/
variables [comm_ring α] (A : matrix n n α) (b : n → α)

/--
  `cramer_map A b i` is the determinant of the matrix `A` with column `i` replaced with `b`,
  and thus `cramer_map A b` is the vector output by Cramer's rule on `A` and `b`.

  If `A ⬝ x = b` has a unique solution in `x`, `cramer_map` sends a square matrix `A`
  and vector `b` to the vector `x` such that `A ⬝ x = b`.
  Otherwise, the outcome of `cramer_map` is well-defined but not necessarily useful.
-/
def cramer_map (i : n) : α := (A.update_column i b).det

lemma cramer_map_is_linear (i : n) : is_linear_map α (λ b, cramer_map A b i) :=
begin
  have : Π {f : n → n} {i : n} (x : n → α),
    (∏ i' : n, (update_column A i x)ᵀ (f i') i')
    = (∏ i' : n, if i' = i then x (f i') else A i' (f i')),
  { intros, congr, ext i', rw [transpose_val, update_column_val] },
  split,
  { intros x y,
    repeat { rw [cramer_map, ←det_transpose, det] },
    rw [←sum_add_distrib],
    congr, ext σ,
    rw [←mul_add ↑↑(sign σ)],
    congr,
    repeat { erw [this, finset.prod_ite] },
    erw [finset.filter_eq', if_pos (mem_univ i), prod_singleton, prod_singleton,
      prod_singleton, ←add_mul],
    refl },
  { intros c x,
    repeat { rw [cramer_map, ←det_transpose, det] },
    rw [smul_eq_mul, mul_sum],
    congr, ext σ,
    rw [←mul_assoc, mul_comm c, mul_assoc], congr,
    repeat { erw [this, finset.prod_ite] },
    erw [finset.filter_eq', if_pos (mem_univ i),
      prod_singleton, prod_singleton, mul_assoc], }
end

lemma cramer_is_linear : is_linear_map α (cramer_map A) :=
begin
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

lemma cramer_apply (i : n) : cramer α A b i = (A.update_column i b).det := rfl

/-- Applying Cramer's rule to a column of the matrix gives a scaled basis vector. -/
lemma cramer_column_self (i : n) :
cramer α A (A i) = (λ j, if i = j then A.det else 0) :=
begin
  ext j,
  rw cramer_apply,
  by_cases i = j,
  { -- i = j: this entry should be `A.det`
    rw [if_pos h, ←h],
    congr, ext i',
    by_cases h : i' = i, { rw [h, update_column_self] }, { rw [update_column_ne h]} },
  { -- i ≠ j: this entry should be 0
    rw [if_neg h],
    apply det_zero_of_column_eq h,
    rw [update_column_self, update_column_ne],
    apply h }
end

/-- Use linearity of `cramer` to take it out of a summation. -/
lemma sum_cramer {β} (s : finset β) (f : β → n → α) :
  ∑ x in s, cramer α A (f x) = cramer α A (∑ x in s, f x) :=
(linear_map.map_sum (cramer α A)).symm

/-- Use linearity of `cramer` and vector evaluation to take `cramer A _ i` out of a summation. -/
lemma sum_cramer_apply {β} (s : finset β) (f : n → β → α) (i : n) :
∑ x in s, cramer α A (λ j, f j x) i = cramer α A (λ (j : n), ∑ x in s, f j x) i :=
calc ∑ x in s, cramer α A (λ j, f j x) i
    = (∑ x in s, cramer α A (λ j, f j x)) i : (pi.finset_sum_apply i s _).symm
... = cramer α A (λ (j : n), ∑ x in s, f j x) i :
  by { rw [sum_cramer, cramer_apply], congr, ext j, apply pi.finset_sum_apply }

end cramer

section adjugate
/-!
### `adjugate` section

Define the `adjugate` matrix and a few equations.
These will hold for any matrix over a commutative ring,
while the `inv` section is specifically for invertible matrices.
-/

variable [comm_ring α]
/-- The adjugate matrix is the transpose of the cofactor matrix.

  Typically, the cofactor matrix is defined by taking the determinant of minors,
  i.e. the matrix with a row and column removed.
  However, the proof of `mul_adjugate` becomes a lot easier if we define the
  minor as replacing a column with a basis vector, since it allows us to use
  facts about the `cramer` map.
-/
def adjugate (A : matrix n n α) : matrix n n α := λ i, cramer α A (λ j, if i = j then 1 else 0)

lemma adjugate_def (A : matrix n n α) :
  adjugate A = λ i, cramer α A (λ j, if i = j then 1 else 0) := rfl

lemma adjugate_val (A : matrix n n α) (i j : n) :
  adjugate A i j = (A.update_column j (λ j, if i = j then 1 else 0)).det := rfl

lemma adjugate_transpose (A : matrix n n α) : (adjugate A)ᵀ = adjugate (Aᵀ) :=
begin
  ext i j,
  rw [transpose_val, adjugate_val, adjugate_val, update_column_transpose, det_transpose],
  apply finset.sum_congr rfl,
  intros σ _,
  congr' 1,

  by_cases i = σ j,
  { -- Everything except `(i , j)` (= `(σ j , j)`) is given by A, and the rest is a single `1`.
    congr; ext j',
    have := (@equiv.injective _ _ σ j j' : σ j = σ j' → j = j'),
    rw [update_column_val, update_row_val],
    finish },
  { -- Otherwise, we need to show that there is a `0` somewhere in the product.
    have : (∏ j' : n, update_row A j (λ (i' : n), ite (i = i') 1 0) (σ j') j') = 0,
    { apply prod_eq_zero (mem_univ j),
      rw [update_row_self],
      exact if_neg h },
    rw this,
    apply prod_eq_zero (mem_univ (σ⁻¹ i)),
    erw [apply_symm_apply σ i, update_column_self],
    apply if_neg,
    intro h',
    exact h ((symm_apply_eq σ).mp h'.symm) }
end

lemma mul_adjugate_val (A : matrix n n α) (i j k) :
  A i k * adjugate A k j = cramer α A (λ j, if k = j then A i k else 0) j :=
begin
  erw [←smul_eq_mul, ←pi.smul_apply, ←linear_map.map_smul],
  congr, ext,
  rw [pi.smul_apply, smul_eq_mul, mul_boole],
end

lemma mul_adjugate (A : matrix n n α) : A ⬝ adjugate A = A.det • 1 :=
begin
  ext i j,
  rw [mul_val, smul_val, one_val, mul_boole],
  calc
    ∑ k : n, A i k * adjugate A k j
        = ∑ k : n, cramer α A (λ j, if k = j then A i k else 0) j
      : by {congr, ext k, apply mul_adjugate_val A i j k}
    ... = cramer α A (λ j, ∑ k : n, if k = j then A i k else 0) j
      : sum_cramer_apply A univ (λ (j k : n), if k = j then A i k else 0) j
    ... = cramer α A (A i) j : by { rw [cramer_apply], congr, ext,
      rw [sum_ite_eq' univ x (A i), if_pos (mem_univ _)] }
    ... = if i = j then det A else 0 : by rw [cramer_column_self]
end

lemma adjugate_mul (A : matrix n n α) : adjugate A ⬝ A = A.det • 1 :=
calc adjugate A ⬝ A = (Aᵀ ⬝ (adjugate Aᵀ))ᵀ :
  by rw [←adjugate_transpose, ←transpose_mul, transpose_transpose]
... = A.det • 1 : by rw [mul_adjugate (Aᵀ), det_transpose, transpose_smul, transpose_one]

/-- `det_adjugate_of_cancel` is an auxiliary lemma for computing `(adjugate A).det`,
  used in `det_adjugate_eq_one` and `det_adjugate_of_is_unit`.

  The formula for the determinant of the adjugate of an `n` by `n` matrix `A`
  is in general `(adjugate A).det = A.det ^ (n - 1)`, but the proof differs in several cases.
  This lemma `det_adjugate_of_cancel` covers the case that `det A` cancels
  on the left of the equation `A.det * b = A.det ^ n`.
-/
lemma det_adjugate_of_cancel {A : matrix n n α}
  (h : ∀ b, A.det * b = A.det ^ fintype.card n → b = A.det ^ (fintype.card n - 1)) :
  (adjugate A).det = A.det ^ (fintype.card n - 1) :=
h (adjugate A).det (calc A.det * (adjugate A).det = (A ⬝ adjugate A).det   : (det_mul _ _).symm
                                              ... = A.det ^ fintype.card n : by simp [mul_adjugate])

lemma adjugate_eq_one_of_card_eq_one {A : matrix n n α} (h : fintype.card n = 1) : adjugate A = 1 :=
begin
  ext i j,
  have univ_eq_i := univ_eq_singleton_of_card_one i h,
  have univ_eq_j := univ_eq_singleton_of_card_one j h,
  have i_eq_j : i = j := singleton_inj.mp (by rw [←univ_eq_i, univ_eq_j]),
  have perm_eq : (univ : finset (perm n)) = {1} :=
    univ_eq_singleton_of_card_one (1 : perm n) (by simp [card_univ, fintype.card_perm, h]),
  simp [adjugate_val, det, univ_eq_i, perm_eq, i_eq_j]
end

@[simp] lemma adjugate_zero (h : 1 < fintype.card n) : adjugate (0 : matrix n n α) = 0 :=
begin
  ext i j,
  obtain ⟨j', hj'⟩ : ∃ j', j' ≠ j := fintype.exists_ne_of_one_lt_card h j,
  apply det_eq_zero_of_column_eq_zero j',
  intro j'',
  simp [update_column_ne hj']
end

lemma det_adjugate_eq_one {A : matrix n n α} (h : A.det = 1) : (adjugate A).det = 1 :=
calc (adjugate A).det
    = A.det ^ (fintype.card n - 1) : det_adjugate_of_cancel (λ b hb, by simpa [h] using hb)
... = 1                            : by rw [h, one_pow]

/-- `det_adjugate_of_is_unit` gives the formula for `(adjugate A).det` if `A.det` has an inverse.

  The formula for the determinant of the adjugate of an `n` by `n` matrix `A`
  is in general `(adjugate A).det = A.det ^ (n - 1)`, but the proof differs in several cases.
  This lemma `det_adjugate_of_is_unit` covers the case that `det A` has an inverse.
-/
lemma det_adjugate_of_is_unit {A : matrix n n α} (h : is_unit A.det) :
  (adjugate A).det = A.det ^ (fintype.card n - 1) :=
begin
  rcases is_unit_iff_exists_inv'.mp h with ⟨a, ha⟩,
  by_cases card_lt_zero : fintype.card n ≤ 0,
  { have h : fintype.card n = 0 := by linarith,
    simp [det_eq_one_of_card_eq_zero h] },
  have zero_lt_card : 0 < fintype.card n := by linarith,
  have n_nonempty : nonempty n := fintype.card_pos_iff.mp zero_lt_card,

  by_cases card_lt_one : fintype.card n ≤ 1,
  { have h : fintype.card n = 1 := by linarith,
    simp [h, adjugate_eq_one_of_card_eq_one h] },
  have one_lt_card : 1 < fintype.card n := by linarith,
  have zero_lt_card_sub_one : 0 < fintype.card n - 1 :=
    (nat.sub_lt_sub_right_iff (refl 1)).mpr one_lt_card,

  apply det_adjugate_of_cancel,
  intros b hb,
  calc b = a * (det A ^ (fintype.card n - 1 + 1)) :
       by rw [←one_mul b, ←ha, mul_assoc, hb, nat.sub_add_cancel zero_lt_card]
     ... = a * det A * det A ^ (fintype.card n - 1) : by ring_exp
     ... = det A ^ (fintype.card n - 1) : by rw [ha, one_mul]
end

end adjugate

section inv
/-!
### `inv` section

Defines the matrix `nonsing_inv A` and proves it is the inverse matrix
of a square matrix `A` as long as `det A` has a multiplicative inverse.
-/

variables [comm_ring α]
variables (A : matrix n n α)

open_locale classical

lemma is_unit_det_transpose (h : is_unit A.det) : is_unit Aᵀ.det :=
by { rw det_transpose, exact h, }

/-- The inverse of a square matrix, when it is invertible (and zero otherwise).-/
noncomputable def nonsing_inv : matrix n n α :=
if h : is_unit A.det then (↑h.unit⁻¹ : α) • A.adjugate else 0

noncomputable instance : has_inv (matrix n n α) := ⟨matrix.nonsing_inv⟩

lemma nonsing_inv_apply (h : is_unit A.det) :
  A⁻¹ = (↑h.unit⁻¹ : α) • A.adjugate :=
by { change A.nonsing_inv = _, dunfold nonsing_inv, simp only [dif_pos, h], }

lemma transpose_nonsing_inv (h : is_unit A.det) :
  (A⁻¹)ᵀ = (Aᵀ)⁻¹ :=
begin
  have h' := A.is_unit_det_transpose h,
  have dets_eq : (↑h.unit : α) = ↑h'.unit := by rw [h.unit_spec, h'.unit_spec, det_transpose],
  rw [A.nonsing_inv_apply h, Aᵀ.nonsing_inv_apply h',
      units.inv_unique dets_eq, A.adjugate_transpose.symm],
  refl,
end

/-- The `nonsing_inv` of `A` is a right inverse. -/
@[simp] lemma mul_nonsing_inv (h : is_unit A.det) : A ⬝ A⁻¹ = 1 :=
by rw [A.nonsing_inv_apply h, mul_smul, mul_adjugate, smul_smul, units.inv_mul_of_eq h.unit_spec,
       one_smul]

/-- The `nonsing_inv` of `A` is a left inverse. -/
@[simp] lemma nonsing_inv_mul (h : is_unit A.det) : A⁻¹ ⬝ A = 1 :=
calc A⁻¹ ⬝ A = (Aᵀ ⬝ (Aᵀ)⁻¹)ᵀ : by { rw [transpose_mul,
                                    Aᵀ.transpose_nonsing_inv (A.is_unit_det_transpose h),
                                    transpose_transpose], }
         ... = 1ᵀ             : by { rw Aᵀ.mul_nonsing_inv, exact A.is_unit_det_transpose h, }
         ... = 1              : transpose_one

@[simp] lemma nonsing_inv_det (h : is_unit A.det) : A⁻¹.det * A.det = 1 :=
by rw [←det_mul, A.nonsing_inv_mul h, det_one]

lemma is_unit_nonsing_inv_det (h : is_unit A.det) : is_unit A⁻¹.det :=
is_unit_of_mul_eq_one _ _ (A.nonsing_inv_det h)

@[simp] lemma nonsing_inv_nonsing_inv (h : is_unit A.det) : (A⁻¹)⁻¹ = A :=
calc (A⁻¹)⁻¹ = 1 ⬝ (A⁻¹)⁻¹        : by rw matrix.one_mul
         ... = A ⬝ A⁻¹ ⬝ (A⁻¹)⁻¹  : by rw A.mul_nonsing_inv h
         ... = A                  : by { rw [matrix.mul_assoc,
                                         (A⁻¹).mul_nonsing_inv (A.is_unit_nonsing_inv_det h),
                                         matrix.mul_one], }

/-- A matrix whose determinant is a unit is itself a unit. -/
noncomputable def nonsing_inv_unit (h : is_unit A.det) : units (matrix n n α) :=
{ val     := A,
  inv     := A⁻¹,
  val_inv := by { rw matrix.mul_eq_mul, apply A.mul_nonsing_inv h, },
  inv_val := by { rw matrix.mul_eq_mul, apply A.nonsing_inv_mul h, } }

lemma is_unit_iff_is_unit_det : is_unit A ↔ is_unit A.det :=
begin
  split; intros h,
  { -- is_unit A → is_unit A.det
    suffices : ∃ (B : matrix n n α), A ⬝ B = 1,
    { rcases this with ⟨B, hB⟩, apply is_unit_of_mul_eq_one _ B.det, rw [←det_mul, hB, det_one], },
    refine ⟨↑h.unit⁻¹, _⟩, conv_lhs { congr, rw ←h.unit_spec, }, exact h.unit.mul_inv, },
  { -- is_unit A.det → is_unit A
    exact is_unit_unit (A.nonsing_inv_unit h), },
end

end inv
end matrix
