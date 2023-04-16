/-
Copyright (c) 2019 Tim Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baanen, Lu-Ming Zhang
-/
import linear_algebra.matrix.adjugate

/-!
# Nonsingular inverses

In this file, we define an inverse for square matrices of invertible determinant.

For matrices that are not square or not of full rank, there is a more general notion of
pseudoinverses which we do not consider here.

The definition of inverse used in this file is the adjugate divided by the determinant.
We show that dividing the adjugate by `det A` (if possible), giving a matrix `A⁻¹` (`nonsing_inv`),
will result in a multiplicative inverse to `A`.

Note that there are at least three different inverses in mathlib:

* `A⁻¹` (`has_inv.inv`): alone, this satisfies no properties, although it is usually used in
  conjunction with `group` or `group_with_zero`. On matrices, this is defined to be zero when no
  inverse exists.
* `⅟A` (`inv_of`): this is only available in the presence of `[invertible A]`, which guarantees an
  inverse exists.
* `ring.inverse A`: this is defined on any `monoid_with_zero`, and just like `⁻¹` on matrices, is
  defined to be zero when no inverse exists.

We start by working with `invertible`, and show the main results:

* `matrix.invertible_of_det_invertible`
* `matrix.det_invertible_of_invertible`
* `matrix.is_unit_iff_is_unit_det`
* `matrix.mul_eq_one_comm`

After this we define `matrix.has_inv` and show it matches `⅟A` and `ring.inverse A`.
The rest of the results in the file are then about `A⁻¹`

## References

  * https://en.wikipedia.org/wiki/Cramer's_rule#Finding_inverse_matrix

## Tags

matrix inverse, cramer, cramer's rule, adjugate
-/

namespace matrix
universes u u' v
variables {m : Type u} {n : Type u'} {α : Type v}
open_locale matrix big_operators
open equiv equiv.perm finset

/-! ### Matrices are `invertible` iff their determinants are -/

section invertible
variables [fintype n] [decidable_eq n] [comm_ring α]

/-- A copy of `inv_of_mul_self` using `⬝` not `*`. -/
protected lemma inv_of_mul_self (A : matrix n n α) [invertible A] : ⅟A ⬝ A = 1 := inv_of_mul_self A

/-- A copy of `mul_inv_of_self` using `⬝` not `*`. -/
protected lemma mul_inv_of_self (A : matrix n n α) [invertible A] : A ⬝ ⅟A = 1 := mul_inv_of_self A

/-- A copy of `inv_of_mul_self_assoc` using `⬝` not `*`. -/
protected lemma inv_of_mul_self_assoc (A : matrix n n α) (B : matrix n m α) [invertible A] :
  ⅟A ⬝ (A ⬝ B) = B :=
by rw [←matrix.mul_assoc, matrix.inv_of_mul_self, matrix.one_mul]

/-- A copy of `mul_inv_of_self_assoc` using `⬝` not `*`. -/
protected lemma mul_inv_of_self_assoc (A : matrix n n α) (B : matrix n m α) [invertible A] :
  A ⬝ (⅟A ⬝ B) = B :=
by rw [←matrix.mul_assoc, matrix.mul_inv_of_self, matrix.one_mul]

/-- A copy of `mul_inv_of_mul_self_cancel` using `⬝` not `*`. -/
protected lemma mul_inv_of_mul_self_cancel (A : matrix m n α) (B : matrix n n α)
  [invertible B] : A ⬝ ⅟B ⬝ B = A :=
by rw [matrix.mul_assoc, matrix.inv_of_mul_self, matrix.mul_one]

/-- A copy of `mul_mul_inv_of_self_cancel` using `⬝` not `*`. -/
protected lemma mul_mul_inv_of_self_cancel (A : matrix m n α) (B : matrix n n α)
  [invertible B] : A ⬝ B ⬝ ⅟B = A :=
by rw [matrix.mul_assoc, matrix.mul_inv_of_self, matrix.mul_one]

variables (A : matrix n n α) (B : matrix n n α)

/-- If `A.det` has a constructive inverse, produce one for `A`. -/
def invertible_of_det_invertible [invertible A.det] : invertible A :=
{ inv_of := ⅟A.det • A.adjugate,
  mul_inv_of_self :=
    by rw [mul_smul_comm, matrix.mul_eq_mul, mul_adjugate, smul_smul, inv_of_mul_self, one_smul],
  inv_of_mul_self :=
    by rw [smul_mul_assoc, matrix.mul_eq_mul, adjugate_mul, smul_smul, inv_of_mul_self, one_smul] }

lemma inv_of_eq [invertible A.det] [invertible A] : ⅟A = ⅟A.det • A.adjugate :=
by { letI := invertible_of_det_invertible A, convert (rfl : ⅟A = _) }

/-- `A.det` is invertible if `A` has a left inverse. -/
def det_invertible_of_left_inverse (h : B ⬝ A = 1) : invertible A.det :=
{ inv_of := B.det,
  mul_inv_of_self := by rw [mul_comm, ← det_mul, h, det_one],
  inv_of_mul_self := by rw [← det_mul, h, det_one] }

/-- `A.det` is invertible if `A` has a right inverse. -/
def det_invertible_of_right_inverse (h : A ⬝ B = 1) : invertible A.det :=
{ inv_of := B.det,
  mul_inv_of_self := by rw [← det_mul, h, det_one],
  inv_of_mul_self := by rw [mul_comm, ← det_mul, h, det_one] }

/-- If `A` has a constructive inverse, produce one for `A.det`. -/
def det_invertible_of_invertible [invertible A] : invertible A.det :=
det_invertible_of_left_inverse A (⅟A) (inv_of_mul_self _)

lemma det_inv_of [invertible A] [invertible A.det] : (⅟A).det = ⅟A.det :=
by { letI := det_invertible_of_invertible A, convert (rfl : _ = ⅟A.det) }

/-- Together `matrix.det_invertible_of_invertible` and `matrix.invertible_of_det_invertible` form an
equivalence, although both sides of the equiv are subsingleton anyway. -/
@[simps]
def invertible_equiv_det_invertible : invertible A ≃ invertible A.det :=
{ to_fun := @det_invertible_of_invertible _ _ _ _ _ A,
  inv_fun := @invertible_of_det_invertible _ _ _ _ _ A,
  left_inv := λ _, subsingleton.elim _ _,
  right_inv := λ _, subsingleton.elim _ _ }

variables {A B}

lemma mul_eq_one_comm : A ⬝ B = 1 ↔ B ⬝ A = 1 :=
suffices ∀ A B, A ⬝ B = 1 → B ⬝ A = 1, from ⟨this A B, this B A⟩, assume A B h,
begin
  letI : invertible B.det := det_invertible_of_left_inverse _ _ h,
  letI : invertible B := invertible_of_det_invertible B,
  calc B ⬝ A = (B ⬝ A) ⬝ (B ⬝ ⅟B) : by rw [matrix.mul_inv_of_self, matrix.mul_one]
        ... = B ⬝ ((A ⬝ B) ⬝ ⅟B) : by simp only [matrix.mul_assoc]
        ... = B ⬝ ⅟B : by rw [h, matrix.one_mul]
        ... = 1 : matrix.mul_inv_of_self B,
end

variables (A B)

/-- We can construct an instance of invertible A if A has a left inverse. -/
def invertible_of_left_inverse (h : B ⬝ A = 1) : invertible A :=
⟨B, h, mul_eq_one_comm.mp h⟩

/-- We can construct an instance of invertible A if A has a right inverse. -/
def invertible_of_right_inverse (h : A ⬝ B = 1) : invertible A :=
⟨B, mul_eq_one_comm.mp h, h⟩

/-- The transpose of an invertible matrix is invertible. -/
instance invertible_transpose [invertible A] : invertible Aᵀ :=
begin
  haveI : invertible Aᵀ.det,
    by simpa using det_invertible_of_invertible A,
  exact invertible_of_det_invertible Aᵀ
end

/-- A matrix is invertible if the transpose is invertible. -/
def invertible__of_invertible_transpose [invertible Aᵀ] : invertible A :=
begin
  rw ←transpose_transpose A,
  apply_instance
end

/-- A matrix is invertible if the conjugate transpose is invertible. -/
def invertible_of_invertible_conj_transpose [star_ring α] [invertible Aᴴ] :
  invertible A :=
begin
  rw ←conj_transpose_conj_transpose A,
  apply_instance
end

/-- Given a proof that `A.det` has a constructive inverse, lift `A` to `(matrix n n α)ˣ`-/
def unit_of_det_invertible [invertible A.det] : (matrix n n α)ˣ :=
@unit_of_invertible _ _ A (invertible_of_det_invertible A)

/-- When lowered to a prop, `matrix.invertible_equiv_det_invertible` forms an `iff`. -/
lemma is_unit_iff_is_unit_det : is_unit A ↔ is_unit A.det :=
by simp only [← nonempty_invertible_iff_is_unit, (invertible_equiv_det_invertible A).nonempty_congr]

/-! #### Variants of the statements above with `is_unit`-/

lemma is_unit_det_of_invertible [invertible A] : is_unit A.det :=
@is_unit_of_invertible _ _ _ (det_invertible_of_invertible A)

variables {A B}

lemma is_unit_of_left_inverse (h : B ⬝ A = 1) : is_unit A :=
⟨⟨A, B, mul_eq_one_comm.mp h, h⟩, rfl⟩

lemma is_unit_of_right_inverse (h : A ⬝ B = 1) : is_unit A :=
⟨⟨A, B, h, mul_eq_one_comm.mp h⟩, rfl⟩

lemma is_unit_det_of_left_inverse (h : B ⬝ A = 1) : is_unit A.det :=
@is_unit_of_invertible _ _ _ (det_invertible_of_left_inverse _ _ h)

lemma is_unit_det_of_right_inverse (h : A ⬝ B = 1) : is_unit A.det :=
@is_unit_of_invertible _ _ _ (det_invertible_of_right_inverse _ _ h)

lemma det_ne_zero_of_left_inverse [nontrivial α] (h : B ⬝ A = 1) : A.det ≠ 0 :=
(is_unit_det_of_left_inverse h).ne_zero

lemma det_ne_zero_of_right_inverse [nontrivial α] (h : A ⬝ B = 1) : A.det ≠ 0 :=
(is_unit_det_of_right_inverse h).ne_zero

end invertible

variables [fintype n] [decidable_eq n] [comm_ring α]
variables (A : matrix n n α) (B : matrix n n α)

lemma is_unit_det_transpose (h : is_unit A.det) : is_unit Aᵀ.det :=
by { rw det_transpose, exact h, }

/-! ### A noncomputable `has_inv` instance  -/

/-- The inverse of a square matrix, when it is invertible (and zero otherwise).-/
noncomputable instance : has_inv (matrix n n α) := ⟨λ A, ring.inverse A.det • A.adjugate⟩

lemma inv_def (A : matrix n n α) : A⁻¹ = ring.inverse A.det • A.adjugate := rfl

lemma nonsing_inv_apply_not_is_unit (h : ¬ is_unit A.det) :
  A⁻¹ = 0 :=
by rw [inv_def, ring.inverse_non_unit _ h, zero_smul]

lemma nonsing_inv_apply (h : is_unit A.det) :
  A⁻¹ = (↑h.unit⁻¹ : α) • A.adjugate :=
by rw [inv_def, ←ring.inverse_unit h.unit, is_unit.unit_spec]

/-- The nonsingular inverse is the same as `inv_of` when `A` is invertible. -/
@[simp] lemma inv_of_eq_nonsing_inv [invertible A] : ⅟A = A⁻¹ :=
begin
  letI := det_invertible_of_invertible A,
  rw [inv_def, ring.inverse_invertible, inv_of_eq],
end

/-- Coercing the result of `units.has_inv` is the same as coercing first and applying the
nonsingular inverse. -/
@[simp, norm_cast] lemma coe_units_inv (A : (matrix n n α)ˣ) :
  ↑(A⁻¹) = (A⁻¹ : matrix n n α) :=
begin
  letI := A.invertible,
  rw [←inv_of_eq_nonsing_inv, inv_of_units],
end

/-- The nonsingular inverse is the same as the general `ring.inverse`. -/
lemma nonsing_inv_eq_ring_inverse : A⁻¹ = ring.inverse A :=
begin
  by_cases h_det : is_unit A.det,
  { casesI (A.is_unit_iff_is_unit_det.mpr h_det).nonempty_invertible,
    rw [←inv_of_eq_nonsing_inv, ring.inverse_invertible], },
  { have h := mt A.is_unit_iff_is_unit_det.mp h_det,
    rw [ring.inverse_non_unit _ h, nonsing_inv_apply_not_is_unit A h_det], },
end

lemma transpose_nonsing_inv : (A⁻¹)ᵀ = (Aᵀ)⁻¹ :=
by rw [inv_def, inv_def, transpose_smul, det_transpose, adjugate_transpose]

lemma conj_transpose_nonsing_inv [star_ring α] : (A⁻¹)ᴴ = (Aᴴ)⁻¹ :=
by rw [inv_def, inv_def, conj_transpose_smul, det_conj_transpose, adjugate_conj_transpose,
       ring.inverse_star]

/-- The `nonsing_inv` of `A` is a right inverse. -/
@[simp] lemma mul_nonsing_inv (h : is_unit A.det) : A ⬝ A⁻¹ = 1 :=
begin
  casesI (A.is_unit_iff_is_unit_det.mpr h).nonempty_invertible,
  rw [←inv_of_eq_nonsing_inv, matrix.mul_inv_of_self],
end

/-- The `nonsing_inv` of `A` is a left inverse. -/
@[simp] lemma nonsing_inv_mul (h : is_unit A.det) : A⁻¹ ⬝ A = 1 :=
begin
  casesI (A.is_unit_iff_is_unit_det.mpr h).nonempty_invertible,
  rw [←inv_of_eq_nonsing_inv, matrix.inv_of_mul_self],
end

instance [invertible A] : invertible A⁻¹ :=
by { rw ← inv_of_eq_nonsing_inv, apply_instance }

@[simp] lemma inv_inv_of_invertible [invertible A] : A⁻¹⁻¹ = A :=
by simp only [← inv_of_eq_nonsing_inv, inv_of_inv_of]

@[simp] lemma mul_nonsing_inv_cancel_right (B : matrix m n α) (h : is_unit A.det) :
  B ⬝ A ⬝ A⁻¹ = B :=
by simp [matrix.mul_assoc, mul_nonsing_inv A h]

@[simp] lemma mul_nonsing_inv_cancel_left (B : matrix n m α) (h : is_unit A.det) :
  A ⬝ (A⁻¹ ⬝ B) = B :=
by simp [←matrix.mul_assoc, mul_nonsing_inv A h]

@[simp] lemma nonsing_inv_mul_cancel_right (B : matrix m n α) (h : is_unit A.det) :
  B ⬝ A⁻¹ ⬝ A = B :=
by simp [matrix.mul_assoc, nonsing_inv_mul A h]

@[simp] lemma nonsing_inv_mul_cancel_left (B : matrix n m α) (h : is_unit A.det) :
  A⁻¹ ⬝ (A ⬝ B) = B :=
by simp [←matrix.mul_assoc, nonsing_inv_mul A h]

@[simp] lemma mul_inv_of_invertible [invertible A] : A ⬝ A⁻¹ = 1 :=
mul_nonsing_inv A (is_unit_det_of_invertible A)

@[simp] lemma inv_mul_of_invertible [invertible A] : A⁻¹ ⬝ A = 1 :=
nonsing_inv_mul A (is_unit_det_of_invertible A)

@[simp] lemma mul_inv_cancel_right_of_invertible (B : matrix m n α) [invertible A] :
  B ⬝ A ⬝ A⁻¹ = B :=
mul_nonsing_inv_cancel_right A B (is_unit_det_of_invertible A)

@[simp] lemma mul_inv_cancel_left_of_invertible (B : matrix n m α) [invertible A] :
  A ⬝ (A⁻¹ ⬝ B) = B :=
mul_nonsing_inv_cancel_left A B (is_unit_det_of_invertible A)

@[simp] lemma inv_mul_cancel_right_of_invertible (B : matrix m n α) [invertible A] :
  B ⬝ A⁻¹ ⬝ A = B :=
nonsing_inv_mul_cancel_right A B (is_unit_det_of_invertible A)

@[simp] lemma inv_mul_cancel_left_of_invertible (B : matrix n m α) [invertible A] :
  A⁻¹ ⬝ (A ⬝ B) = B :=
nonsing_inv_mul_cancel_left A B (is_unit_det_of_invertible A)

lemma inv_mul_eq_iff_eq_mul_of_invertible (A B C : matrix n n α) [invertible A] :
  A⁻¹ ⬝ B = C ↔ B = A ⬝ C :=
⟨λ h, by rw [←h, mul_inv_cancel_left_of_invertible],
 λ h, by rw [h, inv_mul_cancel_left_of_invertible]⟩

lemma mul_inv_eq_iff_eq_mul_of_invertible (A B C : matrix n n α) [invertible A] :
  B ⬝ A⁻¹ = C ↔ B = C ⬝ A :=
⟨λ h, by rw [←h, inv_mul_cancel_right_of_invertible],
 λ h, by rw [h, mul_inv_cancel_right_of_invertible]⟩

lemma nonsing_inv_cancel_or_zero :
  (A⁻¹ ⬝ A = 1 ∧ A ⬝ A⁻¹ = 1) ∨ A⁻¹ = 0 :=
begin
  by_cases h : is_unit A.det,
  { exact or.inl ⟨nonsing_inv_mul _ h, mul_nonsing_inv _ h⟩ },
  { exact or.inr (nonsing_inv_apply_not_is_unit _ h) }
end

lemma det_nonsing_inv_mul_det (h : is_unit A.det) : A⁻¹.det * A.det = 1 :=
by rw [←det_mul, A.nonsing_inv_mul h, det_one]

@[simp] lemma det_nonsing_inv : A⁻¹.det = ring.inverse A.det :=
begin
  by_cases h : is_unit A.det,
  { casesI h.nonempty_invertible, letI := invertible_of_det_invertible A,
    rw [ring.inverse_invertible, ←inv_of_eq_nonsing_inv, det_inv_of] },
  casesI is_empty_or_nonempty n,
  { rw [det_is_empty, det_is_empty, ring.inverse_one] },
  { rw [ring.inverse_non_unit _ h, nonsing_inv_apply_not_is_unit _ h, det_zero ‹_›] },
end

lemma is_unit_nonsing_inv_det (h : is_unit A.det) : is_unit A⁻¹.det :=
is_unit_of_mul_eq_one _ _ (A.det_nonsing_inv_mul_det h)

@[simp] lemma nonsing_inv_nonsing_inv (h : is_unit A.det) : (A⁻¹)⁻¹ = A :=
calc (A⁻¹)⁻¹ = 1 ⬝ (A⁻¹)⁻¹        : by rw matrix.one_mul
         ... = A ⬝ A⁻¹ ⬝ (A⁻¹)⁻¹  : by rw A.mul_nonsing_inv h
         ... = A                  : by { rw [matrix.mul_assoc,
                                         (A⁻¹).mul_nonsing_inv (A.is_unit_nonsing_inv_det h),
                                         matrix.mul_one], }

lemma is_unit_nonsing_inv_det_iff {A : matrix n n α} :
  is_unit A⁻¹.det ↔ is_unit A.det :=
by rw [matrix.det_nonsing_inv, is_unit_ring_inverse]

/- `is_unit.invertible` lifts the proposition `is_unit A` to a constructive inverse of `A`. -/

/-- A version of `matrix.invertible_of_det_invertible` with the inverse defeq to `A⁻¹` that is
therefore noncomputable. -/
noncomputable def invertible_of_is_unit_det (h : is_unit A.det) : invertible A :=
⟨A⁻¹, nonsing_inv_mul A h, mul_nonsing_inv A h⟩

/-- A version of `matrix.units_of_det_invertible` with the inverse defeq to `A⁻¹` that is therefore
noncomputable. -/
noncomputable def nonsing_inv_unit (h : is_unit A.det) : (matrix n n α)ˣ :=
@unit_of_invertible _ _ _ (invertible_of_is_unit_det A h)

lemma unit_of_det_invertible_eq_nonsing_inv_unit [invertible A.det] :
  unit_of_det_invertible A = nonsing_inv_unit A (is_unit_of_invertible _) :=
by { ext, refl }

variables {A} {B}

/-- If matrix A is left invertible, then its inverse equals its left inverse. -/
lemma inv_eq_left_inv (h : B ⬝ A = 1) : A⁻¹ = B :=
begin
  letI := invertible_of_left_inverse _ _ h,
  exact inv_of_eq_nonsing_inv A ▸ inv_of_eq_left_inv h,
end

/-- If matrix A is right invertible, then its inverse equals its right inverse. -/
lemma inv_eq_right_inv (h : A ⬝ B = 1) : A⁻¹ = B :=
inv_eq_left_inv (mul_eq_one_comm.2 h)

section inv_eq_inv

variables {C : matrix n n α}

/-- The left inverse of matrix A is unique when existing. -/
lemma left_inv_eq_left_inv (h : B ⬝ A = 1) (g : C ⬝ A = 1) : B = C :=
by rw [←inv_eq_left_inv h, ←inv_eq_left_inv g]

/-- The right inverse of matrix A is unique when existing. -/
lemma right_inv_eq_right_inv (h : A ⬝ B = 1) (g : A ⬝ C = 1) : B = C :=
by rw [←inv_eq_right_inv h, ←inv_eq_right_inv g]

/-- The right inverse of matrix A equals the left inverse of A when they exist. -/
lemma right_inv_eq_left_inv (h : A ⬝ B = 1) (g : C ⬝ A = 1) : B = C :=
by rw [←inv_eq_right_inv h, ←inv_eq_left_inv g]

lemma inv_inj (h : A⁻¹ = B⁻¹) (h' : is_unit A.det) : A = B :=
begin
  refine left_inv_eq_left_inv (mul_nonsing_inv _ h') _,
  rw h,
  refine mul_nonsing_inv _ _,
  rwa [←is_unit_nonsing_inv_det_iff, ←h, is_unit_nonsing_inv_det_iff]
end

end inv_eq_inv

variable (A)

@[simp] lemma inv_zero : (0 : matrix n n α)⁻¹ = 0 :=
begin
  casesI (subsingleton_or_nontrivial α) with ht ht,
  { simp },
  cases (fintype.card n).zero_le.eq_or_lt with hc hc,
  { rw [eq_comm, fintype.card_eq_zero_iff] at hc,
    haveI := hc,
    ext i,
    exact (is_empty.false i).elim },
  { have hn : nonempty n := fintype.card_pos_iff.mp hc,
    refine nonsing_inv_apply_not_is_unit _ _,
    simp [hn] },
end

noncomputable instance : inv_one_class (matrix n n α) :=
{ inv_one := inv_eq_left_inv (by simp),
  ..matrix.has_one,
  ..matrix.has_inv }

lemma inv_smul (k : α) [invertible k] (h : is_unit A.det) : (k • A)⁻¹ = ⅟k • A⁻¹ :=
inv_eq_left_inv (by simp [h, smul_smul])

lemma inv_smul' (k : αˣ) (h : is_unit A.det) : (k • A)⁻¹ = k⁻¹ • A⁻¹ :=
inv_eq_left_inv (by simp [h, smul_smul])

lemma inv_adjugate (A : matrix n n α) (h : is_unit A.det) :
  (adjugate A)⁻¹ = h.unit⁻¹ • A :=
begin
  refine inv_eq_left_inv _,
  rw [smul_mul, mul_adjugate, units.smul_def, smul_smul, h.coe_inv_mul, one_smul]
end

/-- `diagonal v` is invertible if `v` is -/
def diagonal_invertible {α} [non_assoc_semiring α] (v : n → α) [invertible v] :
  invertible (diagonal v) :=
invertible.map (diagonal_ring_hom n α) v

lemma inv_of_diagonal_eq {α} [semiring α] (v : n → α) [invertible v] [invertible (diagonal v)] :
  ⅟(diagonal v) = diagonal (⅟v) :=
begin
  letI := diagonal_invertible v,
  haveI := invertible.subsingleton (diagonal v),
  convert (rfl : ⅟(diagonal v) = _),
end

/-- `v` is invertible if `diagonal v` is -/
def invertible_of_diagonal_invertible (v : n → α) [invertible (diagonal v)] : invertible v :=
{ inv_of := diag (⅟(diagonal v)),
  inv_of_mul_self := funext $ λ i, begin
    letI : invertible (diagonal v).det := det_invertible_of_invertible _,
    rw [inv_of_eq, diag_smul, adjugate_diagonal, diag_diagonal],
    dsimp,
    rw [mul_assoc, prod_erase_mul _ _ (finset.mem_univ _), ←det_diagonal],
    exact mul_inv_of_self _,
  end,
  mul_inv_of_self := funext $ λ i, begin
    letI : invertible (diagonal v).det := det_invertible_of_invertible _,
    rw [inv_of_eq, diag_smul, adjugate_diagonal, diag_diagonal],
    dsimp,
    rw [mul_left_comm, mul_prod_erase _ _ (finset.mem_univ _), ←det_diagonal],
    exact mul_inv_of_self _,
  end }

/-- Together `matrix.diagonal_invertible` and `matrix.invertible_of_diagonal_invertible` form an
equivalence, although both sides of the equiv are subsingleton anyway. -/
@[simps]
def diagonal_invertible_equiv_invertible (v : n → α) : invertible (diagonal v) ≃ invertible v :=
{ to_fun := @invertible_of_diagonal_invertible _ _ _ _ _ _,
  inv_fun := @diagonal_invertible _ _ _ _ _ _,
  left_inv := λ _, subsingleton.elim _ _,
  right_inv := λ _, subsingleton.elim _ _ }

/-- When lowered to a prop, `matrix.diagonal_invertible_equiv_invertible` forms an `iff`. -/
@[simp] lemma is_unit_diagonal {v : n → α} : is_unit (diagonal v) ↔ is_unit v :=
by simp only [← nonempty_invertible_iff_is_unit,
  (diagonal_invertible_equiv_invertible v).nonempty_congr]

lemma inv_diagonal (v : n → α) : (diagonal v)⁻¹ = diagonal (ring.inverse v) :=
begin
  rw nonsing_inv_eq_ring_inverse,
  by_cases h : is_unit v,
  { have := is_unit_diagonal.mpr h,
    casesI this.nonempty_invertible,
    casesI h.nonempty_invertible,
    rw [ring.inverse_invertible, ring.inverse_invertible, inv_of_diagonal_eq], },
  { have := is_unit_diagonal.not.mpr h,
    rw [ring.inverse_non_unit _ h, pi.zero_def, diagonal_zero, ring.inverse_non_unit _ this] }
end

@[simp] lemma inv_inv_inv (A : matrix n n α) : A⁻¹⁻¹⁻¹ = A⁻¹ :=
begin
  by_cases h : is_unit A.det,
  { rw [nonsing_inv_nonsing_inv _ h] },
  { simp [nonsing_inv_apply_not_is_unit _ h] }
end

lemma mul_inv_rev (A B : matrix n n α) : (A ⬝ B)⁻¹ = B⁻¹ ⬝ A⁻¹ :=
begin
  simp only [inv_def],
  rw [matrix.smul_mul, matrix.mul_smul, smul_smul, det_mul, adjugate_mul_distrib,
    ring.mul_inverse_rev],
end

/-- A version of `list.prod_inv_reverse` for `matrix.has_inv`. -/
lemma list_prod_inv_reverse : ∀ l : list (matrix n n α), l.prod⁻¹ = (l.reverse.map has_inv.inv).prod
| [] := by rw [list.reverse_nil, list.map_nil, list.prod_nil, inv_one]
| (A :: Xs) := by rw [list.reverse_cons', list.map_concat, list.prod_concat, list.prod_cons,
                      matrix.mul_eq_mul, matrix.mul_eq_mul, mul_inv_rev, list_prod_inv_reverse]

/-- One form of **Cramer's rule**. See `matrix.mul_vec_cramer` for a stronger form. -/
@[simp] lemma det_smul_inv_mul_vec_eq_cramer (A : matrix n n α) (b : n → α) (h : is_unit A.det) :
  A.det • A⁻¹.mul_vec b = cramer A b :=
begin
  rw [cramer_eq_adjugate_mul_vec, A.nonsing_inv_apply h, ← smul_mul_vec_assoc,
      smul_smul, h.mul_coe_inv, one_smul]
end

/-- One form of **Cramer's rule**. See `matrix.mul_vec_cramer` for a stronger form. -/
@[simp] lemma det_smul_inv_vec_mul_eq_cramer_transpose
  (A : matrix n n α) (b : n → α) (h : is_unit A.det) :
  A.det • A⁻¹.vec_mul b = cramer Aᵀ b :=
by rw [← (A⁻¹).transpose_transpose, vec_mul_transpose, transpose_nonsing_inv, ← det_transpose,
    Aᵀ.det_smul_inv_mul_vec_eq_cramer _ (is_unit_det_transpose A h)]

/-! ### More results about determinants -/

section det
variables [fintype m] [decidable_eq m]

/-- A variant of `matrix.det_units_conj`. -/
lemma det_conj {M : matrix m m α} (h : is_unit M) (N : matrix m m α) :
  det (M ⬝ N ⬝ M⁻¹) = det N :=
by rw [←h.unit_spec, ←coe_units_inv, det_units_conj]

/-- A variant of `matrix.det_units_conj'`. -/
lemma det_conj' {M : matrix m m α} (h : is_unit M) (N : matrix m m α) :
  det (M⁻¹ ⬝ N ⬝ M) = det N :=
by rw [←h.unit_spec, ←coe_units_inv, det_units_conj']

/-- Determinant of a 2×2 block matrix, expanded around an invertible top left element in terms of
the Schur complement. -/
lemma det_from_blocks₁₁ (A : matrix m m α) (B : matrix m n α) (C : matrix n m α) (D : matrix n n α)
  [invertible A] : (matrix.from_blocks A B C D).det = det A * det (D - C ⬝ (⅟A) ⬝ B) :=
begin
  have : from_blocks A B C D =
    from_blocks 1 0 (C ⬝ ⅟A) 1 ⬝ from_blocks A 0 0 (D - C ⬝ (⅟A) ⬝ B) ⬝ from_blocks 1 (⅟A ⬝ B) 0 1,
  { simp only [from_blocks_multiply, matrix.mul_zero, matrix.zero_mul, add_zero, zero_add,
      matrix.one_mul, matrix.mul_one, matrix.inv_of_mul_self, matrix.mul_inv_of_self_assoc,
        matrix.mul_inv_of_mul_self_cancel, matrix.mul_assoc, add_sub_cancel'_right] },
  rw [this, det_mul, det_mul, det_from_blocks_zero₂₁, det_from_blocks_zero₂₁,
    det_from_blocks_zero₁₂, det_one, det_one, one_mul, one_mul, mul_one],
end

@[simp] lemma det_from_blocks_one₁₁ (B : matrix m n α) (C : matrix n m α) (D : matrix n n α) :
  (matrix.from_blocks 1 B C D).det = det (D - C ⬝ B) :=
begin
  haveI : invertible (1 : matrix m m α) := invertible_one,
  rw [det_from_blocks₁₁, inv_of_one, matrix.mul_one, det_one, one_mul],
end

/-- Determinant of a 2×2 block matrix, expanded around an invertible bottom right element in terms
of the Schur complement. -/
lemma det_from_blocks₂₂ (A : matrix m m α) (B : matrix m n α) (C : matrix n m α) (D : matrix n n α)
  [invertible D] : (matrix.from_blocks A B C D).det = det D * det (A - B ⬝ (⅟D) ⬝ C) :=
begin
  have : from_blocks A B C D = (from_blocks D C B A).submatrix (sum_comm _ _) (sum_comm _ _),
  { ext i j,
    cases i; cases j; refl },
  rw [this, det_submatrix_equiv_self, det_from_blocks₁₁],
end

@[simp] lemma det_from_blocks_one₂₂ (A : matrix m m α) (B : matrix m n α) (C : matrix n m α) :
  (matrix.from_blocks A B C 1).det = det (A - B ⬝ C) :=
begin
  haveI : invertible (1 : matrix n n α) := invertible_one,
  rw [det_from_blocks₂₂, inv_of_one, matrix.mul_one, det_one, one_mul],
end

/-- The **Weinstein–Aronszajn identity**. Note the `1` on the LHS is of shape m×m, while the `1` on
the RHS is of shape n×n. -/
lemma det_one_add_mul_comm (A : matrix m n α) (B : matrix n m α) :
  det (1 + A ⬝ B) = det (1 + B ⬝ A) :=
calc  det (1 + A ⬝ B)
    = det (from_blocks 1 (-A) B 1) : by rw [det_from_blocks_one₂₂, matrix.neg_mul, sub_neg_eq_add]
... = det (1 + B ⬝ A)              : by rw [det_from_blocks_one₁₁, matrix.mul_neg, sub_neg_eq_add]

/-- Alternate statement of the **Weinstein–Aronszajn identity** -/
lemma det_mul_add_one_comm (A : matrix m n α) (B : matrix n m α) :
  det (A ⬝ B + 1) = det (B ⬝ A + 1) :=
by rw [add_comm, det_one_add_mul_comm, add_comm]

lemma det_one_sub_mul_comm (A : matrix m n α) (B : matrix n m α) :
  det (1 - A ⬝ B) = det (1 - B ⬝ A) :=
by rw [sub_eq_add_neg, ←matrix.neg_mul, det_one_add_mul_comm, matrix.mul_neg, ←sub_eq_add_neg]

/-- A special case of the **Matrix determinant lemma** for when `A = I`.

TODO: show this more generally. -/
lemma det_one_add_col_mul_row (u v : m → α) : det (1 + col u ⬝ row v) = 1 + v ⬝ᵥ u :=
by rw [det_one_add_mul_comm, det_unique, pi.add_apply, pi.add_apply, matrix.one_apply_eq,
       matrix.row_mul_col_apply]

end det

end matrix
