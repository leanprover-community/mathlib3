/-
Copyright (c) 2019 Tim Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baanen, Lu-Ming Zhang
-/
import algebra.regular.smul
import data.matrix.notation
import linear_algebra.matrix.polynomial
import linear_algebra.matrix.adjugate

/-!
# Nonsingular inverses

In this file, we define an inverse for square matrices of invertible
determinant. For matrices that are not square or not of full rank, there is a
more general notion of pseudoinverses which we do not consider here.

The definition of inverse used in this file is the adjugate divided by the determinant.
We show that dividing the adjugate by `det A` (if possible), giving a matrix `A⁻¹` (`nonsing_inv`),
will result in a multiplicative inverse to `A`.

## References

  * https://en.wikipedia.org/wiki/Cramer's_rule#Finding_inverse_matrix

## Tags

matrix inverse, cramer, cramer's rule, adjugate
-/

namespace matrix
universes u v
variables {n : Type u} [decidable_eq n] [fintype n] {α : Type v} [comm_ring α]
open_locale matrix big_operators
open equiv equiv.perm finset

variables (A : matrix n n α) (B : matrix n n α)

open_locale classical

lemma is_unit_det_transpose (h : is_unit A.det) : is_unit Aᵀ.det :=
by { rw det_transpose, exact h, }


/-- The inverse of a square matrix, when it is invertible (and zero otherwise).-/
noncomputable instance : has_inv (matrix n n α) := ⟨λ A, ring.inverse A.det • A.adjugate⟩

lemma inv_def (A : matrix n n α) : A⁻¹ = ring.inverse A.det • A.adjugate := rfl

lemma nonsing_inv_apply_not_is_unit (h : ¬ is_unit A.det) :
  A⁻¹ = 0 :=
by rw [inv_def, ring.inverse_non_unit _ h, zero_smul]

lemma nonsing_inv_apply (h : is_unit A.det) :
  A⁻¹ = (↑h.unit⁻¹ : α) • A.adjugate :=
begin
  rw [inv_def, ←ring.inverse_unit h.unit],
  refl,
end

lemma transpose_nonsing_inv : (A⁻¹)ᵀ = (Aᵀ)⁻¹ :=
by rw [inv_def, inv_def, transpose_smul, det_transpose, adjugate_transpose]

/-- The `nonsing_inv` of `A` is a right inverse. -/
@[simp] lemma mul_nonsing_inv (h : is_unit A.det) : A ⬝ A⁻¹ = 1 :=
by rw [A.nonsing_inv_apply h, mul_smul, mul_adjugate, smul_smul,
       units.inv_mul_of_eq h.unit_spec, one_smul]

/-- The `nonsing_inv` of `A` is a left inverse. -/
@[simp] lemma nonsing_inv_mul (h : is_unit A.det) : A⁻¹ ⬝ A = 1 :=
calc A⁻¹ ⬝ A = (Aᵀ ⬝ (Aᵀ)⁻¹)ᵀ : by { rw [transpose_mul,
                                    Aᵀ.transpose_nonsing_inv,
                                    transpose_transpose], }
         ... = 1ᵀ             : by { rw Aᵀ.mul_nonsing_inv, exact A.is_unit_det_transpose h, }
         ... = 1              : transpose_one

lemma nonsing_inv_cancel_or_zero :
  (A⁻¹ ⬝ A = 1 ∧ A ⬝ A⁻¹ = 1) ∨ A⁻¹ = 0 :=
begin
  by_cases h : is_unit A.det,
  { exact or.inl ⟨nonsing_inv_mul _ h, mul_nonsing_inv _ h⟩ },
  { exact or.inr (nonsing_inv_apply_not_is_unit _ h) }
end

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

@[simp] lemma is_unit_nonsing_inv_det_iff {A : matrix n n α} :
  is_unit A⁻¹.det ↔ is_unit A.det :=
begin
  refine ⟨λ h, _, is_unit_nonsing_inv_det _⟩,
  nontriviality α,
  casesI is_empty_or_nonempty n,
  { simp },
  contrapose! h,
  rw [nonsing_inv_apply_not_is_unit _ h, det_zero],
  { simp },
  { apply_instance }
end

/-- If `A.det` has a constructive inverse, produce one for `A`. -/
def invertible_of_det_invertible [invertible A.det] : invertible A :=
{ inv_of := ⅟A.det • A.adjugate,
  mul_inv_of_self :=
    by rw [mul_smul_comm, matrix.mul_eq_mul, mul_adjugate, smul_smul, inv_of_mul_self, one_smul],
  inv_of_mul_self :=
    by rw [smul_mul_assoc, matrix.mul_eq_mul, adjugate_mul, smul_smul, inv_of_mul_self, one_smul] }

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

/-- Given a proof that `A.det` has a constructive inverse, lift `A` to `units (matrix n n α)`-/
def unit_of_det_invertible [invertible A.det] : units (matrix n n α) :=
@unit_of_invertible _ _ A (invertible_of_det_invertible A)

/-- A matrix whose determinant is a unit is itself a unit. This is a noncomputable version of
`matrix.units_of_det_invertible`, with the inverse defeq to `matrix.nonsing_inv`. -/
noncomputable def nonsing_inv_unit (h : is_unit A.det) : units (matrix n n α) :=
{ val     := A,
  inv     := A⁻¹,
  val_inv := by { rw matrix.mul_eq_mul, apply A.mul_nonsing_inv h, },
  inv_val := by { rw matrix.mul_eq_mul, apply A.nonsing_inv_mul h, } }

lemma unit_of_det_invertible_eq_nonsing_inv_unit [invertible A.det] :
  unit_of_det_invertible A = nonsing_inv_unit A (is_unit_of_invertible _) :=
by { ext, refl }

/-- When lowered to a prop, `matrix.det_invertible_of_invertible` and
`matrix.invertible_of_det_invertible` form an `iff`. -/
lemma is_unit_iff_is_unit_det : is_unit A ↔ is_unit A.det :=
begin
  split; rintros ⟨x, hx⟩; refine @is_unit_of_invertible _ _ _ (id _),
  { haveI : invertible A := hx.rec x.invertible,
    apply det_invertible_of_invertible, },
  { haveI : invertible A.det := hx.rec x.invertible,
    apply invertible_of_det_invertible, },
end

/- `is_unit_of_invertible A`
   converts the "stronger" condition `invertible A` to proposition `is_unit A`. -/

/-- `matrix.is_unit_det_of_invertible` converts `invertible A` to `is_unit A.det`. -/
lemma is_unit_det_of_invertible [invertible A] : is_unit A.det :=
@is_unit_of_invertible _ _ _(det_invertible_of_invertible A)

@[simp]
lemma inv_eq_nonsing_inv_of_invertible [invertible A] : ⅟ A = A⁻¹ :=
begin
  suffices : is_unit A,
  { rw [←this.mul_left_inj, inv_of_mul_self, matrix.mul_eq_mul, nonsing_inv_mul],
    rwa ←is_unit_iff_is_unit_det },
  exact is_unit_of_invertible _
end

variables {A} {B}

/- `is_unit.invertible` lifts the proposition `is_unit A` to a constructive inverse of `A`. -/

/-- "Lift" the proposition `is_unit A.det` to a constructive inverse of `A`. -/
noncomputable def invertible_of_is_unit_det  (h : is_unit A.det) : invertible A :=
⟨A⁻¹, nonsing_inv_mul A h, mul_nonsing_inv A h⟩

lemma is_unit_det_of_left_inverse (h : B ⬝ A = 1) : is_unit A.det :=
@is_unit_of_invertible _ _ _ (det_invertible_of_left_inverse _ _ h)

lemma is_unit_det_of_right_inverse (h : A ⬝ B = 1) : is_unit A.det :=
@is_unit_of_invertible _ _ _ (det_invertible_of_right_inverse _ _ h)

lemma det_ne_zero_of_left_inverse [nontrivial α] (h : B ⬝ A = 1) : A.det ≠ 0 :=
is_unit.ne_zero (matrix.is_unit_det_of_left_inverse h)

lemma det_ne_zero_of_right_inverse [nontrivial α] (h : A ⬝ B = 1) : A.det ≠ 0 :=
is_unit.ne_zero (matrix.is_unit_det_of_right_inverse h)

lemma nonsing_inv_left_right (h : A ⬝ B = 1) : B ⬝ A = 1 :=
begin
  have h' : is_unit B.det := is_unit_det_of_left_inverse h,
  calc B ⬝ A = (B ⬝ A) ⬝ (B ⬝ B⁻¹) : by simp only [h', matrix.mul_one, mul_nonsing_inv]
        ... = B ⬝ ((A ⬝ B) ⬝ B⁻¹) : by simp only [matrix.mul_assoc]
        ... = B ⬝ B⁻¹ : by simp only [h, matrix.one_mul]
        ... = 1 : mul_nonsing_inv B h',
end

lemma nonsing_inv_right_left (h : B ⬝ A = 1) : A ⬝ B = 1 :=
nonsing_inv_left_right h

/-- If matrix A is left invertible, then its inverse equals its left inverse. -/
lemma inv_eq_left_inv (h : B ⬝ A = 1) : A⁻¹ = B :=
begin
  have h1 :=  (is_unit_det_of_left_inverse h),
  have h2 := matrix.invertible_of_is_unit_det h1,
  have := @inv_of_eq_left_inv (matrix n n α) (infer_instance) A B h2 h,
  simp* at *,
end

/-- If matrix A is right invertible, then its inverse equals its right inverse. -/
lemma inv_eq_right_inv (h : A ⬝ B = 1) : A⁻¹ = B :=
begin
  have h1 :=  (is_unit_det_of_right_inverse h),
  have h2 := matrix.invertible_of_is_unit_det h1,
  have := @inv_of_eq_right_inv (matrix n n α) (infer_instance) A B h2 h,
  simp* at *,
end

/-- We can construct an instance of invertible A if A has a left inverse. -/
def invertible_of_left_inverse (h: B ⬝ A = 1) : invertible A :=
⟨B, h, nonsing_inv_right_left h⟩

/-- We can construct an instance of invertible A if A has a right inverse. -/
def invertible_of_right_inverse (h: A ⬝ B = 1) : invertible A :=
⟨B, nonsing_inv_left_right h, h⟩

section inv_eq_inv

variables {C : matrix n n α}

/-- The left inverse of matrix A is unique when existing. -/
lemma left_inv_eq_left_inv (h: B ⬝ A = 1) (g: C ⬝ A = 1) : B = C :=
by rw [←(inv_eq_left_inv h), ←(inv_eq_left_inv g)]

/-- The right inverse of matrix A is unique when existing. -/
lemma right_inv_eq_right_inv (h: A ⬝ B = 1) (g: A ⬝ C = 1) : B = C :=
by rw [←(inv_eq_right_inv h), ←(inv_eq_right_inv g)]

/-- The right inverse of matrix A equals the left inverse of A when they exist. -/
lemma right_inv_eq_left_inv (h: A ⬝ B = 1) (g: C ⬝ A = 1) : B = C :=
by rw [←(inv_eq_right_inv h), ←(inv_eq_left_inv g)]

lemma inv_inj (h : A⁻¹ = B⁻¹) (h' : is_unit A.det) : A = B :=
begin
  refine left_inv_eq_left_inv (mul_nonsing_inv _ h') _,
  rw h,
  refine mul_nonsing_inv _ _,
  rwa [←is_unit_nonsing_inv_det_iff, ←h, is_unit_nonsing_inv_det_iff]
end

end inv_eq_inv

variable (A)

@[simp] lemma mul_inv_of_invertible [invertible A] : A ⬝ A⁻¹ = 1 :=
mul_nonsing_inv A (is_unit_det_of_invertible A)

@[simp] lemma inv_mul_of_invertible [invertible A] : A⁻¹ ⬝ A = 1 :=
nonsing_inv_mul A (is_unit_det_of_invertible A)

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

@[simp] lemma inv_one : (1 : matrix n n α)⁻¹ = 1 :=
inv_eq_left_inv (by simp)

lemma inv_smul (k : α) [invertible k] (h : is_unit A.det) : (k • A)⁻¹ = ⅟k • A⁻¹ :=
inv_eq_left_inv (by simp [h, smul_smul])

lemma inv_smul' (k : units α) (h : is_unit A.det) : (k • A)⁻¹ = k⁻¹ • A⁻¹ :=
inv_eq_left_inv (by simp [h, smul_smul])

lemma inv_adjugate (A : matrix n n α) (h : is_unit A.det) :
  (adjugate A)⁻¹ = h.unit⁻¹ • A :=
begin
  refine inv_eq_left_inv _,
  rw [smul_mul, mul_adjugate, units.smul_def, smul_smul, h.coe_inv_mul, one_smul]
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

/-- One form of **Cramer's rule**. See `matrix.mul_vec_cramer` for a stronger form. -/
@[simp] lemma det_smul_inv_mul_vec_eq_cramer (A : matrix n n α) (b : n → α) (h : is_unit A.det) :
  A.det • A⁻¹.mul_vec b = cramer A b :=
begin
  rw [cramer_eq_adjugate_mul_vec, A.nonsing_inv_apply h, ← smul_mul_vec_assoc,
      smul_smul, h.mul_coe_inv, one_smul]
end

end matrix
