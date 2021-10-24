/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import linear_algebra.matrix.nonsingular_inverse

/-!
# Integer powers of square matrices

In this file, we define integer power of matrices, relying on
the nonsingular inverse definition for negative powers.

## Implementation details

The main definition is a direct recursive call on the integer inductive type,
as provided by the `div_inv_monoid.gpow` default implementation.
The lemma names are taken from `algebra.group_with_zero.power`.

## Tags

matrix inverse, matrix powers
-/

open_locale matrix

namespace matrix

variables {n' : Type*} [decidable_eq n'] [fintype n'] {R : Type*} [comm_ring R]

local notation `M` := matrix n' n' R

noncomputable instance : div_inv_monoid M :=
{ ..(show monoid M, by apply_instance),
  ..(show has_inv M, by apply_instance) }

section nat_pow

@[simp] theorem inv_pow' (A : M) (n : ℕ) : (A⁻¹) ^ n = (A ^ n)⁻¹ :=
begin
  induction n with n ih,
  { simp },
  { rw [pow_succ A, mul_eq_mul, mul_inv_rev, ← ih, ← mul_eq_mul, ← pow_succ'] }
end

theorem pow_sub' (A : M) {m n : ℕ} (ha : is_unit A.det) (h : n ≤ m) :
  A ^ (m - n) = A ^ m ⬝ (A ^ n)⁻¹ :=
begin
  rw [←nat.sub_add_cancel h, pow_add, mul_eq_mul, matrix.mul_assoc, mul_nonsing_inv,
      nat.sub_add_cancel h, matrix.mul_one],
  simpa using ha.pow n
end

theorem pow_inv_comm' (A : M) (m n : ℕ) : (A⁻¹) ^ m ⬝ A ^ n = A ^ n ⬝ (A⁻¹) ^ m :=
begin
  induction n with n IH generalizing m,
  { simp },
  cases m,
  { simp },
  rcases nonsing_inv_cancel_or_zero A with ⟨h, h'⟩ | h,
  { calc  A⁻¹ ^ (m + 1) ⬝ A ^ (n + 1)
        = A⁻¹ ^ m ⬝ (A⁻¹ ⬝ A) ⬝ A ^ n :
          by simp only [pow_succ' A⁻¹, pow_succ A, mul_eq_mul, matrix.mul_assoc]
    ... = A ^ n ⬝ A⁻¹ ^ m :
          by simp only [h, matrix.mul_one, matrix.one_mul, IH m]
    ... = A ^ n ⬝ (A ⬝ A⁻¹) ⬝ A⁻¹ ^ m :
          by simp only [h', matrix.mul_one, matrix.one_mul]
    ... = A ^ (n + 1) ⬝ A⁻¹ ^ (m + 1) :
          by simp only [pow_succ' A, pow_succ A⁻¹, mul_eq_mul, matrix.mul_assoc] },
  { simp [h] }
end

end nat_pow

section int_pow
open int

@[simp] theorem one_fpow : ∀ (n : ℤ), (1 : M) ^ n = 1
| (n : ℕ) := by rw [gpow_coe_nat, one_pow]
| -[1+ n] := by rw [gpow_neg_succ_of_nat, one_pow, inv_one]

lemma zero_fpow : ∀ z : ℤ, z ≠ 0 → (0 : M) ^ z = 0
| (n : ℕ) h := by { rw [gpow_coe_nat, zero_pow], refine lt_of_le_of_ne n.zero_le (ne.symm _),
  simpa using h  }
| -[1+n]  h := by simp [zero_pow n.zero_lt_succ]

lemma zero_fpow_eq (n : ℤ) : (0 : M) ^ n = if n = 0 then 1 else 0 :=
begin
  split_ifs with h,
  { rw [h, gpow_zero] },
  { rw [zero_fpow _ h] }
end

theorem inv_fpow (A : M) : ∀n:ℤ, A⁻¹ ^ n = (A ^ n)⁻¹
| (n : ℕ) := by rw [gpow_coe_nat, gpow_coe_nat, inv_pow']
| -[1+ n] := by rw [gpow_neg_succ_of_nat, gpow_neg_succ_of_nat, inv_pow']

@[simp] lemma fpow_neg_one (A : M) : A ^ (-1 : ℤ) = A⁻¹ :=
begin
  convert div_inv_monoid.gpow_neg' 0 A,
  simp only [gpow_one, int.coe_nat_zero, int.coe_nat_succ, gpow_eq_pow, zero_add]
end

theorem fpow_coe_nat (A : M) (n : ℕ) : A ^ (n : ℤ) = (A ^ n) :=
gpow_coe_nat _ _

@[simp] theorem fpow_neg_coe_nat (A : M) (n : ℕ) : A ^ (-n : ℤ) = (A ^ n)⁻¹ :=
begin
  cases n,
  { simp },
  { exact div_inv_monoid.gpow_neg' _ _ }
end

lemma _root_.is_unit.det_fpow {A : M} (h : is_unit A.det) (n : ℤ) : is_unit (A ^ n).det :=
begin
  cases n,
  { simpa using h.pow n },
  { simpa using h.pow n.succ }
end

lemma is_unit_det_fpow_iff {A : M} {z : ℤ} :
  is_unit (A ^ z).det ↔ is_unit A.det ∨ z = 0 :=
begin
  induction z using int.induction_on with z IH z IH,
  { simp },
  { rw [←int.coe_nat_succ, fpow_coe_nat, det_pow, is_unit_pos_pow_iff (z.zero_lt_succ),
        ←int.coe_nat_zero, int.coe_nat_eq_coe_nat_iff],
    simp },
  { rw [←neg_add', ←int.coe_nat_succ, fpow_neg_coe_nat, is_unit_nonsing_inv_det_iff,
        det_pow, is_unit_pos_pow_iff (z.zero_lt_succ), neg_eq_zero, ←int.coe_nat_zero,
        int.coe_nat_eq_coe_nat_iff],
    simp }
end

theorem fpow_neg {A : M} (h : is_unit A.det) : ∀ (n : ℤ), A ^ -n = (A ^ n)⁻¹
| (n : ℕ) := fpow_neg_coe_nat _ _
| -[1+ n] := by { rw [gpow_neg_succ_of_nat, neg_neg_of_nat_succ, of_nat_eq_coe, fpow_coe_nat,
                      nonsing_inv_nonsing_inv],
                  rw det_pow,
                  exact h.pow _ }

lemma inv_fpow' {A : M} (h : is_unit A.det) (n : ℤ) :
  (A ⁻¹) ^ n = A ^ (-n) :=
by rw [fpow_neg h, inv_fpow]

lemma fpow_add_one {A : M} (h : is_unit A.det) : ∀ n : ℤ, A ^ (n + 1) = A ^ n * A
| (n : ℕ)        := by simp [← int.coe_nat_succ, pow_succ']
| -((n : ℕ) + 1) :=
calc  A ^ (-(n + 1) + 1 : ℤ)
    = (A ^ n)⁻¹ : by rw [neg_add, neg_add_cancel_right, fpow_neg h, fpow_coe_nat]
... = (A ⬝ A ^ n)⁻¹ ⬝ A : by rw [mul_inv_rev, matrix.mul_assoc, nonsing_inv_mul _ h, matrix.mul_one]
... = A ^ -(n + 1 : ℤ) * A :
      by rw [fpow_neg h, ← int.coe_nat_succ, fpow_coe_nat, pow_succ, mul_eq_mul, mul_eq_mul]

lemma fpow_sub_one {A : M} (h : is_unit A.det) (n : ℤ) : A ^ (n - 1) = A ^ n * A⁻¹ :=
calc A ^ (n - 1) = A ^ (n - 1) * A * A⁻¹ : by rw [mul_assoc, mul_eq_mul A, mul_nonsing_inv _ h,
                                                  mul_one]
             ... = A^n * A⁻¹             : by rw [← fpow_add_one h, sub_add_cancel]

lemma fpow_add {A : M} (ha : is_unit A.det) (m n : ℤ) : A ^ (m + n) = A ^ m * A ^ n :=
begin
  induction n using int.induction_on with n ihn n ihn,
  case hz : { simp },
  { simp only [← add_assoc, fpow_add_one ha, ihn, mul_assoc] },
  { rw [fpow_sub_one ha, ← mul_assoc, ← ihn, ← fpow_sub_one ha, add_sub_assoc] }
end

lemma fpow_add_of_nonpos {A : M} {m n : ℤ} (hm : m ≤ 0) (hn : n ≤ 0) :
  A ^ (m + n) = A ^ m * A ^ n :=
begin
  rcases nonsing_inv_cancel_or_zero A with ⟨h, h'⟩ | h,
  { exact fpow_add (is_unit_det_of_left_inverse h) m n },
  { obtain ⟨k, rfl⟩ := exists_eq_neg_of_nat hm,
    obtain ⟨l, rfl⟩ := exists_eq_neg_of_nat hn,
    simp_rw [←neg_add, ←int.coe_nat_add, fpow_neg_coe_nat, ←inv_pow', h, pow_add] }
end

lemma fpow_add_of_nonneg {A : M} {m n : ℤ} (hm : 0 ≤ m) (hn : 0 ≤ n) :
  A ^ (m + n) = A ^ m * A ^ n :=
begin
  rcases nonsing_inv_cancel_or_zero A with ⟨h, h'⟩ | h,
  { exact fpow_add (is_unit_det_of_left_inverse h) m n },
  { obtain ⟨k, rfl⟩ := eq_coe_of_zero_le hm,
    obtain ⟨l, rfl⟩ := eq_coe_of_zero_le hn,
    rw [←int.coe_nat_add, fpow_coe_nat, fpow_coe_nat, fpow_coe_nat, pow_add] }
end

theorem fpow_one_add {A : M} (h : is_unit A.det) (i : ℤ) : A ^ (1 + i) = A * A ^ i :=
by rw [fpow_add h, gpow_one]

theorem semiconj_by.fpow_right {A X Y : M} (hx : is_unit X.det) (hy : is_unit Y.det)
  (h : semiconj_by A X Y) :
  ∀ m : ℤ, semiconj_by A (X^m) (Y^m)
| (n : ℕ) := by simp [h.pow_right n]
| -[1+n]  := begin
  by_cases ha : A = 0,
  { simp only [ha, semiconj_by.zero_left] },
  have hx' : is_unit (X ^ n.succ).det,
  { rw det_pow,
    exact hx.pow n.succ },
  have hy' : is_unit (Y ^ n.succ).det,
  { rw det_pow,
    exact hy.pow n.succ },
  rw [gpow_neg_succ_of_nat, gpow_neg_succ_of_nat, nonsing_inv_apply _ hx', nonsing_inv_apply _ hy',
      semiconj_by],
  refine (is_regular_of_is_left_regular_det hy'.is_regular.left).left _,
  rw [←mul_assoc, ←(h.pow_right n.succ).eq, mul_assoc, mul_eq_mul (X ^ _), mul_smul, mul_adjugate,
      mul_eq_mul, mul_eq_mul, mul_eq_mul, ←matrix.mul_assoc, mul_smul (Y ^ _) (↑(hy'.unit)⁻¹ : R),
      mul_adjugate, smul_smul, smul_smul, hx'.coe_inv_mul,
      hy'.coe_inv_mul, one_smul, matrix.mul_one, matrix.one_mul],
end

theorem commute.fpow_right {A B : M} (h : commute A B) (m : ℤ) : commute A (B^m) :=
begin
  rcases nonsing_inv_cancel_or_zero B with ⟨hB, hB'⟩ | hB,
  { refine semiconj_by.fpow_right _ _ h _;
    exact is_unit_det_of_left_inverse hB },
  { cases m,
    { simpa using h.pow_right _ },
    { simp [←inv_pow', hB] } }
end

theorem commute.fpow_left {A B : M} (h : commute A B) (m : ℤ) : commute (A^m) B :=
(commute.fpow_right h.symm m).symm

theorem commute.fpow_fpow {A B : M} (h : commute A B) (m n : ℤ) : commute (A^m) (B^n) :=
commute.fpow_right (commute.fpow_left h _) _

theorem commute.fpow_self (A : M) (n : ℤ) : commute (A^n) A :=
commute.fpow_left (commute.refl A) _

theorem commute.self_fpow (A : M) (n : ℤ) : commute A (A^n) :=
commute.fpow_right (commute.refl A) _

theorem commute.fpow_fpow_self (A : M) (m n : ℤ) : commute (A^m) (A^n) :=
commute.fpow_fpow (commute.refl A) _ _

theorem fpow_bit0 (A : M) (n : ℤ) : A ^ bit0 n = A ^ n * A ^ n :=
begin
  cases le_total 0 n with nonneg nonpos,
  { exact fpow_add_of_nonneg nonneg nonneg },
  { exact fpow_add_of_nonpos nonpos nonpos }
end

lemma fpow_add_one_of_ne_neg_one {A : M} : ∀ (n : ℤ), n ≠ -1 → A ^ (n + 1) = A ^ n * A
| (n : ℕ) _ := by simp [← int.coe_nat_succ, pow_succ']
| (-1) h := absurd rfl h
| (-((n : ℕ) + 2)) _ := begin
  rcases nonsing_inv_cancel_or_zero A with ⟨h, h'⟩ | h,
  { apply fpow_add_one (is_unit_det_of_left_inverse h) },
  { show A ^ (-((n + 1 : ℕ) : ℤ)) = A ^ -((n + 2 : ℕ) : ℤ) * A,
    simp_rw [fpow_neg_coe_nat, ←inv_pow', h, zero_pow nat.succ_pos', zero_mul] }
end

theorem fpow_bit1 (A : M) (n : ℤ) : A ^ bit1 n = A ^ n * A ^ n * A :=
begin
  rw [bit1, fpow_add_one_of_ne_neg_one, fpow_bit0],
  intro h,
  simpa using congr_arg bodd h
end

theorem fpow_mul (A : M) (h : is_unit A.det) : ∀ m n : ℤ, A ^ (m * n) = (A ^ m) ^ n
| (m : ℕ) (n : ℕ) := by rw [gpow_coe_nat, gpow_coe_nat, ← pow_mul, ← gpow_coe_nat, int.coe_nat_mul]
| (m : ℕ) -[1+ n] := by rw [gpow_coe_nat, gpow_neg_succ_of_nat, ← pow_mul, coe_nat_mul_neg_succ,
    ←int.coe_nat_mul, fpow_neg_coe_nat]
| -[1+ m] (n : ℕ) := by rw [gpow_coe_nat, gpow_neg_succ_of_nat, ← inv_pow', ← pow_mul,
    neg_succ_mul_coe_nat, ←int.coe_nat_mul, fpow_neg_coe_nat, inv_pow']
| -[1+ m] -[1+ n] := by { rw [gpow_neg_succ_of_nat, gpow_neg_succ_of_nat, neg_succ_mul_neg_succ,
    ←int.coe_nat_mul, fpow_coe_nat, inv_pow', ←pow_mul, nonsing_inv_nonsing_inv],
    rw det_pow,
    exact h.pow _ }

theorem fpow_mul' (A : M) (h : is_unit A.det) (m n : ℤ) : A ^ (m * n) = (A ^ n) ^ m :=
by rw [mul_comm, fpow_mul _ h]

@[simp, norm_cast] lemma units.coe_inv'' (u : units M) :
  ((u⁻¹ : units M) : M) = u⁻¹ :=
begin
  refine (inv_eq_left_inv _).symm,
  rw [←mul_eq_mul, ←units.coe_mul, inv_mul_self, units.coe_one]
end

@[simp, norm_cast] lemma units.coe_fpow (u : units M) :
  ∀ (n : ℤ), ((u ^ n : units M) : M) = u ^ n
| (n : ℕ) := by rw [gpow_coe_nat, gpow_coe_nat, units.coe_pow]
| -[1+k] := by rw [gpow_neg_succ_of_nat, gpow_neg_succ_of_nat, ←inv_pow, u⁻¹.coe_pow, ←inv_pow',
                   units.coe_inv'']

lemma fpow_ne_zero_of_is_unit_det [nonempty n'] [nontrivial R] {A : M}
  (ha : is_unit A.det) (z : ℤ) : A ^ z ≠ 0 :=
begin
  have := ha.det_fpow z,
  contrapose! this,
  rw [this, det_zero ‹_›],
  exact not_is_unit_zero
end

lemma fpow_sub {A : M} (ha : is_unit A.det) (z1 z2 : ℤ) : A ^ (z1 - z2) = A ^ z1 / A ^ z2 :=
by rw [sub_eq_add_neg, fpow_add ha, fpow_neg ha, div_eq_mul_inv]

lemma commute.mul_fpow {A B : M} (h : commute A B) :
  ∀ (i : ℤ), (A * B) ^ i = (A ^ i) * (B ^ i)
| (n : ℕ) := by simp [h.mul_pow n, -mul_eq_mul]
| -[1+n]  := by rw [gpow_neg_succ_of_nat, gpow_neg_succ_of_nat, gpow_neg_succ_of_nat,
                    mul_eq_mul (_⁻¹), ←mul_inv_rev, ←mul_eq_mul, h.mul_pow n.succ,
                    (h.pow_pow _ _).eq]

theorem fpow_bit0' (A : M) (n : ℤ) : A ^ bit0 n = (A * A) ^ n :=
(fpow_bit0 A n).trans (commute.mul_fpow (commute.refl A) n).symm

theorem fpow_bit1' (A : M) (n : ℤ) : A ^ bit1 n = (A * A) ^ n * A :=
by rw [fpow_bit1, commute.mul_fpow (commute.refl A)]

theorem fpow_neg_mul_fpow_self (n : ℤ) {A : M} (h : is_unit A.det) :
  A ^ (-n) * A ^ n = 1 :=
by rw [fpow_neg h, mul_eq_mul, nonsing_inv_mul _ (h.det_fpow _)]

theorem one_div_pow {A : M} (n : ℕ) :
  (1 / A) ^ n = 1 / A ^ n :=
by simp only [one_div, inv_pow']

theorem one_div_fpow {A : M} (n : ℤ) :
  (1 / A) ^ n = 1 / A ^ n :=
by simp only [one_div, inv_fpow]

end int_pow

end matrix
