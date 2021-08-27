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

variables {n' : Type*} [decidable_eq n'] [fintype n'] {K : Type*} [comm_ring K]

lemma smul_pow {α R : Type*} [semiring α] [monoid R] [distrib_mul_action R α]
  [is_scalar_tower R α α] [smul_comm_class R α α]
  (k : R) (A : matrix n' n' α) (p : ℕ) :
  (k • A) ^ p = k ^ p • A ^ p :=
begin
  induction p with p IH,
  { simp },
  { rw [pow_succ', IH, smul_mul_smul, ←pow_succ', ←pow_succ'] }
end

local notation `M` := matrix n' n' K

noncomputable instance : div_inv_monoid M :=
{ ..(show monoid M, by apply_instance),
  ..(show has_inv M, by apply_instance) }

section nat_pow

@[simp] theorem inv_pow' (A : M) (n : ℕ) : (A⁻¹) ^ n = (A ^ n)⁻¹ :=
begin
  by_cases h : is_unit A.det,
  { induction n with n ih,
    { simp },
    { rw [pow_succ', pow_succ, ih, eq_comm],
      refine inv_eq_left_inv _,
      rw [mul_eq_mul, mul_eq_mul, matrix.mul_assoc, ←matrix.mul_assoc _ A,
          nonsing_inv_mul _ h, matrix.one_mul, nonsing_inv_mul],
      simpa using h.pow n } },
  { cases n,
    { simp },
    { rw [nonsing_inv_apply_not_is_unit _ h, nonsing_inv_apply_not_is_unit,
          zero_pow n.zero_lt_succ],
      simpa [det_pow, is_unit_pos_pow_iff n.zero_lt_succ] using h } }
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
  by_cases h : is_unit A.det,
  { rw [nonsing_inv_apply _ h, smul_pow, smul_mul, mul_smul, smul_left_cancel_iff,
        ←adjugate_pow],
    cases le_total m n with hm hm,
    { obtain ⟨k, rfl⟩ := le_iff_exists_add.mp hm,
      rw [pow_add, mul_eq_mul, ←matrix.mul_assoc, adjugate_mul, ←mul_eq_mul (A ^ m), ←pow_add,
          add_comm, pow_add, mul_eq_mul (A ^ k), matrix.mul_assoc, mul_adjugate, mul_smul, smul_mul,
          matrix.mul_one, matrix.one_mul] },
    { obtain ⟨k, rfl⟩ := le_iff_exists_add.mp hm,
      rw [pow_add, mul_eq_mul, adjugate_mul_distrib, matrix.mul_assoc, ←adjugate_mul_distrib,
          adjugate_mul, mul_smul, matrix.mul_one, ←mul_eq_mul _ (A ^ k), ←pow_add,
          add_comm, pow_add, mul_eq_mul (A ^ k), adjugate_mul_distrib, ←matrix.mul_assoc,
          mul_adjugate, smul_mul, matrix.one_mul] } },
  { rw [A.nonsing_inv_apply_not_is_unit h],
    cases m,
    { rw [pow_zero, matrix.mul_one, matrix.one_mul] },
    { rw [zero_pow (nat.zero_lt_succ m), matrix.mul_zero, matrix.zero_mul] } }
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

lemma fzero_pow_eq (n : ℤ) : (0 : M) ^ n = if n = 0 then 1 else 0 :=
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

lemma inv_fpow' {a : M} (h : is_unit a.det) (n : ℤ) :
  (a ⁻¹) ^ n = a ^ (-n) :=
begin
  induction n using int.induction_on with n IH n IH,
  { simp },
  { rw [←int.coe_nat_succ, fpow_coe_nat, fpow_neg_coe_nat, inv_pow'] },
  { rw [←neg_add', ←int.coe_nat_succ, neg_neg, fpow_coe_nat, fpow_neg_coe_nat, inv_pow',
        nonsing_inv_nonsing_inv],
    rw det_pow,
    exact h.pow _ }
end

theorem fpow_neg {A : M} (h : is_unit A.det) : ∀ (n : ℤ), A ^ -n = (A ^ n)⁻¹
| (n : ℕ) := fpow_neg_coe_nat _ _
| -[1+ n] := by { rw [gpow_neg_succ_of_nat, neg_neg_of_nat_succ, of_nat_eq_coe, fpow_coe_nat,
                      nonsing_inv_nonsing_inv],
                  rw det_pow,
                  exact h.pow _ }

lemma fpow_add_one {A : M} (h : is_unit A.det) : ∀ n : ℤ, A ^ (n + 1) = A ^ n * A
| (n : ℕ)    := by simp [← int.coe_nat_succ, pow_succ']
| -[1+0]     := by simp [int.neg_succ_of_nat_eq, fpow_neg_one, nonsing_inv_mul _ h]
| -[1+(n+1)] := by rw [int.neg_succ_of_nat_eq, fpow_neg h, neg_add, neg_add_cancel_right,
  fpow_neg h, ← int.coe_nat_succ, gpow_coe_nat, gpow_coe_nat, pow_succ _ (n + 1),
  mul_eq_mul A, mul_inv_rev, mul_eq_mul, matrix.mul_assoc,
  nonsing_inv_mul _ h, matrix.mul_one]

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

lemma fpow_add' {A : M} {m n : ℤ} (h : is_unit A.det ∨ (m < 0 ∧ n < 0 ∨ 0 ≤ m ∧ 0 ≤ n)) :
  A ^ (m + n) = A ^ m * A ^ n :=
begin
  by_cases ha : is_unit A.det,
  { exact fpow_add ha m n },
  { casesI is_empty_or_nonempty n' with H H,
    { ext i j,
      exact is_empty_elim i },
    nontriviality K,
    simp only [false_or, ha] at h,
    rcases h with (⟨hm', hn'⟩|⟨hm', hn'⟩),
    { obtain ⟨k, rfl⟩ := exists_eq_neg_of_nat hm'.le,
      obtain ⟨l, rfl⟩ := exists_eq_neg_of_nat hn'.le,
      simp only [right.neg_neg_iff, coe_nat_pos] at hm' hn',
      rw [←neg_add, ←int.coe_nat_add, fpow_neg_coe_nat, fpow_neg_coe_nat,
          nonsing_inv_apply_not_is_unit, nonsing_inv_apply_not_is_unit, zero_mul],
      { rwa [det_pow, is_unit_pos_pow_iff],
        simpa using hm' },
      { rwa [det_pow, is_unit_pos_pow_iff],
        rw ←zero_add 0,
        exact add_lt_add hm' hn' } },
    { obtain ⟨k, rfl⟩ := eq_coe_of_zero_le hm',
      obtain ⟨l, rfl⟩ := eq_coe_of_zero_le hn',
      rw [←int.coe_nat_add, fpow_coe_nat, fpow_coe_nat, fpow_coe_nat, pow_add] } }
end

lemma fpow_add'' {A : M} {m n : ℤ} (h : is_unit A.det ∨ (m ≤ 0 ∧ n ≤ 0 ∨ 0 < m ∧ 0 < n)) :
  A ^ (m + n) = A ^ m * A ^ n :=
begin
  by_cases ha : is_unit A.det,
  { exact fpow_add ha m n },
  { casesI is_empty_or_nonempty n' with H H,
    { ext i j,
      exact is_empty_elim i },
    nontriviality K,
    simp only [false_or, ha] at h,
    rcases h with (⟨hm', hn'⟩|⟨hm', hn'⟩),
    { rcases hm'.eq_or_lt with rfl|hk,
      { rw [zero_add, gpow_zero, one_mul] },
      rcases hn'.eq_or_lt with rfl|hl,
      { rw [add_zero, gpow_zero, mul_one] },
      obtain ⟨k, rfl⟩ := exists_eq_neg_of_nat hk.le,
      obtain ⟨l, rfl⟩ := exists_eq_neg_of_nat hl.le,
      simp only [right.neg_neg_iff, coe_nat_pos] at hk hl,
      rw [←neg_add, ←int.coe_nat_add, fpow_neg_coe_nat, fpow_neg_coe_nat,
          nonsing_inv_apply_not_is_unit, nonsing_inv_apply_not_is_unit, zero_mul],
      { rwa [det_pow, is_unit_pos_pow_iff],
        simpa using hk },
      { rwa [det_pow, is_unit_pos_pow_iff],
        rw ←zero_add 0,
        exact add_lt_add hk hl } },
    { obtain ⟨k, rfl⟩ := eq_coe_of_zero_le hm'.le,
      obtain ⟨l, rfl⟩ := eq_coe_of_zero_le hn'.le,
      rw [←int.coe_nat_add, fpow_coe_nat, fpow_coe_nat, fpow_coe_nat, pow_add] } }
end

theorem fpow_one_add {A : M} (h : is_unit A.det) (i : ℤ) : A ^ (1 + i) = A * A ^ i :=
by rw [fpow_add h, gpow_one]

theorem semiconj_by.fpow_right {a x y : M} (hx : is_unit x.det) (hy : is_unit y.det)
  (h : semiconj_by a x y) :
  ∀ m : ℤ, semiconj_by a (x^m) (y^m)
| (n : ℕ) := by simp [h.pow_right n]
| -[1+n]  := begin
  by_cases ha : a = 0,
  { simp only [ha, semiconj_by.zero_left] },
  have hx' : is_unit (x ^ n.succ).det,
  { rw det_pow,
    exact hx.pow n.succ },
  have hy' : is_unit (y ^ n.succ).det,
  { rw det_pow,
    exact hy.pow n.succ },
  rw [gpow_neg_succ_of_nat, gpow_neg_succ_of_nat, nonsing_inv_apply _ hx', nonsing_inv_apply _ hy',
      semiconj_by],
  refine (is_regular_of_is_left_regular_det hy'.is_regular.left).left _,
  rw [←mul_assoc, ←(h.pow_right n.succ).eq, mul_assoc, mul_eq_mul (x ^ _), mul_smul, mul_adjugate,
      mul_eq_mul, mul_eq_mul, mul_eq_mul, ←matrix.mul_assoc, mul_smul (y ^ _), mul_adjugate,
      units.smul_def, units.smul_def, smul_smul, smul_smul, hx'.coe_inv_mul, hy'.coe_inv_mul,
      one_smul, matrix.mul_one, matrix.one_mul],
  apply_instance -- TODO: why is this necessary?
end

theorem commute.fpow_right {a b : M} (h : commute a b) (m : ℤ) : commute a (b^m) :=
begin
  by_cases hb : is_unit b.det,
  { exact semiconj_by.fpow_right hb hb h _ },
  { cases m,
    { simpa using h.pow_right _ },
    { simp only [gpow_neg_succ_of_nat, ←inv_pow', nonsing_inv_apply_not_is_unit _ hb,
                 zero_pow (nat.zero_lt_succ m), commute.zero_right] } }
end

theorem commute.fpow_left {a b : M} (h : commute a b) (m : ℤ) : commute (a^m) b :=
(commute.fpow_right h.symm m).symm

theorem commute.fpow_fpow {a b : M} (h : commute a b) (m n : ℤ) : commute (a^m) (b^n) :=
commute.fpow_right (commute.fpow_left h _) _

theorem commute.fpow_self (a : M) (n : ℤ) : commute (a^n) a :=
commute.fpow_left (commute.refl a) _

theorem commute.self_fpow (a : M) (n : ℤ) : commute a (a^n) :=
commute.fpow_right (commute.refl a) _

theorem commute.fpow_fpow_self (a : M) (m n : ℤ) : commute (a^m) (a^n) :=
commute.fpow_fpow (commute.refl a) _ _

theorem fpow_bit0 (a : M) (n : ℤ) : a ^ bit0 n = a ^ n * a ^ n :=
begin
  apply fpow_add', right,
  by_cases hn : n = 0,
  { simp [hn] },
  { simpa [← two_mul, hn, two_ne_zero] using lt_or_le n 0 }
end

theorem fpow_bit1 (a : M) (n : ℤ) : a ^ bit1 n = a ^ n * a ^ n * a :=
begin
  induction n using int.induction_on with n IH n IH,
  { simp },
  { rw [←fpow_bit0, ←int.coe_nat_succ, ←linarith.int.coe_nat_bit0, ←linarith.int.coe_nat_bit1,
        fpow_coe_nat, fpow_coe_nat, pow_bit1, pow_bit0] },
  { have key : ∀ (i : ℤ), (-i + -1 + (-1 + 2)) = -i := by norm_num,
    have i0 : ∀ (i : ℤ), bit0 (-i) = - bit0 i,
    { intro i,
      simp [bit0] },
    have i1 : ∀ (i : ℤ), bit1 (-i) = - bit1 i + 2,
    { intro i,
      rw [bit1, bit1, neg_add, i0, add_assoc],
      norm_num },
    have i1' : ∀ (i : ℤ), bit1 (-(i + 1)) = - (bit1 i),
    { intro i,
      rw [i1, bit1, neg_add, bit0, neg_add, neg_add, add_assoc, add_assoc, key, add_right_comm,
          bit1, neg_add, bit0, neg_add] },
    rw [←neg_add', i1', bit1, neg_add, fpow_add'', ←int.coe_nat_succ, ←linarith.int.coe_nat_bit0,
        fpow_neg_coe_nat, fpow_neg_coe_nat, ←inv_pow', ←inv_pow', ←pow_bit0, fpow_neg_one],
    { by_cases h : is_unit a.det,
      { rw [nat.bit0_succ_eq, pow_succ', pow_succ', mul_assoc _ _ a, mul_eq_mul _ a,
            nonsing_inv_mul _ h, mul_one] },
      { rw [nonsing_inv_apply_not_is_unit _ h, mul_zero, zero_pow, zero_mul],
        simp } },
    { simp } }
end

theorem fpow_mul (a : M) (h : is_unit a.det) : ∀ m n : ℤ, a ^ (m * n) = (a ^ m) ^ n
| (m : ℕ) (n : ℕ) := by rw [gpow_coe_nat, gpow_coe_nat, ← pow_mul, ← gpow_coe_nat, int.coe_nat_mul]
| (m : ℕ) -[1+ n] := by rw [gpow_coe_nat, gpow_neg_succ_of_nat, ← pow_mul, coe_nat_mul_neg_succ,
    ←int.coe_nat_mul, fpow_neg_coe_nat]
| -[1+ m] (n : ℕ) := by rw [gpow_coe_nat, gpow_neg_succ_of_nat, ← inv_pow', ← pow_mul,
    neg_succ_mul_coe_nat, ←int.coe_nat_mul, fpow_neg_coe_nat, inv_pow']
| -[1+ m] -[1+ n] := by { rw [gpow_neg_succ_of_nat, gpow_neg_succ_of_nat, neg_succ_mul_neg_succ,
    ←int.coe_nat_mul, fpow_coe_nat, inv_pow', ←pow_mul, nonsing_inv_nonsing_inv],
    rw det_pow,
    exact h.pow _ }

theorem fpow_mul' (a : M) (h : is_unit a.det) (m n : ℤ) : a ^ (m * n) = (a ^ n) ^ m :=
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

lemma fpow_ne_zero_of_is_unit_det [nonempty n'] [nontrivial K] {a : M}
  (ha : is_unit a.det) (z : ℤ) : a ^ z ≠ 0 :=
begin
  have := ha.det_fpow z,
  contrapose! this,
  rw [this, det_zero ‹_›],
  exact not_is_unit_zero
end

lemma fpow_sub {a : M} (ha : is_unit a.det) (z1 z2 : ℤ) : a ^ (z1 - z2) = a ^ z1 / a ^ z2 :=
by rw [sub_eq_add_neg, fpow_add ha, fpow_neg ha, div_eq_mul_inv]

lemma commute.mul_fpow {a b : M} (h : commute a b) :
  ∀ (i : ℤ), (a * b) ^ i = (a ^ i) * (b ^ i)
| (n : ℕ) := by simp [h.mul_pow n, -mul_eq_mul]
| -[1+n]  := by rw [gpow_neg_succ_of_nat, gpow_neg_succ_of_nat, gpow_neg_succ_of_nat,
                    mul_eq_mul (_⁻¹), ←mul_inv_rev, ←mul_eq_mul, h.mul_pow n.succ,
                    (h.pow_pow _ _).eq]

theorem fpow_bit0' (a : M) (n : ℤ) : a ^ bit0 n = (a * a) ^ n :=
(fpow_bit0 a n).trans (commute.mul_fpow (commute.refl a) n).symm

theorem fpow_bit1' (a : M) (n : ℤ) : a ^ bit1 n = (a * a) ^ n * a :=
by rw [fpow_bit1, commute.mul_fpow (commute.refl a)]

theorem fpow_neg_mul_fpow_self (n : ℤ) {A : M} (h : is_unit A.det) :
  A ^ (-n) * A ^ n = 1 :=
by rw [fpow_neg h, mul_eq_mul, nonsing_inv_mul _ (h.det_fpow _)]

theorem one_div_pow {a : M} (n : ℕ) :
  (1 / a) ^ n = 1 / a ^ n :=
by simp only [one_div, inv_pow']

theorem one_div_fpow {a : M} (n : ℤ) :
  (1 / a) ^ n = 1 / a ^ n :=
by simp only [one_div, inv_fpow]

end int_pow

end matrix
