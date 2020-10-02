/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import algebra.group_power.basic
import algebra.opposites
import data.list.basic
import data.int.cast
import data.equiv.basic
import deprecated.group

/-!
# Lemmas about power operations on monoids and groups

This file contains lemmas about `monoid.pow`, `group.pow`, `nsmul`, `gsmul`
which require additional imports besides those available in `.basic`.
-/

universes u v w x y z u₁ u₂

variables {M : Type u} {N : Type v} {G : Type w} {H : Type x} {A : Type y} {B : Type z}
  {R : Type u₁} {S : Type u₂}

/-!
### (Additive) monoid
-/
section monoid
variables [monoid M] [monoid N] [add_monoid A] [add_monoid B]

@[simp] theorem nsmul_one [has_one A] : ∀ n : ℕ, n •ℕ (1 : A) = n :=
add_monoid_hom.eq_nat_cast
  ⟨λ n, n •ℕ (1 : A), zero_nsmul _, λ _ _, add_nsmul _ _ _⟩
  (one_nsmul _)

@[simp, priority 500]
theorem list.prod_repeat (a : M) (n : ℕ) : (list.repeat a n).prod = a ^ n :=
begin
  induction n with n ih,
  { refl },
  { rw [list.repeat_succ, list.prod_cons, ih], refl, }
end

@[simp, priority 500]
theorem list.sum_repeat : ∀ (a : A) (n : ℕ), (list.repeat a n).sum = n •ℕ a :=
@list.prod_repeat (multiplicative A) _

@[simp, norm_cast] lemma units.coe_pow (u : units M) (n : ℕ) : ((u ^ n : units M) : M) = u ^ n :=
(units.coe_hom M).map_pow u n

lemma is_unit_of_pow_eq_one (x : M) (n : ℕ) (hx : x ^ n = 1) (hn : 0 < n) :
  is_unit x :=
begin
  cases n, { exact (nat.not_lt_zero _ hn).elim },
  refine ⟨⟨x, x ^ n, _, _⟩, rfl⟩,
  { rwa [pow_succ] at hx },
  { rwa [pow_succ'] at hx }
end

end monoid

theorem nat.nsmul_eq_mul (m n : ℕ) : m •ℕ n = m * n :=
by induction m with m ih; [rw [zero_nsmul, zero_mul],
  rw [succ_nsmul', ih, nat.succ_mul]]

section group
variables [group G] [group H] [add_group A] [add_group B]

open int

local attribute [ematch] le_of_lt
open nat

theorem gsmul_one [has_one A] (n : ℤ) : n •ℤ (1 : A) = n :=
by cases n; simp

lemma gpow_add_one (a : G) : ∀ n : ℤ, a ^ (n + 1) = a ^ n * a
| (of_nat n) := by simp [← int.coe_nat_succ, pow_succ']
| -[1+0]     := by simp [int.neg_succ_of_nat_eq]
| -[1+(n+1)] := by rw [int.neg_succ_of_nat_eq, gpow_neg, neg_add, neg_add_cancel_right, gpow_neg,
  ← int.coe_nat_succ, gpow_coe_nat, gpow_coe_nat, pow_succ _ (n + 1), mul_inv_rev,
  inv_mul_cancel_right]

theorem add_one_gsmul : ∀ (a : A) (i : ℤ), (i + 1) •ℤ a = i •ℤ a + a :=
@gpow_add_one (multiplicative A) _

lemma gpow_sub_one (a : G) (n : ℤ) : a ^ (n - 1) = a ^ n * a⁻¹ :=
calc a ^ (n - 1) = a ^ (n - 1) * a * a⁻¹ : (mul_inv_cancel_right _ _).symm
             ... = a^n * a⁻¹             : by rw [← gpow_add_one, sub_add_cancel]

lemma gpow_add (a : G) (m n : ℤ) : a ^ (m + n) = a ^ m * a ^ n :=
begin
  induction n using int.induction_on with n ihn n ihn,
  case hz : { simp },
  { simp only [← add_assoc, gpow_add_one, ihn, mul_assoc] },
  { rw [gpow_sub_one, ← mul_assoc, ← ihn, ← gpow_sub_one, add_sub_assoc] }
end

lemma mul_self_gpow (b : G) (m : ℤ) : b*b^m = b^(m+1) :=
by { conv_lhs {congr, rw ← gpow_one b }, rw [← gpow_add, add_comm] }

lemma mul_gpow_self (b : G) (m : ℤ) : b^m*b = b^(m+1) :=
by { conv_lhs {congr, skip, rw ← gpow_one b }, rw [← gpow_add, add_comm] }

theorem add_gsmul : ∀ (a : A) (i j : ℤ), (i + j) •ℤ a = i •ℤ a + j •ℤ a :=
@gpow_add (multiplicative A) _

lemma gpow_sub (a : G) (m n : ℤ) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ :=
by rw [sub_eq_add_neg, gpow_add, gpow_neg]

lemma sub_gsmul (m n : ℤ) (a : A) : (m - n) •ℤ a = m •ℤ a - n •ℤ a :=
@gpow_sub (multiplicative A) _ _ _ _

theorem gpow_one_add (a : G) (i : ℤ) : a ^ (1 + i) = a * a ^ i :=
by rw [gpow_add, gpow_one]

theorem one_add_gsmul : ∀ (a : A) (i : ℤ), (1 + i) •ℤ a = a + i •ℤ a :=
@gpow_one_add (multiplicative A) _

theorem gpow_mul_comm (a : G) (i j : ℤ) : a ^ i * a ^ j = a ^ j * a ^ i :=
by rw [← gpow_add, ← gpow_add, add_comm]

theorem gsmul_add_comm : ∀ (a : A) (i j), i •ℤ a + j •ℤ a = j •ℤ a + i •ℤ a :=
@gpow_mul_comm (multiplicative A) _

theorem gpow_mul (a : G) (m n : ℤ) : a ^ (m * n) = (a ^ m) ^ n :=
int.induction_on n (by simp) (λ n ihn, by simp [mul_add, gpow_add, ihn])
  (λ n ihn, by simp only [mul_sub, gpow_sub, ihn, mul_one, gpow_one])

theorem gsmul_mul' : ∀ (a : A) (m n : ℤ), m * n •ℤ a = n •ℤ (m •ℤ a) :=
@gpow_mul (multiplicative A) _

theorem gpow_mul' (a : G) (m n : ℤ) : a ^ (m * n) = (a ^ n) ^ m :=
by rw [mul_comm, gpow_mul]

theorem gsmul_mul (a : A) (m n : ℤ) : m * n •ℤ a = m •ℤ (n •ℤ a) :=
by rw [mul_comm, gsmul_mul']

theorem gpow_bit0 (a : G) (n : ℤ) : a ^ bit0 n = a ^ n * a ^ n := gpow_add _ _ _

theorem bit0_gsmul (a : A) (n : ℤ) : bit0 n •ℤ a = n •ℤ a + n •ℤ a := gpow_add _ _ _

theorem gpow_bit1 (a : G) (n : ℤ) : a ^ bit1 n = a ^ n * a ^ n * a :=
by rw [bit1, gpow_add]; simp [gpow_bit0]

theorem bit1_gsmul : ∀ (a : A) (n : ℤ), bit1 n •ℤ a = n •ℤ a + n •ℤ a + a :=
@gpow_bit1 (multiplicative A) _

theorem monoid_hom.map_gpow (f : G →* H) (a : G) (n : ℤ) : f (a ^ n) = f a ^ n :=
by cases n; [exact f.map_pow _ _, exact (f.map_inv _).trans (congr_arg _ $ f.map_pow _ _)]

theorem add_monoid_hom.map_gsmul (f : A →+ B) (a : A) (n : ℤ) : f (n •ℤ a) = n •ℤ f a :=
f.to_multiplicative.map_gpow a n

@[simp, norm_cast] lemma units.coe_gpow (u : units G) (n : ℤ) : ((u ^ n : units G) : G) = u ^ n :=
(units.coe_hom G).map_gpow u n

end group

section ordered_add_comm_group

variables [ordered_add_comm_group A]
/-! Lemmas about `gsmul` under ordering,  placed here (rather than in `algebra.group_power.basic`
with their friends) because they require facts from `data.int.basic`-/
open int

lemma gsmul_pos {a : A} (ha : 0 < a) {k : ℤ} (hk : (0:ℤ) < k) : 0 < k •ℤ a :=
begin
  lift k to ℕ using int.le_of_lt hk,
  apply nsmul_pos ha,
  exact coe_nat_pos.mp hk,
end

theorem gsmul_le_gsmul {a : A} {n m : ℤ} (ha : 0 ≤ a) (h : n ≤ m) : n •ℤ a ≤ m •ℤ a :=
calc n •ℤ a = n •ℤ a + 0 : (add_zero _).symm
  ... ≤ n •ℤ a + (m - n) •ℤ a : add_le_add_left (gsmul_nonneg ha (sub_nonneg.mpr h)) _
  ... = m •ℤ a : by { rw [← add_gsmul], simp }

theorem gsmul_lt_gsmul {a : A} {n m : ℤ} (ha : 0 < a) (h : n < m) : n •ℤ a < m •ℤ a :=
calc n •ℤ a = n •ℤ a + 0 : (add_zero _).symm
  ... < n •ℤ a + (m - n) •ℤ a : add_lt_add_left (gsmul_pos ha (sub_pos.mpr h)) _
  ... = m •ℤ a : by { rw [← add_gsmul], simp }

end ordered_add_comm_group

section decidable_linear_ordered_add_comm_group
variable [decidable_linear_ordered_add_comm_group A]

theorem gsmul_le_gsmul_iff {a : A} {n m : ℤ} (ha : 0 < a) : n •ℤ a ≤ m •ℤ a ↔ n ≤ m :=
begin
  refine ⟨λ h, _, gsmul_le_gsmul $ le_of_lt ha⟩,
  by_contra H,
  exact lt_irrefl _ (lt_of_lt_of_le (gsmul_lt_gsmul ha (not_le.mp H)) h)
end

theorem gsmul_lt_gsmul_iff {a : A} {n m : ℤ} (ha : 0 < a) : n •ℤ a < m •ℤ a ↔ n < m :=
begin
  refine ⟨λ h, _, gsmul_lt_gsmul ha⟩,
  by_contra H,
  exact lt_irrefl _ (lt_of_le_of_lt (gsmul_le_gsmul (le_of_lt ha) $ not_lt.mp H) h)
end

theorem nsmul_le_nsmul_iff {a : A} {n m : ℕ} (ha : 0 < a) : n •ℕ a ≤ m •ℕ a ↔ n ≤ m :=
begin
  refine ⟨λ h, _, nsmul_le_nsmul $ le_of_lt ha⟩,
  by_contra H,
  exact lt_irrefl _ (lt_of_lt_of_le (nsmul_lt_nsmul ha (not_le.mp H)) h)
end

theorem nsmul_lt_nsmul_iff {a : A} {n m : ℕ} (ha : 0 < a) : n •ℕ a < m •ℕ a ↔ n < m :=
begin
  refine ⟨λ h, _, nsmul_lt_nsmul ha⟩,
  by_contra H,
  exact lt_irrefl _ (lt_of_le_of_lt (nsmul_le_nsmul (le_of_lt ha) $ not_lt.mp H) h)
end

end decidable_linear_ordered_add_comm_group

@[simp] lemma with_bot.coe_nsmul [add_monoid A] (a : A) (n : ℕ) :
  ((nsmul n a : A) : with_bot A) = nsmul n a :=
add_monoid_hom.map_nsmul ⟨(coe : A → with_bot A), with_bot.coe_zero, with_bot.coe_add⟩ a n

theorem nsmul_eq_mul' [semiring R] (a : R) (n : ℕ) : n •ℕ a = a * n :=
by induction n with n ih; [rw [zero_nsmul, nat.cast_zero, mul_zero],
  rw [succ_nsmul', ih, nat.cast_succ, mul_add, mul_one]]

@[simp] theorem nsmul_eq_mul [semiring R] (n : ℕ) (a : R) : n •ℕ a = n * a :=
by rw [nsmul_eq_mul', (n.cast_commute a).eq]

theorem mul_nsmul_left [semiring R] (a b : R) (n : ℕ) : n •ℕ (a * b) = a * (n •ℕ b) :=
by rw [nsmul_eq_mul', nsmul_eq_mul', mul_assoc]

theorem mul_nsmul_assoc [semiring R] (a b : R) (n : ℕ) : n •ℕ (a * b) = n •ℕ a * b :=
by rw [nsmul_eq_mul, nsmul_eq_mul, mul_assoc]

@[simp, norm_cast] theorem nat.cast_pow [semiring R] (n m : ℕ) : (↑(n ^ m) : R) = ↑n ^ m :=
by induction m with m ih; [exact nat.cast_one, rw [pow_succ', pow_succ', nat.cast_mul, ih]]

@[simp, norm_cast] theorem int.coe_nat_pow (n m : ℕ) : ((n ^ m : ℕ) : ℤ) = n ^ m :=
by induction m with m ih; [exact int.coe_nat_one, rw [pow_succ', pow_succ', int.coe_nat_mul, ih]]

theorem int.nat_abs_pow (n : ℤ) (k : ℕ) : int.nat_abs (n ^ k) = (int.nat_abs n) ^ k :=
by induction k with k ih; [refl, rw [pow_succ', int.nat_abs_mul, pow_succ', ih]]

-- The next four lemmas allow us to replace multiplication by a numeral with a `gsmul` expression.
-- They are used by the `noncomm_ring` tactic, to normalise expressions before passing to `abel`.

lemma bit0_mul [ring R] {n r : R} : bit0 n * r = gsmul 2 (n * r) :=
by { dsimp [bit0], rw [add_mul, add_gsmul, one_gsmul], }

lemma mul_bit0 [ring R] {n r : R} : r * bit0 n = gsmul 2 (r * n) :=
by { dsimp [bit0], rw [mul_add, add_gsmul, one_gsmul], }

lemma bit1_mul [ring R] {n r : R} : bit1 n * r = gsmul 2 (n * r) + r :=
by { dsimp [bit1], rw [add_mul, bit0_mul, one_mul], }

lemma mul_bit1 [ring R] {n r : R} : r * bit1 n = gsmul 2 (r * n) + r :=
by { dsimp [bit1], rw [mul_add, mul_bit0, mul_one], }

@[simp] theorem gsmul_eq_mul [ring R] (a : R) : ∀ n, n •ℤ a = n * a
| (n : ℕ) := nsmul_eq_mul _ _
| -[1+ n] := show -(_ •ℕ _)=-_*_, by rw [neg_mul_eq_neg_mul_symm, nsmul_eq_mul, nat.cast_succ]

theorem gsmul_eq_mul' [ring R] (a : R) (n : ℤ) : n •ℤ a = a * n :=
by rw [gsmul_eq_mul, (n.cast_commute a).eq]

theorem mul_gsmul_left [ring R] (a b : R) (n : ℤ) : n •ℤ (a * b) = a * (n •ℤ b) :=
by rw [gsmul_eq_mul', gsmul_eq_mul', mul_assoc]

theorem mul_gsmul_assoc [ring R] (a b : R) (n : ℤ) : n •ℤ (a * b) = n •ℤ a * b :=
by rw [gsmul_eq_mul, gsmul_eq_mul, mul_assoc]

@[simp]
lemma gsmul_int_int (a b : ℤ) : a •ℤ b = a * b := by simp [gsmul_eq_mul]

lemma gsmul_int_one (n : ℤ) : n •ℤ 1 = n := by simp

@[simp, norm_cast] theorem int.cast_pow [ring R] (n : ℤ) (m : ℕ) : (↑(n ^ m) : R) = ↑n ^ m :=
by induction m with m ih; [exact int.cast_one,
  rw [pow_succ, pow_succ, int.cast_mul, ih]]

lemma neg_one_pow_eq_pow_mod_two [ring R] {n : ℕ} : (-1 : R) ^ n = (-1) ^ (n % 2) :=
by rw [← nat.mod_add_div n 2, pow_add, pow_mul]; simp [pow_two]

section linear_ordered_semiring
variable [linear_ordered_semiring R]

/-- Bernoulli's inequality. This version works for semirings but requires
an additional hypothesis `0 ≤ a * a`. -/
theorem one_add_mul_le_pow' {a : R} (Hsqr : 0 ≤ a * a) (H : 0 ≤ 1 + a) :
  ∀ (n : ℕ), 1 + n •ℕ a ≤ (1 + a) ^ n
| 0     := le_of_eq $ add_zero _
| (n+1) :=
calc 1 + (n + 1) •ℕ a ≤ (1 + a) * (1 + n •ℕ a) :
  by simpa [succ_nsmul, mul_add, add_mul, mul_nsmul_left, add_comm, add_left_comm]
    using nsmul_nonneg Hsqr n
... ≤ (1 + a)^(n+1) : mul_le_mul_of_nonneg_left (one_add_mul_le_pow' n) H

private lemma pow_lt_pow_of_lt_one_aux {a : R} (h : 0 < a) (ha : a < 1) (i : ℕ) :
  ∀ k : ℕ, a ^ (i + k + 1) < a ^ i
| 0 :=
  begin
    simp only [add_zero],
    rw ←one_mul (a^i), exact mul_lt_mul ha (le_refl _) (pow_pos h _) zero_le_one
  end
| (k+1) :=
  begin
    rw ←one_mul (a^i),
    apply mul_lt_mul ha _ _ zero_le_one,
    { apply le_of_lt, apply pow_lt_pow_of_lt_one_aux },
    { show 0 < a ^ (i + (k + 1) + 0), apply pow_pos h }
  end

private lemma pow_le_pow_of_le_one_aux {a : R}  (h : 0 ≤ a) (ha : a ≤ 1) (i : ℕ) :
  ∀ k : ℕ, a ^ (i + k) ≤ a ^ i
| 0 := by simp
| (k+1) := by rw [←add_assoc, ←one_mul (a^i)];
              exact mul_le_mul ha (pow_le_pow_of_le_one_aux _) (pow_nonneg h _) zero_le_one

lemma pow_lt_pow_of_lt_one  {a : R} (h : 0 < a) (ha : a < 1)
  {i j : ℕ} (hij : i < j) : a ^ j < a ^ i :=
let ⟨k, hk⟩ := nat.exists_eq_add_of_lt hij in
by rw hk; exact pow_lt_pow_of_lt_one_aux h ha _ _

lemma pow_le_pow_of_le_one  {a : R} (h : 0 ≤ a) (ha : a ≤ 1)
  {i j : ℕ} (hij : i ≤ j) : a ^ j ≤ a ^ i :=
let ⟨k, hk⟩ := nat.exists_eq_add_of_le hij in
by rw hk; exact pow_le_pow_of_le_one_aux h ha _ _

lemma pow_le_one {x : R} : ∀ (n : ℕ) (h0 : 0 ≤ x) (h1 : x ≤ 1), x ^ n ≤ 1
| 0     h0 h1 := le_refl (1 : R)
| (n+1) h0 h1 := mul_le_one h1 (pow_nonneg h0 _) (pow_le_one n h0 h1)

end linear_ordered_semiring

/-- Bernoulli's inequality for `n : ℕ`, `-2 ≤ a`. -/
theorem one_add_mul_le_pow [linear_ordered_ring R] {a : R} (H : -2 ≤ a) :
  ∀ (n : ℕ), 1 + n •ℕ a ≤ (1 + a) ^ n
| 0     := le_of_eq $ add_zero _
| 1     := by simp
| (n+2) :=
have H' : 0 ≤ 2 + a,
  from neg_le_iff_add_nonneg.1 H,
have 0 ≤ n •ℕ (a * a * (2 + a)) + a * a,
  from add_nonneg (nsmul_nonneg (mul_nonneg (mul_self_nonneg a) H') n)
    (mul_self_nonneg a),
calc 1 + (n + 2) •ℕ a ≤ 1 + (n + 2) •ℕ a + (n •ℕ (a * a * (2 + a)) + a * a) :
  (le_add_iff_nonneg_right _).2 this
... = (1 + a) * (1 + a) * (1 + n •ℕ a) :
  by { simp only [add_mul, mul_add, mul_two, mul_one, one_mul, succ_nsmul, nsmul_add,
         mul_nsmul_assoc, (mul_nsmul_left _ _ _).symm],
       ac_refl }
... ≤ (1 + a) * (1 + a) * (1 + a)^n :
  mul_le_mul_of_nonneg_left (one_add_mul_le_pow n) (mul_self_nonneg (1 + a))
... = (1 + a)^(n + 2) : by simp only [pow_succ, mul_assoc]

/-- Bernoulli's inequality reformulated to estimate `a^n`. -/
theorem one_add_sub_mul_le_pow [linear_ordered_ring R]
  {a : R} (H : -1 ≤ a) (n : ℕ) : 1 + n •ℕ (a - 1) ≤ a ^ n :=
have -2 ≤ a - 1, by { rw [bit0, neg_add], exact sub_le_sub_right H 1 },
by simpa only [add_sub_cancel'_right] using one_add_mul_le_pow this n

namespace int

lemma units_pow_two (u : units ℤ) : u ^ 2 = 1 :=
(units_eq_one_or u).elim (λ h, h.symm ▸ rfl) (λ h, h.symm ▸ rfl)

lemma units_pow_eq_pow_mod_two (u : units ℤ) (n : ℕ) : u ^ n = u ^ (n % 2) :=
by conv {to_lhs, rw ← nat.mod_add_div n 2}; rw [pow_add, pow_mul, units_pow_two, one_pow, mul_one]

@[simp] lemma nat_abs_pow_two (x : ℤ) : (x.nat_abs ^ 2 : ℤ) = x ^ 2 :=
by rw [pow_two, int.nat_abs_mul_self', pow_two]

end int

variables (M G A)

/-- Monoid homomorphisms from `multiplicative ℕ` are defined by the image
of `multiplicative.of_add 1`. -/
def powers_hom [monoid M] : M ≃ (multiplicative ℕ →* M) :=
{ to_fun := λ x, ⟨λ n, x ^ n.to_add, pow_zero x, λ m n, pow_add x m n⟩,
  inv_fun := λ f, f (multiplicative.of_add 1),
  left_inv := pow_one,
  right_inv := λ f, monoid_hom.ext $ λ n, by { simp [← f.map_pow, ← of_add_nsmul] } }

/-- Monoid homomorphisms from `multiplicative ℤ` are defined by the image
of `multiplicative.of_add 1`. -/
def gpowers_hom [group G] : G ≃ (multiplicative ℤ →* G) :=
{ to_fun := λ x, ⟨λ n, x ^ n.to_add, gpow_zero x, λ m n, gpow_add x m n⟩,
  inv_fun := λ f, f (multiplicative.of_add 1),
  left_inv := gpow_one,
  right_inv := λ f, monoid_hom.ext $ λ n, by { simp [← f.map_gpow, ← of_add_gsmul ] } }

/-- Additive homomorphisms from `ℕ` are defined by the image of `1`. -/
def multiples_hom [add_monoid A] : A ≃ (ℕ →+ A) :=
{ to_fun := λ x, ⟨λ n, n •ℕ x, zero_nsmul x, λ m n, add_nsmul _ _ _⟩,
  inv_fun := λ f, f 1,
  left_inv := one_nsmul,
  right_inv := λ f, add_monoid_hom.ext_nat $ one_nsmul (f 1) }

/-- Additive homomorphisms from `ℤ` are defined by the image of `1`. -/
def gmultiples_hom [add_group A] : A ≃ (ℤ →+ A) :=
{ to_fun := λ x, ⟨λ n, n •ℤ x, zero_gsmul x, λ m n, add_gsmul _ _ _⟩,
  inv_fun := λ f, f 1,
  left_inv := one_gsmul,
  right_inv := λ f, add_monoid_hom.ext_int $ one_gsmul (f 1) }

variables {M G A}

@[simp] lemma powers_hom_apply [monoid M] (x : M) (n : multiplicative ℕ) :
  powers_hom M x n = x ^ n.to_add := rfl

@[simp] lemma powers_hom_symm_apply [monoid M] (f : multiplicative ℕ →* M) :
  (powers_hom M).symm f = f (multiplicative.of_add 1) := rfl

lemma mnat_monoid_hom_eq [monoid M] (f : multiplicative ℕ →* M) (n : multiplicative ℕ) :
  f n = (f (multiplicative.of_add 1)) ^ n.to_add :=
by rw [← powers_hom_symm_apply, ← powers_hom_apply, equiv.apply_symm_apply]

lemma mnat_monoid_hom_ext [monoid M] ⦃f g : multiplicative ℕ →* M⦄
  (h : f (multiplicative.of_add 1) = g (multiplicative.of_add 1)) : f = g :=
monoid_hom.ext $ λ n, by rw [mnat_monoid_hom_eq f, mnat_monoid_hom_eq g, h]

/-!
### Commutativity (again)

Facts about `semiconj_by` and `commute` that require `gpow` or `gsmul`, or the fact that integer
multiplication equals semiring multiplication.
-/

namespace semiconj_by

section

variables [semiring R] {a x y : R}

@[simp] lemma cast_nat_mul_right (h : semiconj_by a x y) (n : ℕ) : semiconj_by a ((n : R) * x) (n * y) :=
semiconj_by.mul_right (nat.commute_cast _ _) h

@[simp] lemma cast_nat_mul_left (h : semiconj_by a x y) (n : ℕ) : semiconj_by ((n : R) * a) x y :=
semiconj_by.mul_left (nat.cast_commute _ _) h

@[simp] lemma cast_nat_mul_cast_nat_mul (h : semiconj_by a x y) (m n : ℕ) :
  semiconj_by ((m : R) * a) (n * x) (n * y) :=
(h.cast_nat_mul_left m).cast_nat_mul_right n

end

variables [monoid M] [group G] [ring R]

@[simp] lemma units_gpow_right {a : M} {x y : units M} (h : semiconj_by a x y) :
  ∀ m : ℤ, semiconj_by a (↑(x^m)) (↑(y^m))
| (n : ℕ) := by simp only [gpow_coe_nat, units.coe_pow, h, pow_right]
| -[1+n] := by simp only [gpow_neg_succ_of_nat, units.coe_pow, units_inv_right, h, pow_right]

variables {a b x y x' y' : R}

@[simp] lemma cast_int_mul_right (h : semiconj_by a x y) (m : ℤ) :
  semiconj_by a ((m : ℤ) * x) (m * y) :=
semiconj_by.mul_right (int.commute_cast _ _) h

@[simp] lemma cast_int_mul_left (h : semiconj_by a x y) (m : ℤ) : semiconj_by ((m : R) * a) x y :=
semiconj_by.mul_left (int.cast_commute _ _) h

@[simp] lemma cast_int_mul_cast_int_mul (h : semiconj_by a x y) (m n : ℤ) :
  semiconj_by ((m : R) * a) (n * x) (n * y) :=
(h.cast_int_mul_left m).cast_int_mul_right n

end semiconj_by

namespace commute

section

variables [semiring R] {a b : R}

@[simp] theorem cast_nat_mul_right (h : commute a b) (n : ℕ) : commute a ((n : R) * b) :=
h.cast_nat_mul_right n

@[simp] theorem cast_nat_mul_left (h : commute a b) (n : ℕ) : commute ((n : R) * a) b :=
h.cast_nat_mul_left n

@[simp] theorem cast_nat_mul_cast_nat_mul (h : commute a b) (m n : ℕ) :
  commute ((m : R) * a) (n * b) :=
h.cast_nat_mul_cast_nat_mul m n

@[simp] theorem self_cast_nat_mul (n : ℕ) : commute a (n * a) :=
(commute.refl a).cast_nat_mul_right n

@[simp] theorem cast_nat_mul_self (n : ℕ) : commute ((n : R) * a) a :=
(commute.refl a).cast_nat_mul_left n

@[simp] theorem self_cast_nat_mul_cast_nat_mul (m n : ℕ) : commute ((m : R) * a) (n * a) :=
(commute.refl a).cast_nat_mul_cast_nat_mul m n

end

variables [monoid M] [group G] [ring R]

@[simp] lemma units_gpow_right {a : M} {u : units M} (h : commute a u) (m : ℤ) :
  commute a (↑(u^m)) :=
h.units_gpow_right m

@[simp] lemma units_gpow_left {u : units M} {a : M} (h : commute ↑u a) (m : ℤ) :
  commute (↑(u^m)) a :=
(h.symm.units_gpow_right m).symm

variables {a b : R}

@[simp] lemma cast_int_mul_right (h : commute a b) (m : ℤ) : commute a (m * b) :=
h.cast_int_mul_right m

@[simp] lemma cast_int_mul_left (h : commute a b) (m : ℤ) : commute ((m : R) * a) b :=
h.cast_int_mul_left m

lemma cast_int_mul_cast_int_mul (h : commute a b) (m n : ℤ) : commute ((m : R) * a) (n * b) :=
h.cast_int_mul_cast_int_mul m n

variables (a) (m n : ℤ)

@[simp] theorem self_cast_int_mul : commute a (n * a) := (commute.refl a).cast_int_mul_right n

@[simp] theorem cast_int_mul_self : commute ((n : R) * a) a := (commute.refl a).cast_int_mul_left n

theorem self_cast_int_mul_cast_int_mul : commute ((m : R) * a) (n * a) :=
(commute.refl a).cast_int_mul_cast_int_mul m n

end commute

section multiplicative

open multiplicative

@[simp] lemma nat.to_add_pow (a : multiplicative ℕ) (b : ℕ) : to_add (a ^ b) = to_add a * b :=
begin
  induction b with b ih,
  { erw [pow_zero, to_add_one, mul_zero] },
  { simp [*, pow_succ, add_comm, nat.mul_succ] }
end

@[simp] lemma nat.of_add_mul (a b : ℕ) : of_add (a * b) = of_add a ^ b :=
(nat.to_add_pow _ _).symm

@[simp] lemma int.to_add_pow (a : multiplicative ℤ) (b : ℕ) : to_add (a ^ b) = to_add a * b :=
by induction b; simp [*, mul_add, pow_succ, add_comm]

@[simp] lemma int.to_add_gpow (a : multiplicative ℤ) (b : ℤ) : to_add (a ^ b) = to_add a * b :=
int.induction_on b (by simp)
  (by simp [gpow_add, mul_add] {contextual := tt})
  (by simp [gpow_add, mul_add, sub_eq_add_neg] {contextual := tt})

@[simp] lemma int.of_add_mul (a b : ℤ) : of_add (a * b) = of_add a ^ b :=
(int.to_add_gpow _ _).symm

end multiplicative

namespace units

variables [monoid M]

lemma conj_pow (u : units M) (x : M) (n : ℕ) : (↑u * x * ↑(u⁻¹))^n = u * x^n * ↑(u⁻¹) :=
(divp_eq_iff_mul_eq.2 ((u.mk_semiconj_by x).pow_right n).eq.symm).symm

lemma conj_pow' (u : units M) (x : M) (n : ℕ) : (↑(u⁻¹) * x * u)^n = ↑(u⁻¹) * x^n * u:=
(u⁻¹).conj_pow x n

open opposite

/-- Moving to the opposite monoid commutes with taking powers. -/
@[simp] lemma op_pow (x : M) (n : ℕ) : op (x ^ n) = (op x) ^ n :=
begin
  induction n with n h,
  { simp },
  { rw [pow_succ', op_mul, h, pow_succ] }
end

@[simp] lemma unop_pow (x : Mᵒᵖ) (n : ℕ) : unop (x ^ n) = (unop x) ^ n :=
begin
  induction n with n h,
  { simp },
  { rw [pow_succ', unop_mul, h, pow_succ] }
end

end units
