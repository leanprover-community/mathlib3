/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import algebra.invertible
import data.int.cast

/-!
# Lemmas about power operations on monoids and groups

This file contains lemmas about `monoid.pow`, `group.pow`, `nsmul`, `zsmul`
which require additional imports besides those available in `algebra.group_power.basic`.
-/

open function int nat

universes u v w x y z u₁ u₂

variables {α : Type*} {M : Type u} {N : Type v} {G : Type w} {H : Type x} {A : Type y} {B : Type z}
  {R : Type u₁} {S : Type u₂}

/-!
### (Additive) monoid
-/
section monoid
variables [monoid M] [monoid N] [add_monoid A] [add_monoid B]

@[simp] theorem nsmul_one [has_one A] : ∀ n : ℕ, n • (1 : A) = n :=
begin
  refine eq_nat_cast' (⟨_, _, _⟩ : ℕ →+ A) _,
  { simp [zero_nsmul] },
  { simp [add_nsmul] },
  { simp }
end

instance invertible_pow (m : M) [invertible m] (n : ℕ) : invertible (m ^ n) :=
{ inv_of := ⅟ m ^ n,
  inv_of_mul_self := by rw [← (commute_inv_of m).symm.mul_pow, inv_of_mul_self, one_pow],
  mul_inv_of_self := by rw [← (commute_inv_of m).mul_pow, mul_inv_of_self, one_pow] }

lemma inv_of_pow (m : M) [invertible m] (n : ℕ) [invertible (m ^ n)] :
  ⅟(m ^ n) = ⅟m ^ n :=
@invertible_unique M _ (m ^ n) (m ^ n) _ (invertible_pow m n) rfl

lemma is_unit.pow {m : M} (n : ℕ) : is_unit m → is_unit (m ^ n) :=
λ ⟨u, hu⟩, ⟨u ^ n, by simp *⟩

@[simp] lemma is_unit_pow_succ_iff {m : M} {n : ℕ} :
  is_unit (m ^ (n + 1)) ↔ is_unit m :=
begin
  refine ⟨_, λ h, h.pow _⟩,
  rw [pow_succ, ((commute.refl _).pow_right _).is_unit_mul_iff],
  exact and.left
end

lemma is_unit_pos_pow_iff {m : M} :
  ∀ {n : ℕ} (h : 0 < n), is_unit (m ^ n) ↔ is_unit m
| (n + 1) _ := is_unit_pow_succ_iff

/-- If `x ^ n.succ = 1` then `x` has an inverse, `x^n`. -/
def invertible_of_pow_succ_eq_one (x : M) (n : ℕ) (hx : x ^ n.succ = 1) :
  invertible x :=
⟨x ^ n, (pow_succ' x n).symm.trans hx, (pow_succ x n).symm.trans hx⟩

/-- If `x ^ n = 1` then `x` has an inverse, `x^(n - 1)`. -/
def invertible_of_pow_eq_one (x : M) (n : ℕ) (hx : x ^ n = 1) (hn : 0 < n) :
  invertible x :=
begin
  apply invertible_of_pow_succ_eq_one x (n - 1),
  convert hx,
  exact tsub_add_cancel_of_le (nat.succ_le_of_lt hn),
end

lemma is_unit_of_pow_eq_one (x : M) (n : ℕ) (hx : x ^ n = 1) (hn : 0 < n) :
  is_unit x :=
begin
  haveI := invertible_of_pow_eq_one x n hx hn,
  exact is_unit_of_invertible x
end

lemma smul_pow [mul_action M N] [is_scalar_tower M N N] [smul_comm_class M N N]
  (k : M) (x : N) (p : ℕ) :
  (k • x) ^ p = k ^ p • x ^ p :=
begin
  induction p with p IH,
  { simp },
  { rw [pow_succ', IH, smul_mul_smul, ←pow_succ', ←pow_succ'] }
end

@[simp] lemma smul_pow' [mul_distrib_mul_action M N] (x : M) (m : N) (n : ℕ) :
  x • m ^ n = (x • m) ^ n :=
begin
  induction n with n ih,
  { rw [pow_zero, pow_zero], exact smul_one x },
  { rw [pow_succ, pow_succ], exact (smul_mul' x m (m ^ n)).trans (congr_arg _ ih) }
end

end monoid

section sub_neg_monoid
variables [sub_neg_monoid A]

lemma zsmul_one [has_one A] (n : ℤ) : n • (1 : A) = n := by cases n; simp

end sub_neg_monoid

section division_monoid
variables [division_monoid α]

-- Note that `mul_zsmul` and `zpow_mul` have the primes swapped since their argument order,
-- and therefore the more "natural" choice of lemma, is reversed.
@[to_additive mul_zsmul'] lemma zpow_mul (a : α) : ∀ m n : ℤ, a ^ (m * n) = (a ^ m) ^ n
| (m : ℕ) (n : ℕ) := by { rw [zpow_coe_nat, zpow_coe_nat, ← pow_mul, ← zpow_coe_nat], refl }
| (m : ℕ) -[1+ n] := by { rw [zpow_coe_nat, zpow_neg_succ_of_nat, ← pow_mul, coe_nat_mul_neg_succ,
    zpow_neg, inv_inj, ← zpow_coe_nat], refl }
| -[1+ m] (n : ℕ) := by { rw [zpow_coe_nat, zpow_neg_succ_of_nat, ← inv_pow, ← pow_mul,
    neg_succ_mul_coe_nat, zpow_neg, inv_pow, inv_inj, ← zpow_coe_nat], refl }
| -[1+ m] -[1+ n] := by { rw [zpow_neg_succ_of_nat, zpow_neg_succ_of_nat, neg_succ_mul_neg_succ,
    inv_pow, inv_inv, ← pow_mul, ← zpow_coe_nat], refl }

@[to_additive mul_zsmul] lemma zpow_mul' (a : α) (m n : ℤ) : a ^ (m * n) = (a ^ n) ^ m :=
by rw [mul_comm, zpow_mul]

@[to_additive bit0_zsmul] lemma zpow_bit0 (a : α) : ∀ n : ℤ, a ^ bit0 n = a ^ n * a ^ n
| (n : ℕ) := by simp only [zpow_coe_nat, ←int.coe_nat_bit0, pow_bit0]
| -[1+n]  := by { simp [←mul_inv_rev, ←pow_bit0], rw [neg_succ_of_nat_eq, bit0_neg, zpow_neg],
  norm_cast }

@[to_additive bit0_zsmul'] lemma zpow_bit0' (a : α) (n : ℤ) : a ^ bit0 n = (a * a) ^ n :=
(zpow_bit0 a n).trans ((commute.refl a).mul_zpow n).symm

@[simp] lemma zpow_bit0_neg [has_distrib_neg α] (x : α) (n : ℤ) : (-x) ^ (bit0 n) = x ^ bit0 n :=
by rw [zpow_bit0', zpow_bit0', neg_mul_neg]

end division_monoid

section group
variables [group G]

@[to_additive add_one_zsmul]
lemma zpow_add_one (a : G) : ∀ n : ℤ, a ^ (n + 1) = a ^ n * a
| (of_nat n) := by simp [← int.coe_nat_succ, pow_succ']
| -[1+n] := by rw [int.neg_succ_of_nat_eq, zpow_neg, neg_add, neg_add_cancel_right, zpow_neg,
  ← int.coe_nat_succ, zpow_coe_nat, zpow_coe_nat, pow_succ _ n, mul_inv_rev,
  inv_mul_cancel_right]

@[to_additive zsmul_sub_one]
lemma zpow_sub_one (a : G) (n : ℤ) : a ^ (n - 1) = a ^ n * a⁻¹ :=
calc a ^ (n - 1) = a ^ (n - 1) * a * a⁻¹ : (mul_inv_cancel_right _ _).symm
             ... = a^n * a⁻¹             : by rw [← zpow_add_one, sub_add_cancel]

@[to_additive add_zsmul]
lemma zpow_add (a : G) (m n : ℤ) : a ^ (m + n) = a ^ m * a ^ n :=
begin
  induction n using int.induction_on with n ihn n ihn,
  case hz : { simp },
  { simp only [← add_assoc, zpow_add_one, ihn, mul_assoc] },
  { rw [zpow_sub_one, ← mul_assoc, ← ihn, ← zpow_sub_one, add_sub_assoc] }
end

@[to_additive add_zsmul_self]
lemma mul_self_zpow (b : G) (m : ℤ) : b*b^m = b^(m+1) :=
by { conv_lhs {congr, rw ← zpow_one b }, rw [← zpow_add, add_comm] }

@[to_additive add_self_zsmul]
lemma mul_zpow_self (b : G) (m : ℤ) : b^m*b = b^(m+1) :=
by { conv_lhs {congr, skip, rw ← zpow_one b }, rw [← zpow_add, add_comm] }

@[to_additive sub_zsmul]
lemma zpow_sub (a : G) (m n : ℤ) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ :=
by rw [sub_eq_add_neg, zpow_add, zpow_neg]

@[to_additive one_add_zsmul]
theorem zpow_one_add (a : G) (i : ℤ) : a ^ (1 + i) = a * a ^ i :=
by rw [zpow_add, zpow_one]

@[to_additive] lemma zpow_mul_comm (a : G) (i j : ℤ) : a ^ i * a ^ j = a ^ j * a ^ i :=
(commute.refl _).zpow_zpow _ _

@[to_additive bit1_zsmul]
theorem zpow_bit1 (a : G) (n : ℤ) : a ^ bit1 n = a ^ n * a ^ n * a :=
by rw [bit1, zpow_add, zpow_bit0, zpow_one]

end group

/-!
### `zpow`/`zsmul` and an order

Those lemmas are placed here (rather than in `algebra.group_power.order` with their friends) because
they require facts from `data.int.basic`.
-/

section ordered_add_comm_group
variables [ordered_comm_group α] {m n : ℤ} {a b : α}

@[to_additive zsmul_pos]
lemma one_lt_zpow' (ha : 1 < a) {k : ℤ} (hk : (0:ℤ) < k) : 1 < a^k :=
begin
  lift k to ℕ using int.le_of_lt hk,
  rw zpow_coe_nat,
  exact one_lt_pow' ha (coe_nat_pos.mp hk).ne',
end

@[to_additive zsmul_strict_mono_left]
lemma zpow_strict_mono_right (ha : 1 < a) : strict_mono (λ n : ℤ, a ^ n) :=
λ m n h,
  calc a ^ m = a ^ m * 1 : (mul_one _).symm
    ... < a ^ m * a ^ (n - m) : mul_lt_mul_left' (one_lt_zpow' ha $ sub_pos_of_lt h) _
    ... = a ^ n : by { rw ←zpow_add, simp }

@[to_additive zsmul_mono_left]
lemma zpow_mono_right (ha : 1 ≤ a) : monotone (λ n : ℤ, a ^ n) :=
λ m n h,
  calc a ^ m = a ^ m * 1 : (mul_one _).symm
    ... ≤ a ^ m * a ^ (n - m) : mul_le_mul_left' (one_le_zpow ha $ sub_nonneg_of_le h) _
    ... = a ^ n : by { rw ←zpow_add, simp }

@[to_additive]
lemma zpow_le_zpow (ha : 1 ≤ a) (h : m ≤ n) : a ^ m ≤ a ^ n := zpow_mono_right ha h

@[to_additive]
lemma zpow_lt_zpow (ha : 1 < a) (h : m < n) : a ^ m < a ^ n := zpow_strict_mono_right ha h

@[to_additive]
lemma zpow_le_zpow_iff (ha : 1 < a) : a ^ m ≤ a ^ n ↔ m ≤ n := (zpow_strict_mono_right ha).le_iff_le

@[to_additive]
lemma zpow_lt_zpow_iff (ha : 1 < a) : a ^ m < a ^ n ↔ m < n := (zpow_strict_mono_right ha).lt_iff_lt

variables (α)

@[to_additive zsmul_strict_mono_right]
lemma zpow_strict_mono_left (hn : 0 < n) : strict_mono ((^ n) : α → α) :=
λ a b hab, by { rw [←one_lt_div', ←div_zpow], exact one_lt_zpow' (one_lt_div'.2 hab) hn }

@[to_additive zsmul_mono_right]
lemma zpow_mono_left (hn : 0 ≤ n) : monotone ((^ n) : α → α) :=
λ a b hab, by { rw [←one_le_div', ←div_zpow], exact one_le_zpow (one_le_div'.2 hab) hn }

variables {α}

@[to_additive]
lemma zpow_le_zpow' (hn : 0 ≤ n) (h : a ≤ b) : a ^ n ≤ b ^ n := zpow_mono_left α hn h

@[to_additive]
lemma zpow_lt_zpow' (hn : 0 < n) (h : a < b) : a ^ n < b ^ n := zpow_strict_mono_left α hn h

end ordered_add_comm_group

section linear_ordered_comm_group
variables [linear_ordered_comm_group α] {n : ℤ} {a b : α}

@[to_additive]
lemma zpow_le_zpow_iff' (hn : 0 < n) {a b : α} : a ^ n ≤ b ^ n ↔ a ≤ b :=
(zpow_strict_mono_left α hn).le_iff_le

@[to_additive]
lemma zpow_lt_zpow_iff' (hn : 0 < n) {a b : α} : a ^ n < b ^ n ↔ a < b :=
(zpow_strict_mono_left α hn).lt_iff_lt

@[nolint to_additive_doc, to_additive zsmul_right_injective
"See also `smul_right_injective`. TODO: provide a `no_zero_smul_divisors` instance. We can't do that
here because importing that definition would create import cycles."]
lemma zpow_left_injective (hn : n ≠ 0) : function.injective ((^ n) : α → α) :=
begin
  cases hn.symm.lt_or_lt,
  { exact (zpow_strict_mono_left α h).injective },
  { refine λ a b (hab : a ^ n = b ^ n), (zpow_strict_mono_left α (neg_pos.mpr h)).injective _,
    rw [zpow_neg, zpow_neg, hab] }
end

@[to_additive zsmul_right_inj]
lemma zpow_left_inj (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b := (zpow_left_injective hn).eq_iff

/-- Alias of `zsmul_right_inj`, for ease of discovery alongside `zsmul_le_zsmul_iff'` and
`zsmul_lt_zsmul_iff'`. -/
@[to_additive "Alias of `zsmul_right_inj`, for ease of discovery alongside `zsmul_le_zsmul_iff'` and
`zsmul_lt_zsmul_iff'`."]
lemma zpow_eq_zpow_iff' (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b := zpow_left_inj hn

end linear_ordered_comm_group

section linear_ordered_add_comm_group
variables [linear_ordered_add_comm_group α] {a b : α}

lemma abs_nsmul (n : ℕ) (a : α) : |n • a| = n • |a| :=
begin
  cases le_total a 0 with hneg hpos,
  { rw [abs_of_nonpos hneg, ← abs_neg, ← neg_nsmul, abs_of_nonneg],
    exact nsmul_nonneg (neg_nonneg.mpr hneg) n },
  { rw [abs_of_nonneg hpos, abs_of_nonneg],
    exact nsmul_nonneg hpos n }
end

lemma abs_zsmul (n : ℤ) (a : α) : |n • a| = |n| • |a| :=
begin
  obtain n0 | n0 := le_total 0 n,
  { lift n to ℕ using n0,
    simp only [abs_nsmul, coe_nat_abs, coe_nat_zsmul] },
  { lift (- n) to ℕ using neg_nonneg.2 n0 with m h,
    rw [← abs_neg (n • a), ← neg_zsmul, ← abs_neg n, ← h, coe_nat_zsmul, coe_nat_abs,
      coe_nat_zsmul],
    exact abs_nsmul m _ },
end

lemma abs_add_eq_add_abs_le (hle : a ≤ b) : |a + b| = |a| + |b| ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 :=
begin
  obtain a0 | a0 := le_or_lt 0 a; obtain b0 | b0 := le_or_lt 0 b,
  { simp [a0, b0, abs_of_nonneg, add_nonneg a0 b0] },
  { exact (lt_irrefl (0 : α) $ a0.trans_lt $ hle.trans_lt b0).elim },
  any_goals { simp [a0.le, b0.le, abs_of_nonpos, add_nonpos, add_comm] },
  have : (|a + b| = -a + b ↔ b ≤ 0) ↔ (|a + b| =
    |a| + |b| ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0),
  { simp [a0, a0.le, a0.not_le, b0, abs_of_neg, abs_of_nonneg] },
  refine this.mp ⟨λ h, _, λ h, by simp only [le_antisymm h b0, abs_of_neg a0, add_zero]⟩,
  obtain ab | ab := le_or_lt (a + b) 0,
  { refine le_of_eq (eq_zero_of_neg_eq _),
    rwa [abs_of_nonpos ab, neg_add_rev, add_comm, add_right_inj] at h },
  { refine (lt_irrefl (0 : α) _).elim,
    rw [abs_of_pos ab, add_left_inj] at h,
    rwa eq_zero_of_neg_eq h.symm at a0 }
end

lemma abs_add_eq_add_abs_iff (a b : α) : |a + b| = |a| + |b| ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 :=
begin
  obtain ab | ab := le_total a b,
  { exact abs_add_eq_add_abs_le ab },
  { rw [add_comm a, add_comm (abs _), abs_add_eq_add_abs_le ab, and.comm, @and.comm (b ≤ 0)] }
end

end linear_ordered_add_comm_group

@[simp] lemma with_bot.coe_nsmul [add_monoid A] (a : A) (n : ℕ) :
  ((n • a : A) : with_bot A) = n • a :=
add_monoid_hom.map_nsmul ⟨(coe : A → with_bot A), with_bot.coe_zero, with_bot.coe_add⟩ a n

theorem nsmul_eq_mul' [non_assoc_semiring R] (a : R) (n : ℕ) : n • a = a * n :=
by induction n with n ih; [rw [zero_nsmul, nat.cast_zero, mul_zero],
  rw [succ_nsmul', ih, nat.cast_succ, mul_add, mul_one]]

@[simp] theorem nsmul_eq_mul [non_assoc_semiring R] (n : ℕ) (a : R) : n • a = n * a :=
by rw [nsmul_eq_mul', (n.cast_commute a).eq]

/-- Note that `add_comm_monoid.nat_smul_comm_class` requires stronger assumptions on `R`. -/
instance non_unital_non_assoc_semiring.nat_smul_comm_class [non_unital_non_assoc_semiring R] :
  smul_comm_class ℕ R R :=
⟨λ n x y, match n with
  | 0 := by simp_rw [zero_nsmul, smul_eq_mul, mul_zero]
  | (n + 1) := by simp_rw [succ_nsmul, smul_eq_mul, mul_add, ←smul_eq_mul, _match n]
  end⟩

/-- Note that `add_comm_monoid.nat_is_scalar_tower` requires stronger assumptions on `R`. -/
instance non_unital_non_assoc_semiring.nat_is_scalar_tower [non_unital_non_assoc_semiring R] :
  is_scalar_tower ℕ R R :=
⟨λ n x y, match n with
  | 0 := by simp_rw [zero_nsmul, smul_eq_mul, zero_mul]
  | (n + 1) := by simp_rw [succ_nsmul, ←_match n, smul_eq_mul, add_mul]
  end⟩

@[simp, norm_cast] theorem nat.cast_pow [semiring R] (n m : ℕ) : (↑(n ^ m) : R) = ↑n ^ m :=
begin
  induction m with m ih,
  { rw [pow_zero, pow_zero], exact nat.cast_one },
  { rw [pow_succ', pow_succ', nat.cast_mul, ih] }
end

@[simp, norm_cast] theorem int.coe_nat_pow (n m : ℕ) : ((n ^ m : ℕ) : ℤ) = n ^ m :=
by induction m with m ih; [exact int.coe_nat_one, rw [pow_succ', pow_succ', int.coe_nat_mul, ih]]

theorem int.nat_abs_pow (n : ℤ) (k : ℕ) : int.nat_abs (n ^ k) = (int.nat_abs n) ^ k :=
by induction k with k ih; [refl, rw [pow_succ', int.nat_abs_mul, pow_succ', ih]]

-- The next four lemmas allow us to replace multiplication by a numeral with a `zsmul` expression.
-- They are used by the `noncomm_ring` tactic, to normalise expressions before passing to `abel`.

lemma bit0_mul [non_unital_non_assoc_ring R] {n r : R} : bit0 n * r = (2 : ℤ) • (n * r) :=
by { dsimp [bit0], rw [add_mul, add_zsmul, one_zsmul], }

lemma mul_bit0 [non_unital_non_assoc_ring R] {n r : R} : r * bit0 n = (2 : ℤ) • (r * n) :=
by { dsimp [bit0], rw [mul_add, add_zsmul, one_zsmul], }

lemma bit1_mul [non_assoc_ring R] {n r : R} : bit1 n * r = (2 : ℤ) • (n * r) + r :=
by { dsimp [bit1], rw [add_mul, bit0_mul, one_mul], }

lemma mul_bit1 [non_assoc_ring R] {n r : R} : r * bit1 n = (2 : ℤ) • (r * n) + r :=
by { dsimp [bit1], rw [mul_add, mul_bit0, mul_one], }

@[simp] theorem zsmul_eq_mul [non_assoc_ring R] (a : R) : ∀ (n : ℤ), n • a = n * a
| (n : ℕ) := by { rw [coe_nat_zsmul, nsmul_eq_mul], refl }
| -[1+ n] := by simp [nat.cast_succ, neg_add_rev, int.cast_neg_succ_of_nat, add_mul]

theorem zsmul_eq_mul' [ring R] (a : R) (n : ℤ) : n • a = a * n :=
by rw [zsmul_eq_mul, (n.cast_commute a).eq]

/-- Note that `add_comm_group.int_smul_comm_class` requires stronger assumptions on `R`. -/
instance non_unital_non_assoc_ring.int_smul_comm_class [non_unital_non_assoc_ring R] :
  smul_comm_class ℤ R R :=
⟨λ n x y, match n with
  | (n : ℕ) := by simp_rw [coe_nat_zsmul, smul_comm]
  | -[1+n]  := by simp_rw [zsmul_neg_succ_of_nat, smul_eq_mul, mul_neg, mul_smul_comm]
  end⟩

/-- Note that `add_comm_group.int_is_scalar_tower` requires stronger assumptions on `R`. -/
instance non_unital_non_assoc_ring.int_is_scalar_tower [non_unital_non_assoc_ring R] :
  is_scalar_tower ℤ R R :=
⟨λ n x y, match n with
  | (n : ℕ) := by simp_rw [coe_nat_zsmul, smul_assoc]
  | -[1+n]  := by simp_rw [zsmul_neg_succ_of_nat, smul_eq_mul, neg_mul, smul_mul_assoc]
  end⟩

lemma zsmul_int_int (a b : ℤ) : a • b = a * b := by simp

lemma zsmul_int_one (n : ℤ) : n • 1 = n := by simp

@[simp, norm_cast] theorem int.cast_pow [ring R] (n : ℤ) (m : ℕ) : (↑(n ^ m) : R) = ↑n ^ m :=
begin
  induction m with m ih,
  { rw [pow_zero, pow_zero, int.cast_one] },
  { rw [pow_succ, pow_succ, int.cast_mul, ih] }
end

lemma neg_one_pow_eq_pow_mod_two [ring R] {n : ℕ} : (-1 : R) ^ n = (-1) ^ (n % 2) :=
by rw [← nat.mod_add_div n 2, pow_add, pow_mul]; simp [sq]

section ordered_semiring
variables [ordered_semiring R] {a : R}

/-- Bernoulli's inequality. This version works for semirings but requires
additional hypotheses `0 ≤ a * a` and `0 ≤ (1 + a) * (1 + a)`. -/
theorem one_add_mul_le_pow' (Hsq : 0 ≤ a * a) (Hsq' : 0 ≤ (1 + a) * (1 + a))
  (H : 0 ≤ 2 + a) :
  ∀ (n : ℕ), 1 + (n : R) * a ≤ (1 + a) ^ n
| 0     := by simp
| 1     := by simp
| (n+2) :=
have 0 ≤ (n : R) * (a * a * (2 + a)) + a * a,
  from add_nonneg (mul_nonneg n.cast_nonneg (mul_nonneg Hsq H)) Hsq,
calc 1 + (↑(n + 2) : R) * a ≤ 1 + ↑(n + 2) * a + (n * (a * a * (2 + a)) + a * a) :
  (le_add_iff_nonneg_right _).2 this
... = (1 + a) * (1 + a) * (1 + n * a) :
  by { simp [add_mul, mul_add, bit0, mul_assoc, (n.cast_commute (_ : R)).left_comm],
       ac_refl }
... ≤ (1 + a) * (1 + a) * (1 + a)^n :
  mul_le_mul_of_nonneg_left (one_add_mul_le_pow' n) Hsq'
... = (1 + a)^(n + 2) : by simp only [pow_succ, mul_assoc]

private lemma pow_le_pow_of_le_one_aux (h : 0 ≤ a) (ha : a ≤ 1) (i : ℕ) :
  ∀ k : ℕ, a ^ (i + k) ≤ a ^ i
| 0 := by simp
| (k+1) := by { rw [←add_assoc, ←one_mul (a^i), pow_succ],
                exact mul_le_mul ha (pow_le_pow_of_le_one_aux _) (pow_nonneg h _) zero_le_one }

lemma pow_le_pow_of_le_one (h : 0 ≤ a) (ha : a ≤ 1) {i j : ℕ} (hij : i ≤ j) :
  a ^ j ≤ a ^ i :=
let ⟨k, hk⟩ := nat.exists_eq_add_of_le hij in
by rw hk; exact pow_le_pow_of_le_one_aux h ha _ _

lemma pow_le_of_le_one (h₀ : 0 ≤ a) (h₁ : a ≤ 1) {n : ℕ} (hn : n ≠ 0) : a ^ n ≤ a :=
(pow_one a).subst (pow_le_pow_of_le_one h₀ h₁ (nat.pos_of_ne_zero hn))

lemma sq_le (h₀ : 0 ≤ a) (h₁ : a ≤ 1) : a ^ 2 ≤ a := pow_le_of_le_one h₀ h₁ two_ne_zero

end ordered_semiring

section linear_ordered_semiring

variables [linear_ordered_semiring R]

lemma sign_cases_of_C_mul_pow_nonneg {C r : R} (h : ∀ n : ℕ, 0 ≤ C * r ^ n) :
  C = 0 ∨ (0 < C ∧ 0 ≤ r) :=
begin
  have : 0 ≤ C, by simpa only [pow_zero, mul_one] using h 0,
  refine this.eq_or_lt.elim (λ h, or.inl h.symm) (λ hC, or.inr ⟨hC, _⟩),
  refine nonneg_of_mul_nonneg_left _ hC,
  simpa only [pow_one] using h 1
end

end linear_ordered_semiring

section linear_ordered_ring

variables [linear_ordered_ring R] {a : R} {n : ℕ}

@[simp] lemma abs_pow (a : R) (n : ℕ) : |a ^ n| = |a| ^ n :=
(pow_abs a n).symm

@[simp] theorem pow_bit1_neg_iff : a ^ bit1 n < 0 ↔ a < 0 :=
⟨λ h, not_le.1 $ λ h', not_le.2 h $ pow_nonneg h' _, λ ha, pow_bit1_neg ha n⟩

@[simp] theorem pow_bit1_nonneg_iff : 0 ≤ a ^ bit1 n ↔ 0 ≤ a :=
le_iff_le_iff_lt_iff_lt.2 pow_bit1_neg_iff

@[simp] theorem pow_bit1_nonpos_iff : a ^ bit1 n ≤ 0 ↔ a ≤ 0 :=
by simp only [le_iff_lt_or_eq, pow_bit1_neg_iff, pow_eq_zero_iff (bit1_pos (zero_le n))]

@[simp] theorem pow_bit1_pos_iff : 0 < a ^ bit1 n ↔ 0 < a :=
lt_iff_lt_of_le_iff_le pow_bit1_nonpos_iff

lemma strict_mono_pow_bit1 (n : ℕ) : strict_mono (λ a : R, a ^ bit1 n) :=
begin
  intros a b hab,
  cases le_total a 0 with ha ha,
  { cases le_or_lt b 0 with hb hb,
    { rw [← neg_lt_neg_iff, ← neg_pow_bit1, ← neg_pow_bit1],
      exact pow_lt_pow_of_lt_left (neg_lt_neg hab) (neg_nonneg.2 hb) (bit1_pos (zero_le n)) },
    { exact (pow_bit1_nonpos_iff.2 ha).trans_lt (pow_bit1_pos_iff.2 hb) } },
  { exact pow_lt_pow_of_lt_left hab ha (bit1_pos (zero_le n)) }
end

/-- Bernoulli's inequality for `n : ℕ`, `-2 ≤ a`. -/
theorem one_add_mul_le_pow (H : -2 ≤ a) (n : ℕ) : 1 + (n : R) * a ≤ (1 + a) ^ n :=
one_add_mul_le_pow' (mul_self_nonneg _) (mul_self_nonneg _) (neg_le_iff_add_nonneg'.1 H) _

/-- Bernoulli's inequality reformulated to estimate `a^n`. -/
theorem one_add_mul_sub_le_pow (H : -1 ≤ a) (n : ℕ) : 1 + (n : R) * (a - 1) ≤ a ^ n :=
have -2 ≤ a - 1, by rwa [bit0, neg_add, ← sub_eq_add_neg, sub_le_sub_iff_right],
by simpa only [add_sub_cancel'_right] using one_add_mul_le_pow this n

end linear_ordered_ring

/-- Bernoulli's inequality reformulated to estimate `(n : K)`. -/
theorem nat.cast_le_pow_sub_div_sub {K : Type*} [linear_ordered_field K] {a : K} (H : 1 < a)
  (n : ℕ) :
  (n : K) ≤ (a ^ n - 1) / (a - 1) :=
(le_div_iff (sub_pos.2 H)).2 $ le_sub_left_of_add_le $
  one_add_mul_sub_le_pow ((neg_le_self $ @zero_le_one K _).trans H.le) _

/-- For any `a > 1` and a natural `n` we have `n ≤ a ^ n / (a - 1)`. See also
`nat.cast_le_pow_sub_div_sub` for a stronger inequality with `a ^ n - 1` in the numerator. -/
theorem nat.cast_le_pow_div_sub {K : Type*} [linear_ordered_field K] {a : K} (H : 1 < a) (n : ℕ) :
  (n : K) ≤ a ^ n / (a - 1) :=
(n.cast_le_pow_sub_div_sub H).trans $ div_le_div_of_le (sub_nonneg.2 H.le)
  (sub_le_self _ zero_le_one)

namespace int

alias int.units_sq ← int.units_pow_two

lemma units_pow_eq_pow_mod_two (u : ℤˣ) (n : ℕ) : u ^ n = u ^ (n % 2) :=
by conv {to_lhs, rw ← nat.mod_add_div n 2}; rw [pow_add, pow_mul, units_sq, one_pow, mul_one]

@[simp] lemma nat_abs_sq (x : ℤ) : (x.nat_abs ^ 2 : ℤ) = x ^ 2 :=
by rw [sq, int.nat_abs_mul_self', sq]

alias int.nat_abs_sq ← int.nat_abs_pow_two

lemma abs_le_self_sq (a : ℤ) : (int.nat_abs a : ℤ) ≤ a ^ 2 :=
by { rw [← int.nat_abs_sq a, sq], norm_cast, apply nat.le_mul_self }

alias int.abs_le_self_sq ← int.abs_le_self_pow_two

lemma le_self_sq (b : ℤ) : b ≤ b ^ 2 := le_trans (le_nat_abs) (abs_le_self_sq _)

alias int.le_self_sq ← int.le_self_pow_two

lemma pow_right_injective {x : ℤ} (h : 1 < x.nat_abs) : function.injective ((^) x : ℕ → ℤ) :=
begin
  suffices : function.injective (nat_abs ∘ ((^) x : ℕ → ℤ)),
  { exact function.injective.of_comp this },
  convert nat.pow_right_injective h,
  ext n,
  rw [function.comp_app, nat_abs_pow]
end

end int

variables (M G A)

/-- Monoid homomorphisms from `multiplicative ℕ` are defined by the image
of `multiplicative.of_add 1`. -/
def powers_hom [monoid M] : M ≃ (multiplicative ℕ →* M) :=
{ to_fun := λ x, ⟨λ n, x ^ n.to_add, by { convert pow_zero x, exact to_add_one },
    λ m n, pow_add x m n⟩,
  inv_fun := λ f, f (multiplicative.of_add 1),
  left_inv := pow_one,
  right_inv := λ f, monoid_hom.ext $ λ n, by { simp [← f.map_pow, ← of_add_nsmul] } }

/-- Monoid homomorphisms from `multiplicative ℤ` are defined by the image
of `multiplicative.of_add 1`. -/
def zpowers_hom [group G] : G ≃ (multiplicative ℤ →* G) :=
{ to_fun := λ x, ⟨λ n, x ^ n.to_add, zpow_zero x, λ m n, zpow_add x m n⟩,
  inv_fun := λ f, f (multiplicative.of_add 1),
  left_inv := zpow_one,
  right_inv := λ f, monoid_hom.ext $ λ n, by { simp [← f.map_zpow, ← of_add_zsmul ] } }

/-- Additive homomorphisms from `ℕ` are defined by the image of `1`. -/
def multiples_hom [add_monoid A] : A ≃ (ℕ →+ A) :=
{ to_fun := λ x, ⟨λ n, n • x, zero_nsmul x, λ m n, add_nsmul _ _ _⟩,
  inv_fun := λ f, f 1,
  left_inv := one_nsmul,
  right_inv := λ f, add_monoid_hom.ext_nat $ one_nsmul (f 1) }

/-- Additive homomorphisms from `ℤ` are defined by the image of `1`. -/
def zmultiples_hom [add_group A] : A ≃ (ℤ →+ A) :=
{ to_fun := λ x, ⟨λ n, n • x, zero_zsmul x, λ m n, add_zsmul _ _ _⟩,
  inv_fun := λ f, f 1,
  left_inv := one_zsmul,
  right_inv := λ f, add_monoid_hom.ext_int $ one_zsmul (f 1) }

attribute [to_additive multiples_hom] powers_hom
attribute [to_additive zmultiples_hom] zpowers_hom

variables {M G A}

@[simp] lemma powers_hom_apply [monoid M] (x : M) (n : multiplicative ℕ) :
  powers_hom M x n = x ^ n.to_add := rfl

@[simp] lemma powers_hom_symm_apply [monoid M] (f : multiplicative ℕ →* M) :
  (powers_hom M).symm f = f (multiplicative.of_add 1) := rfl

@[simp] lemma zpowers_hom_apply [group G] (x : G) (n : multiplicative ℤ) :
  zpowers_hom G x n = x ^ n.to_add := rfl

@[simp] lemma zpowers_hom_symm_apply [group G] (f : multiplicative ℤ →* G) :
  (zpowers_hom G).symm f = f (multiplicative.of_add 1) := rfl

@[simp] lemma multiples_hom_apply [add_monoid A] (x : A) (n : ℕ) :
  multiples_hom A x n = n • x := rfl

attribute [to_additive multiples_hom_apply] powers_hom_apply

@[simp] lemma multiples_hom_symm_apply [add_monoid A] (f : ℕ →+ A) :
  (multiples_hom A).symm f = f 1 := rfl

attribute [to_additive multiples_hom_symm_apply] powers_hom_symm_apply

@[simp] lemma zmultiples_hom_apply [add_group A] (x : A) (n : ℤ) :
  zmultiples_hom A x n = n • x := rfl

attribute [to_additive zmultiples_hom_apply] zpowers_hom_apply

@[simp] lemma zmultiples_hom_symm_apply [add_group A] (f : ℤ →+ A) :
  (zmultiples_hom A).symm f = f 1 := rfl

attribute [to_additive zmultiples_hom_symm_apply] zpowers_hom_symm_apply

-- TODO use to_additive in the rest of this file

lemma monoid_hom.apply_mnat [monoid M] (f : multiplicative ℕ →* M) (n : multiplicative ℕ) :
  f n = (f (multiplicative.of_add 1)) ^ n.to_add :=
by rw [← powers_hom_symm_apply, ← powers_hom_apply, equiv.apply_symm_apply]

@[ext] lemma monoid_hom.ext_mnat [monoid M] ⦃f g : multiplicative ℕ →* M⦄
  (h : f (multiplicative.of_add 1) = g (multiplicative.of_add 1)) : f = g :=
monoid_hom.ext $ λ n, by rw [f.apply_mnat, g.apply_mnat, h]

lemma monoid_hom.apply_mint [group M] (f : multiplicative ℤ →* M) (n : multiplicative ℤ) :
  f n = (f (multiplicative.of_add 1)) ^ n.to_add :=
by rw [← zpowers_hom_symm_apply, ← zpowers_hom_apply, equiv.apply_symm_apply]

/-! `monoid_hom.ext_mint` is defined in `data.int.cast` -/

lemma add_monoid_hom.apply_nat [add_monoid M] (f : ℕ →+ M) (n : ℕ) :
  f n = n • (f 1) :=
by rw [← multiples_hom_symm_apply, ← multiples_hom_apply, equiv.apply_symm_apply]

/-! `add_monoid_hom.ext_nat` is defined in `data.nat.cast` -/

lemma add_monoid_hom.apply_int [add_group M] (f : ℤ →+ M) (n : ℤ) :
  f n = n • (f 1) :=
by rw [← zmultiples_hom_symm_apply, ← zmultiples_hom_apply, equiv.apply_symm_apply]

/-! `add_monoid_hom.ext_int` is defined in `data.int.cast` -/

variables (M G A)

/-- If `M` is commutative, `powers_hom` is a multiplicative equivalence. -/
def powers_mul_hom [comm_monoid M] : M ≃* (multiplicative ℕ →* M) :=
{ map_mul' := λ a b, monoid_hom.ext $ by simp [mul_pow],
  ..powers_hom M}

/-- If `M` is commutative, `zpowers_hom` is a multiplicative equivalence. -/
def zpowers_mul_hom [comm_group G] : G ≃* (multiplicative ℤ →* G) :=
{ map_mul' := λ a b, monoid_hom.ext $ by simp [mul_zpow],
  ..zpowers_hom G}

/-- If `M` is commutative, `multiples_hom` is an additive equivalence. -/
def multiples_add_hom [add_comm_monoid A] : A ≃+ (ℕ →+ A) :=
{ map_add' := λ a b, add_monoid_hom.ext $ by simp [nsmul_add],
  ..multiples_hom A}

/-- If `M` is commutative, `zmultiples_hom` is an additive equivalence. -/
def zmultiples_add_hom [add_comm_group A] : A ≃+ (ℤ →+ A) :=
{ map_add' := λ a b, add_monoid_hom.ext $ by simp [zsmul_add],
  ..zmultiples_hom A}

variables {M G A}

@[simp] lemma powers_mul_hom_apply [comm_monoid M] (x : M) (n : multiplicative ℕ) :
  powers_mul_hom M x n = x ^ n.to_add := rfl

@[simp] lemma powers_mul_hom_symm_apply [comm_monoid M] (f : multiplicative ℕ →* M) :
  (powers_mul_hom M).symm f = f (multiplicative.of_add 1) := rfl

@[simp] lemma zpowers_mul_hom_apply [comm_group G] (x : G) (n : multiplicative ℤ) :
  zpowers_mul_hom G x n = x ^ n.to_add := rfl

@[simp] lemma zpowers_mul_hom_symm_apply [comm_group G] (f : multiplicative ℤ →* G) :
  (zpowers_mul_hom G).symm f = f (multiplicative.of_add 1) := rfl

@[simp] lemma multiples_add_hom_apply [add_comm_monoid A] (x : A) (n : ℕ) :
  multiples_add_hom A x n = n • x := rfl

@[simp] lemma multiples_add_hom_symm_apply [add_comm_monoid A] (f : ℕ →+ A) :
  (multiples_add_hom A).symm f = f 1 := rfl

@[simp] lemma zmultiples_add_hom_apply [add_comm_group A] (x : A) (n : ℤ) :
  zmultiples_add_hom A x n = n • x := rfl

@[simp] lemma zmultiples_add_hom_symm_apply [add_comm_group A] (f : ℤ →+ A) :
  (zmultiples_add_hom A).symm f = f 1 := rfl

/-!
### Commutativity (again)

Facts about `semiconj_by` and `commute` that require `zpow` or `zsmul`, or the fact that integer
multiplication equals semiring multiplication.
-/

namespace semiconj_by

section

variables [semiring R] {a x y : R}

@[simp] lemma cast_nat_mul_right (h : semiconj_by a x y) (n : ℕ) :
  semiconj_by a ((n : R) * x) (n * y) :=
semiconj_by.mul_right (nat.commute_cast _ _) h

@[simp] lemma cast_nat_mul_left (h : semiconj_by a x y) (n : ℕ) : semiconj_by ((n : R) * a) x y :=
semiconj_by.mul_left (nat.cast_commute _ _) h

@[simp] lemma cast_nat_mul_cast_nat_mul (h : semiconj_by a x y) (m n : ℕ) :
  semiconj_by ((m : R) * a) (n * x) (n * y) :=
(h.cast_nat_mul_left m).cast_nat_mul_right n

end

variables [monoid M] [group G] [ring R]

@[simp, to_additive] lemma units_zpow_right {a : M} {x y : Mˣ} (h : semiconj_by a x y) :
  ∀ m : ℤ, semiconj_by a (↑(x^m)) (↑(y^m))
| (n : ℕ) := by simp only [zpow_coe_nat, units.coe_pow, h, pow_right]
| -[1+n] := by simp only [zpow_neg_succ_of_nat, units.coe_pow, units_inv_right, h, pow_right]

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
  commute (m * a : R) (n * b : R) :=
h.cast_nat_mul_cast_nat_mul m n

@[simp] theorem self_cast_nat_mul (n : ℕ) : commute a (n * a : R) :=
(commute.refl a).cast_nat_mul_right n

@[simp] theorem cast_nat_mul_self (n : ℕ) : commute ((n : R) * a) a :=
(commute.refl a).cast_nat_mul_left n

@[simp] theorem self_cast_nat_mul_cast_nat_mul (m n : ℕ) : commute (m * a : R) (n * a : R) :=
(commute.refl a).cast_nat_mul_cast_nat_mul m n

end

variables [monoid M] [group G] [ring R]

@[simp, to_additive] lemma units_zpow_right {a : M} {u : Mˣ} (h : commute a u) (m : ℤ) :
  commute a (↑(u^m)) :=
h.units_zpow_right m

@[simp, to_additive] lemma units_zpow_left {u : Mˣ} {a : M} (h : commute ↑u a) (m : ℤ) :
  commute (↑(u^m)) a :=
(h.symm.units_zpow_right m).symm

variables {a b : R}

@[simp] lemma cast_int_mul_right (h : commute a b) (m : ℤ) : commute a (m * b : R) :=
h.cast_int_mul_right m

@[simp] lemma cast_int_mul_left (h : commute a b) (m : ℤ) : commute ((m : R) * a) b :=
h.cast_int_mul_left m

lemma cast_int_mul_cast_int_mul (h : commute a b) (m n : ℤ) : commute (m * a : R) (n * b : R) :=
h.cast_int_mul_cast_int_mul m n

variables (a) (m n : ℤ)

@[simp] lemma cast_int_left : commute (m : R) a :=
by { rw [← mul_one (m : R)], exact (one_left a).cast_int_mul_left m }

@[simp] lemma cast_int_right : commute a m :=
by { rw [← mul_one (m : R)], exact (one_right a).cast_int_mul_right m }

@[simp] theorem self_cast_int_mul : commute a (n * a : R) := (commute.refl a).cast_int_mul_right n

@[simp] theorem cast_int_mul_self : commute ((n : R) * a) a := (commute.refl a).cast_int_mul_left n

theorem self_cast_int_mul_cast_int_mul : commute (m * a : R) (n * a : R) :=
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

@[simp] lemma int.to_add_zpow (a : multiplicative ℤ) (b : ℤ) : to_add (a ^ b) = to_add a * b :=
int.induction_on b (by simp)
  (by simp [zpow_add, mul_add] {contextual := tt})
  (by simp [zpow_add, mul_add, sub_eq_add_neg, -int.add_neg_one] {contextual := tt})

@[simp] lemma int.of_add_mul (a b : ℤ) : of_add (a * b) = of_add a ^ b :=
(int.to_add_zpow _ _).symm

end multiplicative

namespace units

variables [monoid M]

lemma conj_pow (u : Mˣ) (x : M) (n : ℕ) : (↑u * x * ↑(u⁻¹))^n = u * x^n * ↑(u⁻¹) :=
(divp_eq_iff_mul_eq.2 ((u.mk_semiconj_by x).pow_right n).eq.symm).symm

lemma conj_pow' (u : Mˣ) (x : M) (n : ℕ) : (↑(u⁻¹) * x * u)^n = ↑(u⁻¹) * x^n * u:=
(u⁻¹).conj_pow x n

end units

namespace mul_opposite

/-- Moving to the opposite monoid commutes with taking powers. -/
@[simp] lemma op_pow [monoid M] (x : M) (n : ℕ) : op (x ^ n) = (op x) ^ n := rfl
@[simp] lemma unop_pow [monoid M] (x : Mᵐᵒᵖ) (n : ℕ) : unop (x ^ n) = (unop x) ^ n := rfl

/-- Moving to the opposite group or group_with_zero commutes with taking powers. -/
@[simp] lemma op_zpow [div_inv_monoid M] (x : M) (z : ℤ) : op (x ^ z) = (op x) ^ z := rfl
@[simp] lemma unop_zpow [div_inv_monoid M] (x : Mᵐᵒᵖ) (z : ℤ) : unop (x ^ z) = (unop x) ^ z := rfl

end mul_opposite
