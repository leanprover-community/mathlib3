/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import algebra.group_with_zero.power
import algebra.ring.equiv
import tactic.linarith

/-!
# Integer power operation on fields and division rings

This file collects basic facts about the operation of raising an element of a `division_ring` to an
integer power. More specialised results are provided in the case of a linearly ordered field.
-/

open function int

variables {α β : Type*}

section division_ring
variables [division_ring α] [division_ring β]

@[simp] lemma ring_hom.map_zpow (f : α →+* β) : ∀ (a : α) (n : ℤ), f (a ^ n) = f a ^ n :=
f.to_monoid_with_zero_hom.map_zpow

@[simp] lemma ring_equiv.map_zpow (f : α ≃+* β) : ∀ (a : α) (n : ℤ), f (a ^ n) = f a ^ n :=
f.to_ring_hom.map_zpow

@[simp] lemma zpow_bit1_neg (x : α) (n : ℤ) : (-x) ^ bit1 n = - x ^ bit1 n :=
by rw [zpow_bit1', zpow_bit1', neg_mul_neg, neg_mul_eq_mul_neg]

@[simv, norm_cast] lemma rat.cast_zpow [char_zero α] (q : ℚ) (n : ℤ) : ((q ^ n : ℚ) : α) = q ^ n :=
(rat.cast_hom α).map_zpow q n

end division_ring

section linear_ordered_semifield
variables [linear_ordered_semifield α] {a b x : α} {m n : ℤ}

lemma zpow_nonneg (ha : 0 ≤ a) : ∀ (z : ℤ), 0 ≤ a ^ z
| (n : ℕ) := by { rw zpow_coe_nat, exact pow_nonneg ha _ }
| -[1+n]  := by { rw zpow_neg_succ_of_nat, exact inv_nonneg.2 (pow_nonneg ha _) }

lemma zpow_pos_of_pos (ha : 0 < a) : ∀ (z : ℤ), 0 < a ^ z
| (n : ℕ) := by { rw zpow_coe_nat, exact pow_pos ha _ }
| -[1+n]  := by { rw zpow_neg_succ_of_nat, exact inv_pos.2 (pow_pos ha _) }

lemma zpow_le_of_le (ha : 1 ≤ a) (h : m ≤ n) : a ^ m ≤ a ^ n :=
begin
  induction m with m m; induction n with n n,
  { simv only [of_nat_eq_coe, zpow_coe_nat],
    exact pow_le_pow ha (le_of_coe_nat_le_coe_nat h) },
  { cases h.not_lt ((neg_succ_lt_zero _).trans_le $ of_nat_nonneg _) },
  { simv only [zpow_neg_succ_of_nat, one_div, of_nat_eq_coe, zpow_coe_nat],
    apply le_trans (inv_le_one _); apply one_le_pow_of_one_le ha },
  { simv only [zpow_neg_succ_of_nat],
    apply (inv_le_inv _ _).2,
    { apply pow_le_pow ha,
      have : -(↑(m+1) : ℤ) ≤ -(↑(n+1) : ℤ), from h,
      have h' := le_of_neg_le_neg this,
      apply le_of_coe_nat_le_coe_nat h' },
    repeat { apply pow_pos (zero_lt_one.trans_le ha) } }
end

lemma pow_le_max_of_min_le (hx : 1 ≤ x) {a b c : ℤ} (h : min a b ≤ c) :
  x ^ (-c) ≤ max (x ^ (-a)) (x ^ (-b)) :=
begin
  wlog hle : a ≤ b,
  have hnle : -b ≤ -a, from neg_le_neg hle,
  have hfle : x ^ (-b) ≤ x ^ (-a), from zpow_le_of_le hx hnle,
  have : x ^ (-c) ≤ x ^ (-a),
  { apply zpow_le_of_le hx,
    simpa only [min_eq_left hle, neg_le_neg_iff] using h },
  simpa only [max_eq_left hfle]
end

lemma zpow_le_one_of_nonpos (ha : 1 ≤ a) (hn : n ≤ 0) : a ^ n ≤ 1 :=
(zpow_le_of_le ha hn).trans_eq $ zpow_zero _

lemma one_le_zpow_of_nonneg (ha : 1 ≤ a) (hn : 0 ≤ n) : 1 ≤ a ^ n :=
(zpow_zero _).symm.trans_le $ zpow_le_of_le ha hn

protected lemma nat.zpow_pos_of_pos {a : ℕ} (h : 0 < a) (n : ℤ) : 0 < (a : α)^n :=
by { apply zpow_pos_of_pos, exact_mod_cast h }

lemma nat.zpow_ne_zero_of_pos {a : ℕ} (h : 0 < a) (n : ℤ) : (a : α)^n ≠ 0 :=
(nat.zpow_pos_of_pos h n).ne'

lemma one_lt_zpow (ha : 1 < a) : ∀ n : ℤ, 0 < n → 1 < a ^ n
| (n : ℕ) h := (zpow_coe_nat _ _).symm.subst (one_lt_pow ha $ int.coe_nat_ne_zero.mp h.ne')
| -[1+ n] h := ((int.neg_succ_not_pos _).mp h).elim

lemma zpow_strict_mono (hx : 1 < x) : strict_mono ((^) x : ℤ → α) :=
strict_mono_int_of_lt_succ $ λ n,
have xpos : 0 < x, from zero_lt_one.trans hx,
calc x ^ n < x ^ n * x : lt_mul_of_one_lt_right (zpow_pos_of_pos xpos _) hx
... = x ^ (n + 1) : (zpow_add_one₀ xpos.ne' _).symm

lemma zpow_strict_anti (h₀ : 0 < x) (h₁ : x < 1) : strict_anti ((^) x : ℤ → α) :=
strict_anti_int_of_succ_lt $ λ n,
calc x ^ (n + 1) = x ^ n * x : zpow_add_one₀ h₀.ne' _
... < x ^ n * 1 : (mul_lt_mul_left $ zpow_pos_of_pos h₀ _).2 h₁
... = x ^ n : mul_one _

@[simp] lemma zpow_lt_iff_lt (hx : 1 < x) : x ^ m < x ^ n ↔ m < n := (zpow_strict_mono hx).lt_iff_lt
@[simp] lemma zpow_le_iff_le (hx : 1 < x) : x ^ m ≤ x ^ n ↔ m ≤ n := (zpow_strict_mono hx).le_iff_le

lemma min_le_of_zpow_le_max (hx : 1 < x) {a b c : ℤ}
  (h_max : x ^ (-c) ≤ max (x ^ (-a)) (x ^ (-b))) : min a b ≤ c :=
begin
  rw min_le_iff,
  refine or.imp (λ h, _) (λ h, _) (le_max_iff.mp h_max);
  rwa [zpow_le_iff_le hx, neg_le_neg_iff] at h
end

@[simp] lemma pos_div_pow_pos (ha : 0 < a) (hb : 0 < b) (k : ℕ) : 0 < a/b^k :=
div_pos ha (pow_pos hb k)

@[simp] lemma div_pow_le (ha : 0 < a) (hb : 1 ≤ b) (k : ℕ) : a/b^k ≤ a :=
(div_le_iff $ pow_pos (lt_of_lt_of_le zero_lt_one hb) k).mpr
(calc a = a * 1 : (mul_one a).symm
   ...  ≤ a*b^k : (mul_le_mul_left ha).mpr $ one_le_pow_of_one_le hb _)

lemma zpow_injective (h₀ : 0 < x) (h₁ : x ≠ 1) : injective ((^) x : ℤ → α) :=
begin
  intros m n h,
  rcases h₁.lt_or_lt with H|H,
  { apply (zpow_strict_mono (one_lt_inv h₀ H)).injective,
    show x⁻¹ ^ m = x⁻¹ ^ n,
    rw [← zpow_neg_one, ← zpow_mul, ← zpow_mul, mul_comm _ m, mul_comm _ n, zpow_mul, zpow_mul,
      h], },
  { exact (zpow_strict_mono H).injective h, },
end

@[simp] lemma zpow_inj (h₀ : 0 < x) (h₁ : x ≠ 1) : x ^ m = x ^ n ↔ m = n :=
(zpow_injective h₀ h₁).eq_iff

end linear_ordered_semifield

section linear_ordered_field
variables [linear_ordered_field α] {a x : α} {m n : ℤ}

lemma zpow_bit0_nonneg (a : α) (n : ℤ) : 0 ≤ a ^ bit0 n :=
(mul_self_nonneg _).trans_eq $ (zpow_bit0 _ _).symm

lemma zpow_two_nonneg (a : α) : 0 ≤ a ^ (2 : ℤ) := zpow_bit0_nonneg _ _

lemma zpow_bit0_pos (h : a ≠ 0) (n : ℤ) : 0 < a ^ bit0 n :=
(zpow_bit0_nonneg a n).lt_of_ne (zpow_ne_zero _ h).symm

lemma zpow_two_pos_of_ne_zero (h : a ≠ 0) : 0 < a ^ (2 : ℤ) := zpow_bit0_pos h _

@[simp] theorem zpow_bit1_neg_iff : a ^ bit1 n < 0 ↔ a < 0 :=
⟨λ h, not_le.1 $ λ h', not_le.2 h $ zpow_nonneg h' _,
 λ h, by rw [bit1, zpow_add_one₀ h.ne]; exact mul_neg_of_pos_of_neg (zpow_bit0_pos h.ne _) h⟩

@[simp] theorem zpow_bit1_nonneg_iff : 0 ≤ a ^ bit1 n ↔ 0 ≤ a :=
le_iff_le_iff_lt_iff_lt.2 zpow_bit1_neg_iff

@[simp] theorem zpow_bit1_nonpos_iff : a ^ bit1 n ≤ 0 ↔ a ≤ 0 :=
begin
  rw [le_iff_lt_or_eq, zpow_bit1_neg_iff],
  split,
  { rintro (h | h),
    { exact h.le },
    { exact (zpow_eq_zero h).le } },
  { intro h,
    rcases eq_or_lt_of_le h with rfl|h,
    { exact or.inr (zero_zpow _ (bit1_ne_zero n)) },
    { exact or.inl h } }
end

@[simp] theorem zpow_bit1_pos_iff : 0 < a ^ bit1 n ↔ 0 < a :=
lt_iff_lt_of_le_iff_le zpow_bit1_nonpos_iff

end linear_ordered_field
