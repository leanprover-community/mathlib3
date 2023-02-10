/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
import algebra.parity
import algebra.char_zero.lemmas
import algebra.group_with_zero.power
import algebra.order.field.basic

/-!
# Lemmas about powers in ordered fields.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {α : Type*}
open function

section linear_ordered_semifield
variables [linear_ordered_semifield α] {a b c d e : α} {m n : ℤ}

/-! ### Integer powers -/

lemma zpow_le_of_le (ha : 1 ≤ a) (h : m ≤ n) : a ^ m ≤ a ^ n :=
begin
  have ha₀ : 0 < a, from one_pos.trans_le ha,
  lift n - m to ℕ using sub_nonneg.2 h with k hk,
  calc a ^ m = a ^ m * 1 : (mul_one _).symm
  ... ≤ a ^ m * a ^ k : mul_le_mul_of_nonneg_left (one_le_pow_of_one_le ha _) (zpow_nonneg ha₀.le _)
  ... = a ^ n : by rw [← zpow_coe_nat, ← zpow_add₀ ha₀.ne', hk, add_sub_cancel'_right]
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

lemma zpow_strict_mono (hx : 1 < a) : strict_mono ((^) a : ℤ → α) :=
strict_mono_int_of_lt_succ $ λ n,
have xpos : 0 < a, from zero_lt_one.trans hx,
calc a ^ n < a ^ n * a : lt_mul_of_one_lt_right (zpow_pos_of_pos xpos _) hx
... = a ^ (n + 1) : (zpow_add_one₀ xpos.ne' _).symm

lemma zpow_strict_anti (h₀ : 0 < a) (h₁ : a < 1) : strict_anti ((^) a : ℤ → α) :=
strict_anti_int_of_succ_lt $ λ n,
calc a ^ (n + 1) = a ^ n * a : zpow_add_one₀ h₀.ne' _
... < a ^ n * 1 : (mul_lt_mul_left $ zpow_pos_of_pos h₀ _).2 h₁
... = a ^ n : mul_one _

@[simp] lemma zpow_lt_iff_lt (hx : 1 < a) : a ^ m < a ^ n ↔ m < n := (zpow_strict_mono hx).lt_iff_lt
@[simp] lemma zpow_le_iff_le (hx : 1 < a) : a ^ m ≤ a ^ n ↔ m ≤ n := (zpow_strict_mono hx).le_iff_le

@[simp] lemma div_pow_le (ha : 0 ≤ a) (hb : 1 ≤ b) (k : ℕ) : a/b^k ≤ a :=
div_le_self ha $ one_le_pow_of_one_le hb _

lemma zpow_injective (h₀ : 0 < a) (h₁ : a ≠ 1) : injective ((^) a : ℤ → α) :=
begin
  rcases h₁.lt_or_lt with H|H,
  { exact (zpow_strict_anti h₀ H).injective },
  { exact (zpow_strict_mono H).injective }
end

@[simp] lemma zpow_inj (h₀ : 0 < a) (h₁ : a ≠ 1) : a ^ m = a ^ n ↔ m = n :=
(zpow_injective h₀ h₁).eq_iff

lemma zpow_le_max_of_min_le {x : α} (hx : 1 ≤ x) {a b c : ℤ} (h : min a b ≤ c) :
  x ^ -c ≤ max (x ^ -a) (x ^ -b) :=
begin
  have : antitone (λ n : ℤ, x ^ -n) := λ m n h, zpow_le_of_le hx (neg_le_neg h),
  exact (this h).trans_eq this.map_min,
end

lemma zpow_le_max_iff_min_le {x : α} (hx : 1 < x) {a b c : ℤ} :
  x ^ -c ≤ max (x ^ -a) (x ^ -b) ↔ min a b ≤ c :=
by simp_rw [le_max_iff, min_le_iff, zpow_le_iff_le hx, neg_le_neg_iff]

end linear_ordered_semifield

section linear_ordered_field
variables [linear_ordered_field α] {a b c d : α} {n : ℤ}

/-! ### Lemmas about powers to numerals. -/

lemma zpow_bit0_nonneg (a : α) (n : ℤ) : 0 ≤ a ^ bit0 n :=
(mul_self_nonneg _).trans_eq $ (zpow_bit0 _ _).symm

lemma zpow_two_nonneg (a : α) : 0 ≤ a ^ (2 : ℤ) := zpow_bit0_nonneg _ _

lemma zpow_bit0_pos (h : a ≠ 0) (n : ℤ) : 0 < a ^ bit0 n :=
(zpow_bit0_nonneg a n).lt_of_ne (zpow_ne_zero _ h).symm

lemma zpow_two_pos_of_ne_zero (h : a ≠ 0) : 0 < a ^ (2 : ℤ) := zpow_bit0_pos h _

@[simp] lemma zpow_bit0_pos_iff (hn : n ≠ 0) : 0 < a ^ bit0 n ↔ a ≠ 0 :=
⟨by { rintro h rfl, refine (zero_zpow _ _).not_gt h, rwa bit0_ne_zero }, λ h, zpow_bit0_pos h _⟩

@[simp] lemma zpow_bit1_neg_iff : a ^ bit1 n < 0 ↔ a < 0 :=
⟨λ h, not_le.1 $ λ h', not_le.2 h $ zpow_nonneg h' _,
 λ h, by rw [bit1, zpow_add_one₀ h.ne]; exact mul_neg_of_pos_of_neg (zpow_bit0_pos h.ne _) h⟩

@[simp] lemma zpow_bit1_nonneg_iff : 0 ≤ a ^ bit1 n ↔ 0 ≤ a :=
le_iff_le_iff_lt_iff_lt.2 zpow_bit1_neg_iff

@[simp] lemma zpow_bit1_nonpos_iff : a ^ bit1 n ≤ 0 ↔ a ≤ 0 :=
by rw [le_iff_lt_or_eq, le_iff_lt_or_eq, zpow_bit1_neg_iff, zpow_eq_zero_iff (int.bit1_ne_zero n)]

@[simp] lemma zpow_bit1_pos_iff : 0 < a ^ bit1 n ↔ 0 < a :=
lt_iff_lt_of_le_iff_le zpow_bit1_nonpos_iff

protected lemma even.zpow_nonneg (hn : even n) (a : α) : 0 ≤ a ^ n :=
by obtain ⟨k, rfl⟩ := hn; exact zpow_bit0_nonneg _ _

lemma even.zpow_pos_iff (hn : even n) (h : n ≠ 0) : 0 < a ^ n ↔ a ≠ 0 :=
by obtain ⟨k, rfl⟩ := hn; exact zpow_bit0_pos_iff (by rintro rfl; simpa using h)

lemma odd.zpow_neg_iff (hn : odd n) : a ^ n < 0 ↔ a < 0 :=
by cases hn with k hk; simpa only [hk, two_mul] using zpow_bit1_neg_iff

protected lemma odd.zpow_nonneg_iff (hn : odd n) : 0 ≤ a ^ n ↔ 0 ≤ a :=
by cases hn with k hk; simpa only [hk, two_mul] using zpow_bit1_nonneg_iff

lemma odd.zpow_nonpos_iff (hn : odd n) : a ^ n ≤ 0 ↔ a ≤ 0 :=
by cases hn with k hk; simpa only [hk, two_mul] using zpow_bit1_nonpos_iff

lemma odd.zpow_pos_iff (hn : odd n) : 0 < a ^ n ↔ 0 < a :=
by cases hn with k hk; simpa only [hk, two_mul] using zpow_bit1_pos_iff

alias even.zpow_pos_iff ↔ _ even.zpow_pos
alias odd.zpow_neg_iff ↔ _ odd.zpow_neg
alias odd.zpow_nonpos_iff ↔ _ odd.zpow_nonpos

lemma even.zpow_abs {p : ℤ} (hp : even p) (a : α) : |a| ^ p = a ^ p :=
by cases abs_choice a with h h; simp only [h, hp.neg_zpow _]

@[simp] lemma zpow_bit0_abs (a : α) (p : ℤ) : |a| ^ bit0 p = a ^ bit0 p := (even_bit0 _).zpow_abs _

/-! ### Miscellaneous lemmmas -/

/-- Bernoulli's inequality reformulated to estimate `(n : α)`. -/
lemma nat.cast_le_pow_sub_div_sub (H : 1 < a)  (n : ℕ) : (n : α) ≤ (a ^ n - 1) / (a - 1) :=
(le_div_iff (sub_pos.2 H)).2 $ le_sub_left_of_add_le $
  one_add_mul_sub_le_pow ((neg_le_self zero_le_one).trans H.le) _

/-- For any `a > 1` and a natural `n` we have `n ≤ a ^ n / (a - 1)`. See also
`nat.cast_le_pow_sub_div_sub` for a stronger inequality with `a ^ n - 1` in the numerator. -/
theorem nat.cast_le_pow_div_sub (H : 1 < a) (n : ℕ) : (n : α) ≤ a ^ n / (a - 1) :=
(n.cast_le_pow_sub_div_sub H).trans $ div_le_div_of_le (sub_nonneg.2 H.le)
  (sub_le_self _ zero_le_one)

end linear_ordered_field
