/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.int.gcd
import tactic.abel

/-!
# Congruences modulo a natural number

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the equivalence relation `a ≡ b [MOD n]` on the natural numbers,
and proves basic properties about it such as the Chinese Remainder Theorem
`modeq_and_modeq_iff_modeq_mul`.

## Notations

`a ≡ b [MOD n]` is notation for `nat.modeq n a b`, which is defined to mean `a % n = b % n`.

## Tags

modeq, congruence, mod, MOD, modulo
-/

namespace nat

/-- Modular equality. `n.modeq a b`, or `a ≡ b [MOD n]`, means that `a - b` is a multiple of `n`. -/
@[derive decidable]
def modeq (n a b : ℕ) := a % n = b % n

notation a ` ≡ `:50 b ` [MOD `:50 n `]`:0 := modeq n a b

variables {m n a b c d : ℕ}

namespace modeq

@[refl] protected theorem refl (a : ℕ) : a ≡ a [MOD n] := @rfl _ _

protected theorem rfl : a ≡ a [MOD n] := modeq.refl _

instance : is_refl _ (modeq n) := ⟨modeq.refl⟩

@[symm] protected theorem symm : a ≡ b [MOD n] → b ≡ a [MOD n] := eq.symm

@[trans] protected theorem trans : a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c [MOD n] := eq.trans

protected theorem comm : a ≡ b [MOD n] ↔ b ≡ a [MOD n] := ⟨modeq.symm, modeq.symm⟩

end modeq

theorem modeq_zero_iff_dvd : a ≡ 0 [MOD n] ↔ n ∣ a :=
by rw [modeq, zero_mod, dvd_iff_mod_eq_zero]

lemma _root_.has_dvd.dvd.modeq_zero_nat (h : n ∣ a) : a ≡ 0 [MOD n] := modeq_zero_iff_dvd.2 h
lemma _root_.has_dvd.dvd.zero_modeq_nat (h : n ∣ a) : 0 ≡ a [MOD n] := h.modeq_zero_nat.symm

theorem modeq_iff_dvd : a ≡ b [MOD n] ↔ (n:ℤ) ∣ b - a :=
by rw [modeq, eq_comm, ← int.coe_nat_inj', int.coe_nat_mod, int.coe_nat_mod,
   int.mod_eq_mod_iff_mod_sub_eq_zero, int.dvd_iff_mod_eq_zero]

alias modeq_iff_dvd ↔ modeq.dvd modeq_of_dvd

/-- A variant of `modeq_iff_dvd` with `nat` divisibility -/
theorem modeq_iff_dvd' (h : a ≤ b) : a ≡ b [MOD n] ↔ n ∣ b - a :=
by rw [modeq_iff_dvd, ←int.coe_nat_dvd, int.coe_nat_sub h]

theorem mod_modeq (a n) : a % n ≡ a [MOD n] := mod_mod _ _

namespace modeq

protected theorem of_dvd (d : m ∣ n) (h : a ≡ b [MOD n]) : a ≡ b [MOD m] :=
modeq_of_dvd ((int.coe_nat_dvd.2 d).trans h.dvd)

protected theorem mul_left' (c : ℕ) (h : a ≡ b [MOD n]) : c * a ≡ c * b [MOD (c * n)] :=
by unfold modeq at *; rw [mul_mod_mul_left, mul_mod_mul_left, h]

protected theorem mul_left (c : ℕ) (h : a ≡ b [MOD n]) : c * a ≡ c * b [MOD n] :=
(h.mul_left' _ ).of_dvd (dvd_mul_left _ _)

protected theorem mul_right' (c : ℕ) (h : a ≡ b [MOD n]) : a * c ≡ b * c [MOD (n * c)] :=
by rw [mul_comm a, mul_comm b, mul_comm n]; exact h.mul_left' c

protected theorem mul_right (c : ℕ) (h : a ≡ b [MOD n]) : a * c ≡ b * c [MOD n] :=
by rw [mul_comm a, mul_comm b]; exact h.mul_left c

protected theorem mul (h₁ : a ≡ b [MOD n]) (h₂ : c ≡ d [MOD n]) : a * c ≡ b * d [MOD n] :=
(h₂.mul_left _ ).trans (h₁.mul_right _)

protected theorem pow (m : ℕ) (h : a ≡ b [MOD n]) : a ^ m ≡ b ^ m [MOD n] :=
begin
  induction m with d hd, {refl},
  rw [pow_succ, pow_succ],
  exact h.mul hd,
end

protected theorem add (h₁ : a ≡ b [MOD n]) (h₂ : c ≡ d [MOD n]) : a + c ≡ b + d [MOD n] :=
begin
  rw [modeq_iff_dvd, int.coe_nat_add, int.coe_nat_add, add_sub_add_comm],
  exact dvd_add h₁.dvd h₂.dvd,
end

protected theorem add_left (c : ℕ) (h : a ≡ b [MOD n]) : c + a ≡ c + b [MOD n] :=
modeq.rfl.add h

protected theorem add_right (c : ℕ) (h : a ≡ b [MOD n]) : a + c ≡ b + c [MOD n] :=
h.add modeq.rfl

protected theorem add_left_cancel (h₁ : a ≡ b [MOD n]) (h₂ : a + c ≡ b + d [MOD n]) :
  c ≡ d [MOD n] :=
begin
  simp only [modeq_iff_dvd, int.coe_nat_add] at *,
  rw add_sub_add_comm at h₂,
  convert _root_.dvd_sub h₂ h₁ using 1,
  rw add_sub_cancel',
end

protected theorem add_left_cancel' (c : ℕ) (h : c + a ≡ c + b [MOD n]) : a ≡ b [MOD n] :=
modeq.rfl.add_left_cancel h

protected theorem add_right_cancel (h₁ : c ≡ d [MOD n]) (h₂ : a + c ≡ b + d [MOD n]) :
  a ≡ b [MOD n] :=
by { rw [add_comm a, add_comm b] at h₂, exact h₁.add_left_cancel h₂ }

protected theorem add_right_cancel' (c : ℕ) (h : a + c ≡ b + c [MOD n]) : a ≡ b [MOD n] :=
modeq.rfl.add_right_cancel h

/-- Cancel left multiplication on both sides of the `≡` and in the modulus.

For cancelling left multiplication in the modulus, see `nat.modeq.of_mul_left`. -/
protected theorem mul_left_cancel' {a b c m : ℕ} (hc : c ≠ 0) :
  c * a ≡ c * b [MOD c * m] → a ≡ b [MOD m] :=
by simp [modeq_iff_dvd, ←mul_sub, mul_dvd_mul_iff_left (by simp [hc] : (c : ℤ) ≠ 0)]

protected theorem mul_left_cancel_iff' {a b c m : ℕ} (hc : c ≠ 0) :
  c * a ≡ c * b [MOD c * m] ↔ a ≡ b [MOD m] :=
⟨modeq.mul_left_cancel' hc, modeq.mul_left' _⟩

/-- Cancel right multiplication on both sides of the `≡` and in the modulus.

For cancelling right multiplication in the modulus, see `nat.modeq.of_mul_right`. -/
protected theorem mul_right_cancel' {a b c m : ℕ} (hc : c ≠ 0) :
  a * c ≡ b * c [MOD m * c] → a ≡ b [MOD m] :=
by simp [modeq_iff_dvd, ←sub_mul, mul_dvd_mul_iff_right (by simp [hc] : (c : ℤ) ≠ 0)]

protected theorem mul_right_cancel_iff' {a b c m : ℕ} (hc : c ≠ 0) :
  a * c ≡ b * c [MOD m * c] ↔ a ≡ b [MOD m] :=
⟨modeq.mul_right_cancel' hc, modeq.mul_right' _⟩

/-- Cancel left multiplication in the modulus.

For cancelling left multiplication on both sides of the `≡`, see `nat.modeq.mul_left_cancel'`. -/
theorem of_mul_left (m : ℕ) (h : a ≡ b [MOD m * n]) : a ≡ b [MOD n] :=
by { rw [modeq_iff_dvd] at *, exact (dvd_mul_left (n : ℤ) (m : ℤ)).trans h }

/-- Cancel right multiplication in the modulus.

For cancelling right multiplication on both sides of the `≡`, see `nat.modeq.mul_right_cancel'`. -/
theorem of_mul_right (m : ℕ) : a ≡ b [MOD n * m] → a ≡ b [MOD n] := mul_comm m n ▸ of_mul_left _

end modeq

lemma modeq_sub (h : b ≤ a) : a ≡ b [MOD a - b] := (modeq_of_dvd $ by rw [int.coe_nat_sub h]).symm

lemma modeq_one : a ≡ b [MOD 1] := modeq_of_dvd $ one_dvd _

@[simp] lemma modeq_zero_iff : a ≡ b [MOD 0] ↔ a = b := by rw [modeq, mod_zero, mod_zero]

@[simp] lemma add_modeq_left : n + a ≡ a [MOD n] := by rw [modeq, add_mod_left]
@[simp] lemma add_modeq_right : a + n ≡ a [MOD n] := by rw [modeq, add_mod_right]

namespace modeq

lemma le_of_lt_add (h1 : a ≡ b [MOD m]) (h2 : a < b + m) : a ≤ b :=
(le_total a b).elim id (λ h3, nat.le_of_sub_eq_zero
  (eq_zero_of_dvd_of_lt ((modeq_iff_dvd' h3).mp h1.symm) ((tsub_lt_iff_left h3).mpr h2)))

lemma add_le_of_lt (h1 : a ≡ b [MOD m]) (h2 : a < b) : a + m ≤ b :=
le_of_lt_add (add_modeq_right.trans h1) (add_lt_add_right h2 m)

lemma dvd_iff (h : a ≡ b [MOD m]) (hdm : d ∣ m) : d ∣ a ↔ d ∣ b :=
begin
  simp only [←modeq_zero_iff_dvd],
  replace h := h.of_dvd hdm,
  exact ⟨h.symm.trans, h.trans⟩,
end

lemma gcd_eq (h : a ≡ b [MOD m]) : gcd a m = gcd b m :=
begin
  have h1 := gcd_dvd_right a m,
  have h2 := gcd_dvd_right b m,
  exact dvd_antisymm
    (dvd_gcd ((h.dvd_iff h1).mp (gcd_dvd_left a m)) h1)
    (dvd_gcd ((h.dvd_iff h2).mpr (gcd_dvd_left b m)) h2),
end

lemma eq_of_abs_lt (h : a ≡ b [MOD m]) (h2 : |(b - a : ℤ)| < m) : a = b :=
begin
  apply int.coe_nat_inj,
  rw [eq_comm, ←sub_eq_zero],
  exact int.eq_zero_of_abs_lt_dvd (modeq_iff_dvd.mp h) h2,
end

lemma eq_of_lt_of_lt (h : a ≡ b [MOD m]) (ha : a < m) (hb : b < m) : a = b :=
h.eq_of_abs_lt $ abs_sub_lt_iff.2
  ⟨(sub_le_self _ $ int.coe_nat_nonneg _).trans_lt $ cast_lt.2 hb,
   (sub_le_self _ $ int.coe_nat_nonneg _).trans_lt $ cast_lt.2 ha⟩

/-- To cancel a common factor `c` from a `modeq` we must divide the modulus `m` by `gcd m c` -/
lemma cancel_left_div_gcd (hm : 0 < m) (h : c * a ≡ c * b [MOD m]) : a ≡ b [MOD m / gcd m c] :=
begin
  let d := gcd m c,
  have hmd := gcd_dvd_left m c,
  have hcd := gcd_dvd_right m c,
  rw modeq_iff_dvd,
  refine int.dvd_of_dvd_mul_right_of_gcd_one _ _,
  show (m/d : ℤ) ∣ (c/d) * (b - a),
  { rw [mul_comm, ←int.mul_div_assoc (b - a) (int.coe_nat_dvd.mpr hcd), mul_comm],
    apply int.div_dvd_div (int.coe_nat_dvd.mpr hmd),
    rw mul_sub,
    exact modeq_iff_dvd.mp h },
  show int.gcd (m/d) (c/d) = 1,
  { simp only [←int.coe_nat_div, int.coe_nat_gcd (m / d) (c / d), gcd_div hmd hcd,
        nat.div_self (gcd_pos_of_pos_left c hm)] },
end

lemma cancel_right_div_gcd (hm : 0 < m) (h : a * c ≡ b * c [MOD m]) : a ≡ b [MOD m / gcd m c] :=
by { apply cancel_left_div_gcd hm, simpa [mul_comm] using h }

lemma cancel_left_div_gcd' (hm : 0 < m) (hcd : c ≡ d [MOD m]) (h : c * a ≡ d * b [MOD m]) :
  a ≡ b [MOD m / gcd m c] :=
(h.trans (modeq.mul_right b hcd).symm).cancel_left_div_gcd hm

lemma cancel_right_div_gcd' (hm : 0 < m) (hcd : c ≡ d [MOD m]) (h : a * c ≡ b * d [MOD m]) :
  a ≡ b [MOD m / gcd m c] :=
hcd.cancel_left_div_gcd' hm $ by simpa [mul_comm] using h

/-- A common factor that's coprime with the modulus can be cancelled from a `modeq` -/
lemma cancel_left_of_coprime (hmc : gcd m c = 1) (h : c * a ≡ c * b [MOD m]) : a ≡ b [MOD m] :=
begin
  rcases m.eq_zero_or_pos with rfl | hm,
  { simp only [gcd_zero_left] at hmc,
    simp only [gcd_zero_left, hmc, one_mul, modeq_zero_iff] at h,
    subst h },
  simpa [hmc] using h.cancel_left_div_gcd hm
end

/-- A common factor that's coprime with the modulus can be cancelled from a `modeq` -/
lemma cancel_right_of_coprime (hmc : gcd m c = 1) (h : a * c ≡ b * c [MOD m]) : a ≡ b [MOD m] :=
cancel_left_of_coprime hmc $ by simpa [mul_comm] using h

end modeq

/-- The natural number less than `lcm n m` congruent to `a` mod `n` and `b` mod `m` -/
def chinese_remainder' (h : a ≡ b [MOD gcd n m]) : {k // k ≡ a [MOD n] ∧ k ≡ b [MOD m]} :=
if hn : n = 0 then ⟨a, begin rw [hn, gcd_zero_left] at h, split, refl, exact h end⟩ else
if hm : m = 0 then ⟨b, begin rw [hm, gcd_zero_right] at h, split, exact h.symm, refl end⟩ else
⟨let (c, d) := xgcd n m in int.to_nat (((n * c * b + m * d * a) / gcd n m) % lcm n m), begin
  rw xgcd_val,
  dsimp [chinese_remainder'._match_1],
  rw [modeq_iff_dvd, modeq_iff_dvd,
    int.to_nat_of_nonneg (int.mod_nonneg _ (int.coe_nat_ne_zero.2 (lcm_ne_zero hn hm)))],
  have hnonzero : (gcd n m : ℤ) ≠ 0 := begin
    norm_cast,
    rw [nat.gcd_eq_zero_iff, not_and],
    exact λ _, hm,
  end,
  have hcoedvd : ∀ t, (gcd n m : ℤ) ∣ t * (b - a) := λ t, h.dvd.mul_left _,
  have := gcd_eq_gcd_ab n m,
  split; rw [int.mod_def, ← sub_add]; refine dvd_add _ (dvd_mul_of_dvd_left _ _); try {norm_cast},
  { rw ← sub_eq_iff_eq_add' at this,
    rw [← this, sub_mul, ← add_sub_assoc, add_comm, add_sub_assoc, ← mul_sub,
      int.add_div_of_dvd_left, int.mul_div_cancel_left _ hnonzero,
      int.mul_div_assoc _ h.dvd, ← sub_sub, sub_self, zero_sub, dvd_neg, mul_assoc],
    exact dvd_mul_right _ _,
    norm_cast, exact dvd_mul_right _ _, },
  { exact dvd_lcm_left n m, },
  { rw ← sub_eq_iff_eq_add at this,
    rw [← this, sub_mul, sub_add, ← mul_sub, int.sub_div_of_dvd, int.mul_div_cancel_left _ hnonzero,
      int.mul_div_assoc _ h.dvd, ← sub_add, sub_self, zero_add, mul_assoc],
    exact dvd_mul_right _ _,
    exact hcoedvd _ },
  { exact dvd_lcm_right n m, },
end⟩

/-- The natural number less than `n*m` congruent to `a` mod `n` and `b` mod `m` -/
def chinese_remainder (co : coprime n m) (a b : ℕ) : {k // k ≡ a [MOD n] ∧ k ≡ b [MOD m]} :=
chinese_remainder' (by convert modeq_one)

lemma chinese_remainder'_lt_lcm (h : a ≡ b [MOD gcd n m]) (hn : n ≠ 0) (hm : m ≠ 0) :
  ↑(chinese_remainder' h) < lcm n m :=
begin
  dsimp only [chinese_remainder'],
  rw [dif_neg hn, dif_neg hm, subtype.coe_mk, xgcd_val, ←int.to_nat_coe_nat (lcm n m)],
  have lcm_pos := int.coe_nat_pos.mpr (nat.pos_of_ne_zero (lcm_ne_zero hn hm)),
  exact (int.to_nat_lt_to_nat lcm_pos).mpr (int.mod_lt_of_pos _ lcm_pos),
end

lemma chinese_remainder_lt_mul (co : coprime n m) (a b : ℕ) (hn : n ≠ 0) (hm : m ≠ 0) :
  ↑(chinese_remainder co a b) < n * m :=
lt_of_lt_of_le (chinese_remainder'_lt_lcm _ hn hm) (le_of_eq co.lcm_eq_mul)

lemma modeq_and_modeq_iff_modeq_mul {a b m n : ℕ} (hmn : coprime m n) :
  a ≡ b [MOD m] ∧ a ≡ b [MOD n] ↔ (a ≡ b [MOD m * n]) :=
⟨λ h, begin
    rw [nat.modeq_iff_dvd, nat.modeq_iff_dvd, ← int.dvd_nat_abs,
      int.coe_nat_dvd, ← int.dvd_nat_abs, int.coe_nat_dvd] at h,
    rw [nat.modeq_iff_dvd, ← int.dvd_nat_abs, int.coe_nat_dvd],
    exact hmn.mul_dvd_of_dvd_of_dvd h.1 h.2
  end,
λ h, ⟨h.of_mul_right _, h.of_mul_left _⟩⟩

lemma coprime_of_mul_modeq_one (b : ℕ) {a n : ℕ} (h : a * b ≡ 1 [MOD n]) : coprime a n :=
begin
  obtain ⟨g, hh⟩ := nat.gcd_dvd_right a n,
  rw [nat.coprime_iff_gcd_eq_one, ← nat.dvd_one, ← nat.modeq_zero_iff_dvd],
  calc 1 ≡ a * b [MOD a.gcd n] : nat.modeq.of_mul_right g (hh.subst h).symm
  ... ≡ 0 * b [MOD a.gcd n] : (nat.modeq_zero_iff_dvd.mpr (nat.gcd_dvd_left _ _)).mul_right b
  ... = 0 : by rw zero_mul,
end

@[simp] lemma mod_mul_right_mod (a b c : ℕ) : a % (b * c) % b = a % b :=
(mod_modeq _ _).of_mul_right _

@[simp] lemma mod_mul_left_mod (a b c : ℕ) : a % (b * c) % c = a % c :=
(mod_modeq _ _).of_mul_left _

lemma div_mod_eq_mod_mul_div (a b c : ℕ) : a / b % c = a % (b * c) / b :=
if hb0 : b = 0 then by simp [hb0]
else by rw [← @add_right_cancel_iff _ _ _ (c * (a / b / c)), mod_add_div, nat.div_div_eq_div_mul,
  ← mul_right_inj' hb0, ← @add_left_cancel_iff _ _ _ (a % b), mod_add_div,
  mul_add, ← @add_left_cancel_iff _ _ _ (a % (b * c) % b), add_left_comm,
  ← add_assoc (a % (b * c) % b), mod_add_div, ← mul_assoc, mod_add_div, mod_mul_right_mod]

lemma add_mod_add_ite (a b c : ℕ) :
  (a + b) % c + (if c ≤ a % c + b % c then c else 0) = a % c + b % c :=
have (a + b) % c = (a % c + b % c) % c,
  from ((mod_modeq _ _).add $ mod_modeq _ _).symm,
if hc0 : c = 0 then by simp [hc0]
else
  begin
    rw this,
    split_ifs,
    { have h2 : (a % c + b % c) / c < 2,
        from nat.div_lt_of_lt_mul (by rw mul_two;
          exact add_lt_add (nat.mod_lt _ (nat.pos_of_ne_zero hc0))
            (nat.mod_lt _ (nat.pos_of_ne_zero hc0))),
      have h0 : 0 <  (a % c + b % c) / c, from nat.div_pos h (nat.pos_of_ne_zero hc0),
      rw [← @add_right_cancel_iff _ _ _ (c * ((a % c + b % c) / c)), add_comm _ c, add_assoc,
        mod_add_div, le_antisymm (le_of_lt_succ h2) h0, mul_one, add_comm] },
    { rw [nat.mod_eq_of_lt (lt_of_not_ge h), add_zero] }
  end

lemma add_mod_of_add_mod_lt {a b c : ℕ} (hc : a % c + b % c < c) :
  (a + b) % c = a % c + b % c :=
 by rw [← add_mod_add_ite, if_neg (not_le_of_lt hc), add_zero]

lemma add_mod_add_of_le_add_mod {a b c : ℕ} (hc : c ≤ a % c + b % c) :
  (a + b) % c + c = a % c + b % c :=
by rw [← add_mod_add_ite, if_pos hc]

lemma add_div {a b c : ℕ} (hc0 : 0 < c) : (a + b) / c = a / c + b / c +
  if c ≤ a % c + b % c then 1 else 0 :=
begin
  rw [← mul_right_inj' hc0.ne', ← @add_left_cancel_iff _ _ _ ((a + b) % c + a % c + b % c)],
  suffices : (a + b) % c + c * ((a + b) / c) + a % c + b % c =
    a % c + c * (a / c) + (b % c + c * (b / c)) + c * (if c ≤ a % c + b % c then 1 else 0) +
      (a + b) % c,
  { simpa only [mul_add, add_comm, add_left_comm, add_assoc] },
  rw [mod_add_div, mod_add_div, mod_add_div, mul_ite, add_assoc, add_assoc],
  conv_lhs { rw ← add_mod_add_ite },
  simp, ac_refl
end

lemma add_div_eq_of_add_mod_lt {a b c : ℕ} (hc : a % c + b % c < c) :
  (a + b) / c = a / c + b / c :=
if hc0 : c = 0 then by simp [hc0]
else by rw [add_div (nat.pos_of_ne_zero hc0), if_neg (not_le_of_lt hc), add_zero]

protected lemma add_div_of_dvd_right {a b c : ℕ} (hca : c ∣ a) :
  (a + b) / c = a / c + b / c :=
if h : c = 0 then by simp [h] else add_div_eq_of_add_mod_lt begin
  rw [nat.mod_eq_zero_of_dvd hca, zero_add],
  exact nat.mod_lt _ (pos_iff_ne_zero.mpr h),
end

protected lemma add_div_of_dvd_left {a b c : ℕ} (hca : c ∣ b) :
  (a + b) / c = a / c + b / c :=
by rwa [add_comm, nat.add_div_of_dvd_right, add_comm]

lemma add_div_eq_of_le_mod_add_mod {a b c : ℕ} (hc : c ≤ a % c + b % c) (hc0 : 0 < c) :
  (a + b) / c = a / c + b / c + 1 :=
by rw [add_div hc0, if_pos hc]

lemma add_div_le_add_div (a b c : ℕ) : a / c + b / c ≤ (a + b) / c :=
if hc0 : c = 0 then by simp [hc0]
else by rw [nat.add_div (nat.pos_of_ne_zero hc0)]; exact nat.le_add_right _ _

lemma le_mod_add_mod_of_dvd_add_of_not_dvd {a b c : ℕ} (h : c ∣ a + b) (ha : ¬ c ∣ a) :
  c ≤ a % c + b % c :=
by_contradiction $ λ hc,
  have (a + b) % c = a % c + b % c, from add_mod_of_add_mod_lt (lt_of_not_ge hc),
  by simp [dvd_iff_mod_eq_zero, *] at *

lemma odd_mul_odd {n m : ℕ} : n % 2 = 1 → m % 2 = 1 → (n * m) % 2 = 1 :=
by simpa [nat.modeq] using @modeq.mul 2 n 1 m 1

lemma odd_mul_odd_div_two {m n : ℕ} (hm1 : m % 2 = 1) (hn1 : n % 2 = 1) :
  (m * n) / 2 = m * (n / 2) + m / 2 :=
have hm0 : 0 < m := nat.pos_of_ne_zero (λ h, by simp * at *),
have hn0 : 0 < n := nat.pos_of_ne_zero (λ h, by simp * at *),
mul_right_injective₀ two_ne_zero $
by rw [mul_add, two_mul_odd_div_two hm1, mul_left_comm, two_mul_odd_div_two hn1,
  two_mul_odd_div_two (nat.odd_mul_odd hm1 hn1), mul_tsub, mul_one,
  ← add_tsub_assoc_of_le (succ_le_of_lt hm0),
  tsub_add_cancel_of_le (le_mul_of_one_le_right (nat.zero_le _) hn0)]

lemma odd_of_mod_four_eq_one {n : ℕ} : n % 4 = 1 → n % 2 = 1 :=
by simpa [modeq, show 2 * 2 = 4, by norm_num] using @modeq.of_mul_left 2 n 1 2

lemma odd_of_mod_four_eq_three {n : ℕ} : n % 4 = 3 → n % 2 = 1 :=
by simpa [modeq, show 2 * 2 = 4, by norm_num, show 3 % 4 = 3, by norm_num]
  using @modeq.of_mul_left 2 n 3 2

/-- A natural number is odd iff it has residue `1` or `3` mod `4`-/
lemma odd_mod_four_iff {n : ℕ} : n % 2 = 1 ↔ n % 4 = 1 ∨ n % 4 = 3 :=
have help : ∀ (m : ℕ), m < 4 → m % 2 = 1 → m = 1 ∨ m = 3 := dec_trivial,
⟨λ hn, help (n % 4) (mod_lt n (by norm_num)) $ (mod_mod_of_dvd n (by norm_num : 2 ∣ 4)).trans hn,
 λ h, or.dcases_on h odd_of_mod_four_eq_one odd_of_mod_four_eq_three⟩

end nat
