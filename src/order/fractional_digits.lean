/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import data.real.nnreal
import data.nat.log
import algebra.order.floor
import data.fin.vec_notation

/-!
# Fractional Digits of elements of linearly ordered fields

## Main definitions

* `zlog`

## Main statements

* `le_pow_zlog`
* `lt_pow_succ_zlog`

-/


variables {R : Type*} [linear_ordered_field R] [floor_ring R]

/-- The greatest power of `b` such that `b ^ zlog b r ≤ r`. -/
def zlog (b : ℕ) (r : R) : ℤ :=
if 1 ≤ r then
  nat.log b (nat.floor r)
else
  -nat.clog b (nat.ceil r⁻¹)

lemma le_pow_zlog (b : ℕ) (r : R) (hn : 1 < b) (hr : 0 < r) :
  (b : R) ^ zlog b r ≤ r :=
begin
  by_cases hr1 : 1 ≤ r,
  { rw [zlog, if_pos hr1, zpow_coe_nat],
    refine le_trans _ (nat.floor_le hr.le),
    exact_mod_cast nat.pow_log_le_self hn _,
    refine lt_of_lt_of_le (zero_lt_one.trans_eq nat.floor_one.symm) (nat.floor_mono hr1), },
  { have : 1 < ⌈r⁻¹⌉₊,
    { rw not_le at hr1,
      replace hr1 := one_lt_inv hr hr1,
      exact_mod_cast hr1.trans_le (nat.le_ceil _), },
    rw [zlog, if_neg hr1, zpow_neg_coe_of_pos _ (nat.clog_pos hn $ nat.succ_le_of_lt this)],
    apply inv_le_of_inv_le hr,
    refine le_trans (nat.le_ceil _) _,
    exact_mod_cast nat.le_pow_clog hn _, },
end

lemma lt_pow_succ_zlog (b : ℕ) (r : R) (hn : 1 < b) (hr : 0 < r) :
  r < (b : R) ^ (zlog b r + 1) :=
begin
  by_cases hr1 : 1 ≤ r,
  { rw [zlog, if_pos hr1, int.coe_nat_add_one_out, zpow_coe_nat],
    refine (nat.lt_succ_floor _).trans_le _,
    exact_mod_cast nat.succ_le_of_lt (nat.lt_pow_succ_log_self hn ⌊r⌋₊), },
  { have hcri : 1 < ⌈r⁻¹⌉₊,
    { rw not_le at hr1,
      replace hr1 := one_lt_inv hr hr1,
      exact_mod_cast hr1.trans_le (nat.le_ceil _), },
    have : 1 ≤ nat.clog b ⌈r⁻¹⌉₊ := nat.succ_le_of_lt (nat.clog_pos hn $ nat.succ_le_of_lt hcri),
    rw [zlog, if_neg hr1, neg_add_eq_sub, ←neg_sub, ←int.coe_nat_one, ← int.coe_nat_sub this,
      zpow_neg₀, zpow_coe_nat, lt_inv hr (pow_pos (nat.cast_pos.mpr $ zero_lt_one.trans hn) _)],
    have := nat.pow_pred_clog_lt_self hn hcri,
    rw nat.lt_ceil at this,
    exact_mod_cast this }
end

#check @nat.pow_le_iff_le_log

lemma zpow_le_iff_le_log {b : ℕ} (hb : 1 < b) {z : ℤ} {r : R} (hy : 0 < r) :
  (b : R) ^ z ≤ r ↔ z ≤ zlog b r :=
begin
  by_cases hr1 : 1 ≤ r,
  obtain ⟨n, rfl | rfl⟩ := int.eq_coe_or_neg z,
  { rw zpow_coe_nat, },
  induction z using int.,
  rw [zlog, if_pos hr1],
  rw int.le_coe

end

def fractional_digits_aux (b : ℕ) (hn : 1 < b) : ℕ → Π r : R, 0 ≤ r → r < 1 → fin b
| 0 := λ r hr0 hr1, ⟨⌊b • r⌋₊, (nat.floor_lt (nsmul_nonneg hr0 _)).mpr $
  begin
    rw nsmul_eq_mul,
    apply mul_lt_of_lt_one_right (zero_lt_one.trans $ _) hr1,
    exact_mod_cast hn,
  end⟩
| (k + 1) := λ r hr0 hr1, fractional_digits_aux k (b • r - ⌊n • r⌋₊)
  (sub_nonneg_of_le $ nat.floor_le $ nsmul_nonneg hr0 _) (sub_lt_iff_lt_add.mpr $
    (nat.lt_succ_floor _).trans_eq $ (nat.cast_succ _).trans (add_comm _ _))

/-- Compute the `k`th digit of `r` in base `b`.

Note: the VM gets stuck in an infinte loop without the `true →` in `hr`! -/
def fractional_digits (b : ℕ) (hn : 1 < b) (r : R) (hr : 0 ≤ r) (k : ℕ) : fin b :=
fractional_digits_aux b hn k (r / (b : R) ^ (zlog b r + 1))
  (div_nonneg (hr) $ zpow_nonneg (nat.cast_nonneg _) _) $ begin
    obtain rfl | hr := eq_or_lt_of_le (hr),
    { rw zero_div, exact zero_lt_one },
    have := lt_pow_succ_zlog _ r hn hr,
    rw div_lt_one,
    exact this,
    linarith,
  end
