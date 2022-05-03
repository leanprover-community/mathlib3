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
# Integer logarithms

This file defines two `ℤ`-valued analogs of the logarithm of `n : R` with base `b`:
* `int.log b n`: Lower logarithm, or floor **log**. Greatest `k` such that `↑b^k ≤ n`.
* `int.clog b n`: Upper logarithm, or **c**eil **log**. Least `k` such that `n ≤ ↑b^k`.

-/
variables {R : Type*} [linear_ordered_field R] [floor_ring R]

namespace int

/-- The greatest power of `b` such that `b ^ log b r ≤ r`. -/
def log (b : ℕ) (r : R) : ℤ :=
if 1 ≤ r then nat.log b r else -nat.clog b r⁻¹

lemma log_of_left_le_one {b : ℕ} (hb : b ≤ 1) (n : R) : log b n = 0 :=
begin
  cases le_or_lt 1 n with hn hn,
  { rw [log, if_pos hn, nat.log_of_left_le_one hb, int.coe_nat_zero] },
  { rw [log, if_neg hn.not_le, nat.clog_of_left_le_one hb, int.coe_nat_zero, neg_zero] },
end

lemma log_of_right_le_zero {n : R} (hn : n ≤ 0) (b : ℕ) : log b n = 0 :=
by rw [log, if_neg (hn.trans_lt zero_lt_one).not_le,
    nat.clog_of_right_le_one ((inv_nonpos.2 hn).trans zero_le_one),
    int.coe_nat_zero, neg_zero]

lemma zpow_log_le_self (b : ℕ) (r : R) (hn : 1 < b) (hr : 0 < r) :
  (b : R) ^ log b r ≤ r :=
begin
  by_cases hr1 : 1 ≤ r,
  { rw [log, if_pos hr1, zpow_coe_nat],
    exact nat.pow_log_le_self hn hr1 },
  { have : 1 < r⁻¹,
    { rw not_le at hr1,
      exact one_lt_inv hr hr1, },
    rw [log, if_neg hr1, zpow_neg_coe_of_pos _ (nat.clog_pos hn this)],
    apply inv_le_of_inv_le hr,
    exact nat.le_pow_clog hn _, },
end

lemma lt_zpow_succ_log_self (b : ℕ) (r : R) (hn : 1 < b) (hr : 0 < r) :
  r < (b : R) ^ (log b r + 1) :=
begin
  by_cases hr1 : 1 ≤ r,
  { rw [log, if_pos hr1, int.coe_nat_add_one_out, zpow_coe_nat],
    exact nat.lt_pow_succ_log_self hn r, },
  { have hcri : 1 < r⁻¹,
    { rw not_le at hr1,
      exact one_lt_inv hr hr1, },
    have : 1 ≤ nat.clog b r⁻¹ := nat.succ_le_of_lt (nat.clog_pos hn hcri),
    rw [log, if_neg hr1, neg_add_eq_sub, ←neg_sub, ←int.coe_nat_one, ← int.coe_nat_sub this,
      zpow_neg₀, zpow_coe_nat, lt_inv hr (pow_pos (nat.cast_pos.mpr $ zero_lt_one.trans hn) _)],
    exact nat.pow_pred_clog_lt_self hn hcri }
end

/-- The least power of `b` such that `r ≤ b ^ log b r`. -/
def clog (b : ℕ) (r : R) : ℤ :=
if 1 ≤ r then nat.clog b r else -nat.log b r⁻¹

lemma clog_of_left_le_one {b : ℕ} (hb : b ≤ 1) (n : R) : clog b n = 0 :=
begin
  cases le_or_lt 1 n with hn hn,
  { rw [clog, if_pos hn, nat.clog_of_left_le_one hb, int.coe_nat_zero] },
  { rw [clog, if_neg hn.not_le, nat.log_of_left_le_one hb, int.coe_nat_zero, neg_zero] },
end

lemma clog_of_right_le_zero {n : R} (hn : n ≤ 0) (b : ℕ) : clog b n = 0 :=
begin
  rw [clog, if_neg (hn.trans_lt zero_lt_one).not_le, neg_eq_zero, int.coe_nat_eq_zero,
    nat.log_eq_zero_iff],
  cases le_or_lt b 1 with hb hb,
  { exact or.inr hb },
  { refine or.inl ((inv_nonpos.2 hn).trans_lt $ zero_lt_one.trans _),
    exact_mod_cast hb },
end

lemma clog_inv (b : ℕ) (r : R) : clog b r⁻¹ = -log b r :=
begin
  cases lt_or_le 0 r with hrp hrp,
  { obtain hr | rfl | hr := lt_trichotomy r 1,
    { have : 1 < r⁻¹ := one_lt_inv hrp hr,
      rw [clog, if_pos this.le, log, if_neg hr.not_le, neg_neg] },
    { rw [inv_one, clog, log, if_pos le_rfl, if_pos le_rfl, nat.clog_one_right,
        nat.log_one_right, int.coe_nat_zero, neg_zero], },
    { have : r⁻¹ < 1:= inv_lt_one hr,
      rw [clog, if_neg this.not_le, log, if_pos hr.le, inv_inv] } },
  { rw [clog_of_right_le_zero (inv_nonpos.mpr hrp), log_of_right_le_zero hrp, neg_zero], },
end

lemma log_inv (b : ℕ) (r : R) : log b r⁻¹ = -clog b r :=
by rw [←inv_inv r, clog_inv, neg_neg, inv_inv]

end int
