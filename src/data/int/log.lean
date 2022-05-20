/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import data.nat.log
import algebra.order.floor
import algebra.field_power

/-!
# Integer logarithms in a field with respect to a natural base

This file defines two `ℤ`-valued analogs of the logarithm of `n : R` with base `b : ℕ`:

* `int.log b n`: Lower logarithm, or floor **log**. Greatest `k` such that `↑b^k ≤ n`.
* `int.clog b n`: Upper logarithm, or **c**eil **log**. Least `k` such that `n ≤ ↑b^k`.

## Main results

* For `int.log`:
  * `int.zpow_log_le_self`, `int.lt_zpow_succ_log_self`: the bounds formed by `int.log`,
    `(b : R) ^ log b r ≤ r < (b : R) ^ (log b r + 1)`.
  * `int.zpow_log_le_self`, `int.lt_zpow_succ_log_self`: the bounds formed by `int.log`
  * `int.zpow_le_iff_le_log`: the galois almost-connection
* For `int.clog`:
  * `int.zpow_pred_clog_lt_self`, `int.self_le_zpow_clog`: the bounds formed by `int.log`,
    `(b : R) ^ (clog b r - 1) < r ≤ (b : R) ^ clog b r`.
  * `int.zpow_log_le_self`, `int.lt_zpow_succ_log_self`: the bounds formed by `int.log`
  * `int.le_zpow_iff_clog_le`: the galois almost-connection
* `int.clog_eq_neg_log_inv`: the link between the two definitions

-/
variables {R : Type*} [linear_ordered_field R] [floor_ring R]

namespace int

/-- The greatest power of `b` such that `b ^ log b r ≤ r`. -/
def log (b : ℕ) (r : R) : ℤ :=
if 1 ≤ r then
  nat.log b (nat.floor r)
else
  -nat.clog b (nat.ceil r⁻¹)

@[simp] lemma log_nat_cast (b : ℕ) (n : ℕ) : log b (n : R) = nat.log b n :=
begin
  rw log,
  cases n,
  { simp [nat.log_zero_right] },
  { simp [←nat.cast_succ] }
end

lemma log_of_left_le_one {b : ℕ} (hb : b ≤ 1) (n : R) : log b n = 0 :=
begin
  rw log,
  split_ifs with hn,
  { rw [nat.log_of_left_le_one hb, int.coe_nat_zero] },
  { rw [nat.clog_of_left_le_one hb, int.coe_nat_zero, neg_zero] },
end

lemma log_of_right_le_zero {n : R} (hn : n ≤ 0) (b : ℕ) : log b n = 0 :=
by rw [log, if_neg (hn.trans_lt zero_lt_one).not_le,
    nat.clog_of_right_le_one (le_of_eq_of_le (nat.ceil_eq_zero.mpr $ inv_nonpos.2 hn) zero_le_one),
    int.coe_nat_zero, neg_zero]

lemma zpow_log_le_self (b : ℕ) (r : R) (hn : 1 < b) (hr : 0 < r) :
  (b : R) ^ log b r ≤ r :=
begin
  rw log,
  split_ifs with hr1,
  { refine le_trans _ (nat.floor_le hr.le),
    rw [zpow_coe_nat, ←nat.cast_pow, nat.cast_le],
    exact nat.pow_log_le_self hn (nat.floor_pos.mpr hr1) },
  { have : 1 < r⁻¹,
    { rw not_le at hr1,
      exact one_lt_inv hr hr1, },
    rw [zpow_neg_coe_of_pos _ (nat.clog_pos hn $ nat.one_lt_cast.1 $ this.trans_le (nat.le_ceil _)),
      ← nat.cast_pow],
    apply inv_le_of_inv_le hr,
    refine (nat.le_ceil _).trans (nat.cast_le.2 _),
    exact nat.le_pow_clog hn _ },
end

lemma lt_zpow_succ_log_self (b : ℕ) (r : R) (hn : 1 < b) (hr : 0 < r) :
  r < (b : R) ^ (log b r + 1) :=
begin
  rw log,
  split_ifs with hr1,
  { rw [int.coe_nat_add_one_out, zpow_coe_nat, ←nat.cast_pow],
    apply nat.lt_of_floor_lt,
    exact nat.lt_pow_succ_log_self hn _, },
  { have hcri : 1 < r⁻¹,
    { rw not_le at hr1,
      exact one_lt_inv hr hr1, },
    have : 1 ≤ nat.clog b ⌈r⁻¹⌉₊ :=
      nat.succ_le_of_lt (nat.clog_pos hn $ nat.one_lt_cast.1 $ hcri.trans_le (nat.le_ceil _)),
    rw [neg_add_eq_sub, ←neg_sub, ←int.coe_nat_one, ← int.coe_nat_sub this,
      zpow_neg₀, zpow_coe_nat, lt_inv hr (pow_pos (nat.cast_pos.mpr $ zero_lt_one.trans hn) _),
      ←nat.cast_pow],
    refine nat.lt_ceil.1 _,
    exact (nat.pow_pred_clog_lt_self hn $ nat.one_lt_cast.1 $ hcri.trans_le $ nat.le_ceil _), }
end

@[simp] lemma log_zero_right (b : ℕ) : log b (0 : R) = 0 :=
log_of_right_le_zero le_rfl _

@[simp] lemma log_one_right (b : ℕ) : log b (1 : R) = 0 :=
by rw [log, if_pos le_rfl, nat.floor_one, nat.log_one_right, int.coe_nat_zero]

/-- `zpow b` and `int.log b` (almost) form a Galois connection. -/
lemma zpow_le_iff_le_log {b : ℕ} (hb : 1 < b) {x : ℤ} {y : R} (hy : 0 < y) :
  (b : R) ^ x ≤ y ↔ x ≤ log b y :=
begin
  have h1b' : 1 ≤ (b : R) := by exact_mod_cast hb.le,
  rw log,
  split_ifs,
  { obtain ⟨a, rfl | rfl⟩ := x.eq_coe_or_neg,
    { simp only [zpow_coe_nat, ←nat.cast_pow, ← nat.le_floor_iff hy.le, int.coe_nat_le],
      exact nat.pow_le_iff_le_log hb (nat.floor_pos.mpr h) },
    { have hna : -(a : ℤ) ≤ 0 := neg_nonpos.mpr (int.coe_nat_nonneg _),
      refine iff_of_true _ _,
      { exact (zpow_le_one_of_nonpos h1b' hna).trans h },
      { exact hna.trans (int.coe_nat_nonneg _) } } },
  { obtain ⟨a, rfl | rfl⟩ := x.eq_coe_or_neg,
    { refine iff_of_false (mt (le_trans _) h) (λ ha, _),
      { exact one_le_zpow_of_nonneg h1b' (int.coe_nat_nonneg _)},
      { have := (int.coe_nat_nonneg _).trans ha,
        rw [neg_nonneg, coe_nat_nonpos_iff] at this,
        refine (nat.clog_pos hb _).ne' this,
        have := (one_lt_inv hy (not_le.mp h)).trans_le (nat.le_ceil _),
        rw nat.one_lt_cast at this,
        exact this } },
    { rw [zpow_neg₀, zpow_coe_nat, neg_le_neg_iff, int.coe_nat_le,
        inv_le (pow_pos (zero_lt_one.trans_le h1b') _) hy, ←nat.le_pow_iff_clog_le hb,
        ←nat.cast_pow, nat.ceil_le] }, },
end

/-- The least power of `b` such that `r ≤ b ^ log b r`. -/
def clog (b : ℕ) (r : R) : ℤ :=
if 1 ≤ r then
  nat.clog b (nat.ceil r)
else
  -nat.log b (nat.floor r⁻¹)

@[simp] lemma clog_nat_cast (b : ℕ) (n : ℕ) : clog b (n : R) = nat.clog b n :=
begin
  rw clog,
  cases n,
  { simp [nat.clog_zero_right] },
  { simp [←nat.cast_succ] }
end

lemma clog_of_left_le_one {b : ℕ} (hb : b ≤ 1) (n : R) : clog b n = 0 :=
begin
  rw clog,
  split_ifs with hn,
  { rw [nat.clog_of_left_le_one hb, int.coe_nat_zero] },
  { rw [nat.log_of_left_le_one hb, int.coe_nat_zero, neg_zero] },
end

lemma clog_of_right_le_zero {n : R} (hn : n ≤ 0) (b : ℕ) : clog b n = 0 :=
begin
  rw [clog, if_neg (hn.trans_lt zero_lt_one).not_le, neg_eq_zero, int.coe_nat_eq_zero,
    nat.log_eq_zero_iff],
  cases le_or_lt b 1 with hb hb,
  { exact or.inr hb },
  { refine or.inl (lt_of_le_of_lt _ hb),
    exact nat.floor_le_one_of_le_one ((inv_nonpos.2 hn).trans zero_le_one) },
end

lemma clog_inv (b : ℕ) (r : R) : clog b r⁻¹ = -log b r :=
begin
  cases lt_or_le 0 r with hrp hrp,
  { obtain hr | rfl | hr := lt_trichotomy r 1,
    { have : 1 < r⁻¹ := one_lt_inv hrp hr,
      rw [clog, if_pos this.le, log, if_neg hr.not_le, neg_neg] },
    { rw [inv_one, clog, log, if_pos le_rfl, if_pos le_rfl, nat.ceil_one, nat.floor_one,
        nat.clog_one_right, nat.log_one_right, int.coe_nat_zero, neg_zero], },
    { have : r⁻¹ < 1 := inv_lt_one hr,
      rw [clog, if_neg this.not_le, log, if_pos hr.le, inv_inv] } },
  { rw [clog_of_right_le_zero (inv_nonpos.mpr hrp), log_of_right_le_zero hrp, neg_zero], },
end

lemma log_inv (b : ℕ) (r : R) : log b r⁻¹ = -clog b r :=
by rw [←inv_inv r, clog_inv, neg_neg, inv_inv]

lemma clog_eq_neg_log_inv (b : ℕ) (r : R) : clog b r = -log b r⁻¹ :=
by rw [log_inv, neg_neg]

lemma self_le_zpow_clog (b : ℕ) (r : R) (hn : 1 < b) (hr : 0 < r) :
  r ≤ (b : R) ^ clog b r :=
begin
  rw [clog_eq_neg_log_inv, zpow_neg₀, le_inv hr (zpow_pos_of_pos _ _)],
  { exact zpow_log_le_self _ _ hn (inv_pos.mpr hr), },
  { exact nat.cast_pos.mpr (zero_le_one.trans_lt hn), },
end

lemma zpow_pred_clog_lt_self (b : ℕ) (r : R) (hn : 1 < b) (hr : 0 < r) :
  (b : R) ^ (clog b r - 1) < r :=
begin
  rw [clog_eq_neg_log_inv, ←neg_add', zpow_neg₀, inv_lt (zpow_pos_of_pos _ _) hr],
  { exact lt_zpow_succ_log_self _ _ hn (inv_pos.mpr hr), },
  { exact nat.cast_pos.mpr (zero_le_one.trans_lt hn), },
end

@[simp] lemma clog_zero_right (b : ℕ) : clog b (0 : R) = 0 :=
clog_of_right_le_zero le_rfl _

@[simp] lemma clog_one_right (b : ℕ) : clog b (1 : R) = 0 :=
by rw [clog, if_pos le_rfl, nat.ceil_one, nat.clog_one_right, int.coe_nat_zero]

/--`clog b` and `zpow b` form a Galois connection. -/
lemma le_zpow_iff_clog_le {b : ℕ} (hb : 1 < b) {x : ℤ} {y : R} (hy : 0 < y) :
  y ≤ (b : R) ^ x ↔ clog b y ≤ x :=
begin
  rw [clog_eq_neg_log_inv, neg_le, ←zpow_le_iff_le_log hb (inv_pos.mpr hy), zpow_neg₀,
    inv_le_inv (zpow_pos_of_pos _ _) hy],
  { exact nat.cast_pos.mpr (zero_le_one.trans_lt hb), },
end

end int
