/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Yaël Dillies
-/
import data.nat.pow
import tactic.by_contra

/-!
# Natural number logarithms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines two `ℕ`-valued analogs of the logarithm of `n` with base `b`:
* `log b n`: Lower logarithm, or floor **log**. Greatest `k` such that `b^k ≤ n`.
* `clog b n`: Upper logarithm, or **c**eil **log**. Least `k` such that `n ≤ b^k`.

These are interesting because, for `1 < b`, `nat.log b` and `nat.clog b` are respectively right and
left adjoints of `nat.pow b`. See `pow_le_iff_le_log` and `le_pow_iff_clog_le`.
-/

namespace nat

/-! ### Floor logarithm -/

/-- `log b n`, is the logarithm of natural number `n` in base `b`. It returns the largest `k : ℕ`
such that `b^k ≤ n`, so if `b^k = n`, it returns exactly `k`. -/
@[pp_nodot] def log (b : ℕ) : ℕ → ℕ
| n :=
  if h : b ≤ n ∧ 1 < b then
    have n / b < n,
      from div_lt_self ((zero_lt_one.trans h.2).trans_le h.1) h.2,
    log (n / b) + 1
  else 0

@[simp] lemma log_eq_zero_iff {b n : ℕ} : log b n = 0 ↔ n < b ∨ b ≤ 1 :=
begin
  rw [log, ite_eq_right_iff],
  simp only [nat.succ_ne_zero, imp_false, decidable.not_and_distrib, not_le, not_lt]
end

lemma log_of_lt {b n : ℕ} (hb : n < b) : log b n = 0 :=
log_eq_zero_iff.2 (or.inl hb)

lemma log_of_left_le_one {b : ℕ} (hb : b ≤ 1) (n) : log b n = 0 :=
log_eq_zero_iff.2 (or.inr hb)

@[simp] lemma log_pos_iff {b n : ℕ} : 0 < log b n ↔ b ≤ n ∧ 1 < b :=
by rw [pos_iff_ne_zero, ne.def, log_eq_zero_iff, not_or_distrib, not_lt, not_le]

lemma log_pos {b n : ℕ} (hb : 1 < b) (hbn : b ≤ n) : 0 < log b n := log_pos_iff.2 ⟨hbn, hb⟩

lemma log_of_one_lt_of_le {b n : ℕ} (h : 1 < b) (hn : b ≤ n) : log b n = log b (n / b) + 1 :=
by { rw log, exact if_pos ⟨hn, h⟩ }

@[simp] lemma log_zero_left : ∀ n, log 0 n = 0 := log_of_left_le_one zero_le_one
@[simp] lemma log_zero_right (b : ℕ) : log b 0 = 0 := log_eq_zero_iff.2 (le_total 1 b)
@[simp] lemma log_one_left : ∀ n, log 1 n = 0 := log_of_left_le_one le_rfl
@[simp] lemma log_one_right (b : ℕ) : log b 1 = 0 := log_eq_zero_iff.2 (lt_or_le _ _)

/-- `pow b` and `log b` (almost) form a Galois connection. See also `nat.pow_le_of_le_log` and
`nat.le_log_of_pow_le` for individual implications under weaker assumptions. -/
lemma pow_le_iff_le_log {b : ℕ} (hb : 1 < b) {x y : ℕ} (hy : y ≠ 0) : b ^ x ≤ y ↔ x ≤ log b y :=
begin
  induction y using nat.strong_induction_on with y ih generalizing x,
  cases x,
  { exact iff_of_true hy.bot_lt (zero_le _) },
  rw log, split_ifs,
  { have b_pos : 0 < b := zero_le_one.trans_lt hb,
    rw [succ_eq_add_one, add_le_add_iff_right, ←ih (y / b) (div_lt_self hy.bot_lt hb)
      (nat.div_pos h.1 b_pos).ne', le_div_iff_mul_le b_pos, pow_succ'] },
  { exact iff_of_false (λ hby, h ⟨(le_self_pow x.succ_ne_zero _).trans hby, hb⟩)
      (not_succ_le_zero _) }
end

lemma lt_pow_iff_log_lt {b : ℕ} (hb : 1 < b) {x y : ℕ} (hy : y ≠ 0) : y < b ^ x ↔ log b y < x :=
lt_iff_lt_of_le_iff_le (pow_le_iff_le_log hb hy)

lemma pow_le_of_le_log {b x y : ℕ} (hy : y ≠ 0) (h : x ≤ log b y) : b ^ x ≤ y :=
begin
  refine (le_or_lt b 1).elim (λ hb, _) (λ hb, (pow_le_iff_le_log hb hy).2 h),
  rw [log_of_left_le_one hb, nonpos_iff_eq_zero] at h,
  rwa [h, pow_zero, one_le_iff_ne_zero]
end

lemma le_log_of_pow_le {b x y : ℕ} (hb : 1 < b) (h : b ^ x ≤ y) : x ≤ log b y :=
begin
  rcases ne_or_eq y 0 with hy | rfl,
  exacts [(pow_le_iff_le_log hb hy).1 h, (h.not_lt (pow_pos (zero_lt_one.trans hb) _)).elim]
end

lemma pow_log_le_self (b : ℕ) {x : ℕ} (hx : x ≠ 0) : b ^ log b x ≤ x :=
pow_le_of_le_log hx le_rfl

lemma log_lt_of_lt_pow {b x y : ℕ} (hy : y ≠ 0) : y < b ^ x → log b y < x :=
lt_imp_lt_of_le_imp_le (pow_le_of_le_log hy)

lemma lt_pow_of_log_lt {b x y : ℕ} (hb : 1 < b) : log b y < x → y < b ^ x :=
lt_imp_lt_of_le_imp_le (le_log_of_pow_le hb)

lemma lt_pow_succ_log_self {b : ℕ} (hb : 1 < b) (x : ℕ) :
  x < b ^ (log b x).succ :=
lt_pow_of_log_lt hb (lt_succ_self _)

lemma log_eq_iff {b m n : ℕ} (h : m ≠ 0 ∨ 1 < b ∧ n ≠ 0) :
  log b n = m ↔ b ^ m ≤ n ∧ n < b ^ (m + 1) :=
begin
  rcases em (1 < b ∧ n ≠ 0) with ⟨hb, hn⟩|hbn,
  { rw [le_antisymm_iff, ← lt_succ_iff, ← pow_le_iff_le_log, ← lt_pow_iff_log_lt, and.comm];
      assumption },
  { have hm : m ≠ 0, from h.resolve_right hbn,
    rw [not_and_distrib, not_lt, ne.def, not_not] at hbn,
    rcases hbn with hb|rfl,
    { simpa only [log_of_left_le_one hb, hm.symm, false_iff, not_and, not_lt]
        using le_trans (pow_le_pow_of_le_one' hb m.le_succ) },
    { simpa only [log_zero_right, hm.symm, false_iff, not_and, not_lt, le_zero_iff, pow_succ]
        using mul_eq_zero_of_right _ } }
end

lemma log_eq_of_pow_le_of_lt_pow {b m n : ℕ} (h₁ : b ^ m ≤ n) (h₂ : n < b ^ (m + 1)) :
  log b n = m :=
begin
  rcases eq_or_ne m 0 with rfl | hm,
  { rw [pow_one] at h₂, exact log_of_lt h₂ },
  { exact (log_eq_iff (or.inl hm)).2 ⟨h₁, h₂⟩ }
end

lemma log_pow {b : ℕ} (hb : 1 < b) (x : ℕ) : log b (b ^ x) = x :=
log_eq_of_pow_le_of_lt_pow le_rfl (pow_lt_pow hb x.lt_succ_self)

lemma log_eq_one_iff' {b n : ℕ} : log b n = 1 ↔ b ≤ n ∧ n < b * b:=
by rw [log_eq_iff (or.inl one_ne_zero), pow_add, pow_one]

lemma log_eq_one_iff {b n : ℕ} : log b n = 1 ↔ n < b * b ∧ 1 < b ∧ b ≤ n :=
log_eq_one_iff'.trans ⟨λ h, ⟨h.2, lt_mul_self_iff.1 (h.1.trans_lt h.2), h.1⟩, λ h, ⟨h.2.2, h.1⟩⟩

lemma log_mul_base {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) : log b (n * b) = log b n + 1 :=
begin
  apply log_eq_of_pow_le_of_lt_pow; rw [pow_succ'],
  exacts [mul_le_mul_right' (pow_log_le_self _ hn) _,
    (mul_lt_mul_right (zero_lt_one.trans hb)).2 (lt_pow_succ_log_self hb _)]
end

lemma pow_log_le_add_one (b : ℕ) : ∀ x, b ^ log b x ≤ x + 1
| 0 := by rw [log_zero_right, pow_zero]
| (x + 1) := (pow_log_le_self b x.succ_ne_zero).trans (x + 1).le_succ

lemma log_monotone {b : ℕ} : monotone (log b) :=
begin
  refine monotone_nat_of_le_succ (λ n, _),
  cases le_or_lt b 1 with hb hb,
  { rw log_of_left_le_one hb, exact zero_le _ },
  { exact le_log_of_pow_le hb (pow_log_le_add_one _ _) }
end

@[mono] lemma log_mono_right {b n m : ℕ} (h : n ≤ m) : log b n ≤ log b m :=
log_monotone h

@[mono] lemma log_anti_left {b c n : ℕ} (hc : 1 < c) (hb : c ≤ b) : log b n ≤ log c n :=
begin
  rcases eq_or_ne n 0 with rfl | hn, { rw [log_zero_right, log_zero_right] },
  apply le_log_of_pow_le hc,
  calc c ^ log b n ≤ b ^ log b n : pow_le_pow_of_le_left' hb _
               ... ≤ n           : pow_log_le_self _ hn
end

lemma log_antitone_left {n : ℕ} : antitone_on (λ b, log b n) (set.Ioi 1) :=
λ _ hc _ _ hb, log_anti_left (set.mem_Iio.1 hc) hb

@[simp] lemma log_div_base (b n : ℕ) : log b (n / b) = log b n - 1 :=
begin
  cases le_or_lt b 1 with hb hb,
  { rw [log_of_left_le_one hb, log_of_left_le_one hb, nat.zero_sub] },
  cases lt_or_le n b with h h,
  { rw [div_eq_of_lt h, log_of_lt h, log_zero_right] },
  rw [log_of_one_lt_of_le hb h, add_tsub_cancel_right]
end

@[simp] lemma log_div_mul_self (b n : ℕ) : log b (n / b * b) = log b n :=
begin
  cases le_or_lt b 1 with hb hb,
  { rw [log_of_left_le_one hb, log_of_left_le_one hb] },
  cases lt_or_le n b with h h,
  { rw [div_eq_of_lt h, zero_mul, log_zero_right, log_of_lt h] },
  rw [log_mul_base hb (nat.div_pos h (zero_le_one.trans_lt hb)).ne', log_div_base,
    tsub_add_cancel_of_le (succ_le_iff.2 $ log_pos hb h)]
end

private lemma add_pred_div_lt {b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) : (n + b - 1) / b < n :=
begin
  rw [div_lt_iff_lt_mul (zero_lt_one.trans hb), ←succ_le_iff, ←pred_eq_sub_one,
    succ_pred_eq_of_pos (add_pos (zero_lt_one.trans hn) (zero_lt_one.trans hb))],
  exact add_le_mul hn hb,
end

/-! ### Ceil logarithm -/

/-- `clog b n`, is the upper logarithm of natural number `n` in base `b`. It returns the smallest
`k : ℕ` such that `n ≤ b^k`, so if `b^k = n`, it returns exactly `k`. -/
@[pp_nodot] def clog (b : ℕ) : ℕ → ℕ
| n :=
  if h : 1 < b ∧ 1 < n then
    have (n + b - 1)/b < n := add_pred_div_lt h.1 h.2,
    clog ((n + b - 1)/b) + 1
  else 0

lemma clog_of_left_le_one {b : ℕ} (hb : b ≤ 1) (n : ℕ) : clog b n = 0 :=
by rw [clog, if_neg (λ h : 1 < b ∧ 1 < n, h.1.not_le hb)]

lemma clog_of_right_le_one {n : ℕ} (hn : n ≤ 1) (b : ℕ) : clog b n = 0 :=
by rw [clog, if_neg (λ h : 1 < b ∧ 1 < n, h.2.not_le hn)]

@[simp] lemma clog_zero_left (n : ℕ) : clog 0 n = 0 :=
clog_of_left_le_one zero_le_one _

@[simp] lemma clog_zero_right (b : ℕ) : clog b 0 = 0 :=
clog_of_right_le_one zero_le_one _

@[simp] lemma clog_one_left (n : ℕ) : clog 1 n = 0 :=
clog_of_left_le_one le_rfl _

@[simp] lemma clog_one_right (b : ℕ) : clog b 1 = 0 :=
clog_of_right_le_one le_rfl _

lemma clog_of_two_le {b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) :
  clog b n = clog b ((n + b - 1)/b) + 1 :=
by rw [clog, if_pos (⟨hb, hn⟩ : 1 < b ∧ 1 < n)]

lemma clog_pos {b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) : 0 < clog b n :=
by { rw clog_of_two_le hb hn, exact zero_lt_succ _ }

lemma clog_eq_one {b n : ℕ} (hn : 2 ≤ n) (h : n ≤ b) : clog b n = 1 :=
begin
  rw [clog_of_two_le (hn.trans h) hn, clog_of_right_le_one],
  have n_pos : 0 < n := zero_lt_two.trans_le hn,
  rw [←lt_succ_iff, nat.div_lt_iff_lt_mul (n_pos.trans_le h), ←succ_le_iff,
    ←pred_eq_sub_one, succ_pred_eq_of_pos (add_pos n_pos (n_pos.trans_le h)), succ_mul, one_mul],
  exact add_le_add_right h _,
end

/--`clog b` and `pow b` form a Galois connection. -/
lemma le_pow_iff_clog_le {b : ℕ} (hb : 1 < b) {x y : ℕ} : x ≤ b ^ y ↔ clog b x ≤ y :=
begin
  induction x using nat.strong_induction_on with x ih generalizing y,
  cases y,
  { rw [pow_zero],
    refine ⟨λ h, (clog_of_right_le_one h b).le, _⟩,
    simp_rw ←not_lt,
    contrapose!,
    exact clog_pos hb },
  have b_pos : 0 < b := zero_lt_two.trans_le hb,
  rw clog, split_ifs,
  { rw [succ_eq_add_one, add_le_add_iff_right, ←ih ((x + b - 1)/b) (add_pred_div_lt hb h.2),
      nat.div_le_iff_le_mul_add_pred b_pos,
      ← pow_succ, add_tsub_assoc_of_le (nat.succ_le_of_lt b_pos), add_le_add_iff_right] },
  { exact iff_of_true ((not_lt.1 (not_and.1 h hb)).trans $ succ_le_of_lt $ pow_pos b_pos _)
    (zero_le _) }
end

lemma pow_lt_iff_lt_clog {b : ℕ} (hb : 1 < b) {x y : ℕ} : b ^ y < x ↔ y < clog b x :=
lt_iff_lt_of_le_iff_le (le_pow_iff_clog_le hb)

lemma clog_pow (b x : ℕ) (hb : 1 < b) : clog b (b ^ x) = x :=
eq_of_forall_ge_iff $ λ z,
by { rw ←le_pow_iff_clog_le hb, exact (pow_right_strict_mono hb).le_iff_le }

lemma pow_pred_clog_lt_self {b : ℕ} (hb : 1 < b) {x : ℕ} (hx : 1 < x) :
  b ^ (clog b x).pred < x :=
begin
  rw [←not_le, le_pow_iff_clog_le hb, not_le],
  exact pred_lt (clog_pos hb hx).ne',
end

lemma le_pow_clog {b : ℕ} (hb : 1 < b) (x : ℕ) : x ≤ b ^ clog b x :=
(le_pow_iff_clog_le hb).2 le_rfl

@[mono] lemma clog_mono_right (b : ℕ) {n m : ℕ} (h : n ≤ m) : clog b n ≤ clog b m :=
begin
  cases le_or_lt b 1 with hb hb,
  { rw clog_of_left_le_one hb, exact zero_le _ },
  { rw ←le_pow_iff_clog_le hb,
    exact h.trans (le_pow_clog hb _) }
end

@[mono] lemma clog_anti_left {b c n : ℕ} (hc : 1 < c) (hb : c ≤ b) : clog b n ≤ clog c n :=
begin
  rw ← le_pow_iff_clog_le (lt_of_lt_of_le hc hb),
  calc
    n ≤ c ^ clog c n : le_pow_clog hc _
  ... ≤ b ^ clog c n : pow_le_pow_of_le_left (zero_lt_one.trans hc).le hb _
end

lemma clog_monotone (b : ℕ) : monotone (clog b) :=
λ x y, clog_mono_right _

lemma clog_antitone_left {n : ℕ} : antitone_on (λ b : ℕ, clog b n) (set.Ioi 1) :=
λ _ hc _ _ hb, clog_anti_left (set.mem_Iio.1 hc) hb

lemma log_le_clog (b n : ℕ) : log b n ≤ clog b n :=
begin
  obtain hb | hb := le_or_lt b 1,
  { rw log_of_left_le_one hb,
    exact zero_le _},
  cases n,
  { rw log_zero_right,
    exact zero_le _},
  exact (pow_right_strict_mono hb).le_iff_le.1 ((pow_log_le_self b n.succ_ne_zero).trans $
    le_pow_clog hb _),
end

end nat
