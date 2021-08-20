/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import data.nat.pow

/-!
# Natural number logarithm

This file defines `log b n`, the logarithm of `n` with base `b`, to be the largest `k` such that
`b ^ k ≤ n`.

-/
namespace nat

/-- `log b n`, is the logarithm of natural number `n` in base `b`. It returns the largest `k : ℕ`
such that `b^k ≤ n`, so if `b^k = n`, it returns exactly `k`. -/
@[pp_nodot] def log (b : ℕ) : ℕ → ℕ
| n :=
  if h : b ≤ n ∧ 1 < b then
    have n / b < n,
      from div_lt_self
        (nat.lt_of_lt_of_le (lt_trans zero_lt_one h.2) h.1) h.2,
    log (n / b) + 1
  else 0

lemma log_eq_zero {b n : ℕ} (hnb : n < b ∨ b ≤ 1) : log b n = 0 :=
begin
  rw [or_iff_not_and_not, not_lt, not_le] at hnb,
  rw [log, ←ite_not, if_pos hnb],
end

lemma log_eq_zero_of_lt {b n : ℕ} (hn : n < b) : log b n = 0 :=
log_eq_zero $ or.inl hn

lemma log_eq_zero_of_le {b n : ℕ} (hb : b ≤ 1) : log b n = 0 :=
log_eq_zero $ or.inr hb

lemma log_zero_eq_zero {b : ℕ} : log b 0 = 0 :=
by { rw log, cases b; refl }

lemma log_one_eq_zero {b : ℕ} : log b 1 = 0 :=
if h : b ≤ 1 then
  log_eq_zero_of_le h
else
  log_eq_zero_of_lt (not_le.mp h)

lemma log_b_zero_eq_zero {n : ℕ} : log 0 n = 0 :=
log_eq_zero_of_le zero_le_one

lemma log_b_one_eq_zero {n : ℕ} : log 1 n = 0 :=
log_eq_zero_of_le rfl.ge

lemma pow_le_iff_le_log (x y : ℕ) {b} (hb : 1 < b) (hy : 1 ≤ y) :
  b^x ≤ y ↔ x ≤ log b y :=
begin
  induction y using nat.strong_induction_on with y ih
    generalizing x,
  rw [log], split_ifs,
  { have h'' : 0 < b := lt_of_le_of_lt (zero_le _) hb,
    cases h with h₀ h₁,
    rw [← nat.sub_le_right_iff_le_add,← ih (y / b),
          le_div_iff_mul_le _ _ h'',← pow_succ'],
    { cases x; simp [h₀,hy] },
    { apply div_lt_self; assumption },
    { rwa [le_div_iff_mul_le _ _ h'',one_mul], } },
  { replace h := lt_of_not_ge (not_and'.1 h hb),
    split; intros h',
    { have := lt_of_le_of_lt h' h,
      apply le_of_succ_le_succ,
      change x < 1, rw [← pow_lt_iff_lt_right hb,pow_one],
      exact this },
    { replace h' := le_antisymm h' (zero_le _),
      rw [h',pow_zero], exact hy} },
end

lemma log_pow (b x : ℕ) (hb : 1 < b) : log b (b ^ x) = x :=
eq_of_forall_le_iff $ λ z,
by { rwa [← pow_le_iff_le_log _ _ hb,pow_le_iff_le_right],
     rw ← pow_zero b, apply pow_le_pow_of_le_right,
     apply lt_of_le_of_lt (zero_le _) hb, apply zero_le }

lemma pow_succ_log_gt_self (b x : ℕ) (hb : 1 < b) (hy : 1 ≤ x) :
  x < b ^ succ (log b x) :=
begin
  apply lt_of_not_ge,
  rw [(≥),pow_le_iff_le_log _ _ hb hy],
  apply not_le_of_lt, apply lt_succ_self,
end

lemma pow_log_le_self (b x : ℕ) (hb : 1 < b) (hx : 1 ≤ x) : b ^ log b x ≤ x :=
by rw [pow_le_iff_le_log _ _ hb hx]

lemma log_le_log_of_le {b n m : ℕ} (h : n ≤ m) : log b n ≤ log b m :=
begin
  cases le_or_lt b 1 with hb hb,
  { rw log_eq_zero_of_le hb, exact zero_le _ },
  { cases nat.eq_zero_or_pos n with hn hn,
    { rw [hn, log_zero_eq_zero], exact zero_le _ },
    { rw ←pow_le_iff_le_log _ _ hb (lt_of_lt_of_le hn h),
      exact (pow_log_le_self b n hb hn).trans h } }
end

lemma log_le_log_succ {b n : ℕ} : log b n ≤ log b n.succ :=
log_le_log_of_le $ le_succ n

lemma log_mono {b : ℕ} : monotone (λ n : ℕ, log b n) :=
monotone_nat_of_le_succ $ λ n, log_le_log_succ

end nat
