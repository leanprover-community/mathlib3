/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import data.nat.basic
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

end nat
