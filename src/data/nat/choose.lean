/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Bhavik Mehta, Patrick Stevens
-/
import tactic.linarith
import tactic.omega
import algebra.big_operators

open nat

open_locale big_operators

lemma nat.prime.dvd_choose_add {p a b : ℕ} (hap : a < p) (hbp : b < p) (h : p ≤ a + b)
  (hp : prime p) : p ∣ choose (a + b) a :=
have h₁ : p ∣ fact (a + b), from hp.dvd_fact.2 h,
have h₂ : ¬p ∣ fact a, from mt hp.dvd_fact.1 (not_le_of_gt hap),
have h₃ : ¬p ∣ fact b, from mt hp.dvd_fact.1 (not_le_of_gt hbp),
by
  rw [← choose_mul_fact_mul_fact (le.intro rfl), mul_assoc, hp.dvd_mul, hp.dvd_mul,
    norm_num.sub_nat_pos (a + b) a b rfl] at h₁;
  exact h₁.resolve_right (not_or_distrib.2 ⟨h₂, h₃⟩)

lemma nat.prime.dvd_choose_self {p k : ℕ} (hk : 0 < k) (hkp : k < p) (hp : prime p) :
  p ∣ choose p k :=
begin
  have r : k + (p - k) = p,
    by rw [← nat.add_sub_assoc (nat.le_of_lt hkp) k, nat.add_sub_cancel_left],
  have e : p ∣ choose (k + (p - k)) k,
    by exact nat.prime.dvd_choose_add hkp (sub_lt (lt.trans hk hkp) hk) (by rw r) hp,
  rwa r at e,
end

/-- Show that choose is increasing for small values of the right argument. -/
lemma choose_le_succ_of_lt_half_left {r n : ℕ} (h : r < n/2) :
  choose n r ≤ choose n (r+1) :=
begin
  refine le_of_mul_le_mul_right _ (nat.lt_sub_left_of_add_lt (lt_of_lt_of_le h (nat.div_le_self n 2))),
  rw ← choose_succ_right_eq,
  apply nat.mul_le_mul_left,
  rw [← nat.lt_iff_add_one_le, nat.lt_sub_left_iff_add_lt, ← mul_two],
  exact lt_of_lt_of_le (mul_lt_mul_of_pos_right h zero_lt_two) (nat.div_mul_le_self n 2),
end

/-- Show that for small values of the right argument, the middle value is largest. -/
private lemma choose_le_middle_of_le_half_left {n r : ℕ} (hr : r ≤ n/2) :
  choose n r ≤ choose n (n/2) :=
decreasing_induction
  (λ _ k a,
      (eq_or_lt_of_le a).elim
        (λ t, t.symm ▸ le_refl _)
        (λ h, trans (choose_le_succ_of_lt_half_left h) (k h)))
  hr (λ _, le_refl _) hr

/-- `choose n r` is maximised when `r` is `n/2`. -/
lemma choose_le_middle (r n : ℕ) : nat.choose n r ≤ nat.choose n (n/2) :=
begin
  cases le_or_gt r n with b b,
  { cases le_or_lt r (n/2) with a h,
    { apply choose_le_middle_of_le_half_left a },
    { rw ← choose_symm b,
      apply choose_le_middle_of_le_half_left,
      rw [div_lt_iff_lt_mul' zero_lt_two] at h,
      rw [le_div_iff_mul_le' zero_lt_two, nat.mul_sub_right_distrib, nat.sub_le_iff,
          mul_two, nat.add_sub_cancel],
      exact le_of_lt h } },
  { rw nat.choose_eq_zero_of_lt b,
    apply nat.zero_le }
end

section binomial
open finset

variables {α : Type*}

/-- A version of the binomial theorem for noncommutative semirings. -/
theorem commute.add_pow [semiring α] {x y : α} (h : commute x y) (n : ℕ) :
  (x + y) ^ n = ∑ m in range (n + 1), x ^ m * y ^ (n - m) * choose n m :=
begin
  let t : ℕ → ℕ → α := λ n m, x ^ m * (y ^ (n - m)) * (choose n m),
  change (x + y) ^ n = ∑ m in range (n + 1), t n m,
  have h_first : ∀ n, t n 0 = y ^ n :=
    λ n, by { dsimp [t], rw[choose_zero_right, nat.cast_one, mul_one, one_mul] },
  have h_last : ∀ n, t n n.succ = 0 :=
    λ n, by { dsimp [t], rw [choose_succ_self, nat.cast_zero, mul_zero] },
  have h_middle : ∀ (n i : ℕ), (i ∈ finset.range n.succ) →
   ((t n.succ) ∘ nat.succ) i = x * (t n i) + y * (t n i.succ) :=
  begin
    intros n i h_mem,
    have h_le : i ≤ n := nat.le_of_lt_succ (finset.mem_range.mp h_mem),
    dsimp [t],
    rw [choose_succ_succ, nat.cast_add, mul_add],
    congr' 1,
    { rw[pow_succ x, succ_sub_succ, mul_assoc, mul_assoc, mul_assoc] },
    { rw[← mul_assoc y, ← mul_assoc y, (h.symm.pow_right i.succ).eq],
      by_cases h_eq : i = n,
      { rw [h_eq, choose_succ_self, nat.cast_zero, mul_zero, mul_zero] },
      { rw[succ_sub (lt_of_le_of_ne h_le h_eq)],
        rw[pow_succ y, mul_assoc, mul_assoc, mul_assoc, mul_assoc] } }
  end,
  induction n with n ih,
  { rw [pow_zero, sum_range_succ, range_zero, sum_empty, add_zero],
    dsimp [t], rw [choose_self, nat.cast_one, mul_one, mul_one] },
  { rw[sum_range_succ', h_first],
    rw[finset.sum_congr rfl (h_middle n), finset.sum_add_distrib, add_assoc],
    rw[pow_succ (x + y), ih, add_mul, finset.mul_sum, finset.mul_sum],
    congr' 1,
    rw[finset.sum_range_succ', finset.sum_range_succ, h_first, h_last,
       mul_zero, zero_add, pow_succ] }
end

/-- The binomial theorem-/
theorem add_pow [comm_semiring α] (x y : α) (n : ℕ) :
  (x + y) ^ n = ∑ m in range (n + 1), x ^ m * y ^ (n - m) * choose n m :=
(commute.all x y).add_pow n

/-- The sum of entries in a row of Pascal's triangle -/
theorem sum_range_choose (n : ℕ) :
  ∑ m in range (n + 1), choose n m = 2 ^ n :=
by simpa using (add_pow 1 1 n).symm

/-!
# Specific facts about binomial coefficients and their sums
-/

lemma sum_range_choose_halfway (m : nat) :
  ∑ i in range (m + 1), nat.choose (2 * m + 1) i = 4 ^ m :=
have ∑ i in range (m + 1), choose (2 * m + 1) (2 * m + 1 - i) =
  ∑ i in range (m + 1), choose (2 * m + 1) i,
from sum_congr rfl $ λ i hi, choose_symm $ by linarith [mem_range.1 hi],
(nat.mul_right_inj zero_lt_two).1 $
calc 2 * (∑ i in range (m + 1), nat.choose (2 * m + 1) i) =
  (∑ i in range (m + 1), nat.choose (2 * m + 1) i) +
    ∑ i in range (m + 1), nat.choose (2 * m + 1) (2 * m + 1 - i) :
  by rw [two_mul, this]
... = (∑ i in range (m + 1), nat.choose (2 * m + 1) i) +
  ∑ i in Ico (m + 1) (2 * m + 2), nat.choose (2 * m + 1) i :
  by { rw [range_eq_Ico, sum_Ico_reflect], { congr, omega }, omega }
... = ∑ i in range (2 * m + 2), nat.choose (2 * m + 1) i : sum_range_add_sum_Ico _ (by omega)
... = 2^(2 * m + 1) : sum_range_choose (2 * m + 1)
... = 2 * 4^m : by { rw [nat.pow_succ, mul_comm, nat.pow_mul], refl }

lemma choose_middle_le_pow (n : ℕ) : choose (2 * n + 1) n ≤ 4 ^ n :=
begin
  have t : choose (2 * n + 1) n ≤ ∑ i in finset.range (n + 1), choose (2 * n + 1) i :=
    finset.single_le_sum (λ x _, by linarith) (finset.self_mem_range_succ n),
  simpa [sum_range_choose_halfway n] using t
end

end binomial
