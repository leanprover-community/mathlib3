/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Bhavik Mehta, Patrick Stevens
-/
import algebra.commute
import tactic.linarith

open nat

open_locale big_operators

lemma nat.prime.dvd_choose {p k : ℕ} (hk : 0 < k) (hkp : k < p) (hp : prime p) : p ∣ choose p k :=
have h₁ : p ∣ fact p, from hp.dvd_fact.2 (le_refl _),
have h₂ : ¬p ∣ fact k, from mt hp.dvd_fact.1 (not_le_of_gt hkp),
have h₃ : ¬p ∣ fact (p - k), from mt hp.dvd_fact.1 (not_le_of_gt (nat.sub_lt_self hp.pos hk)),
by rw [← choose_mul_fact_mul_fact (le_of_lt hkp), mul_assoc, hp.dvd_mul, hp.dvd_mul] at h₁;
  exact h₁.resolve_right (not_or_distrib.2 ⟨h₂, h₃⟩)

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
lemma choose_le_middle {r n : ℕ} : nat.choose n r ≤ nat.choose n (n/2) :=
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
  { rw [_root_.pow_zero, sum_range_succ, range_zero, sum_empty, add_zero],
    dsimp [t], rw [choose_self, nat.cast_one, mul_one, mul_one] },
  { rw[sum_range_succ', h_first],
    rw[finset.sum_congr rfl (h_middle n), finset.sum_add_distrib, add_assoc],
    rw[pow_succ (x + y), ih, add_mul, finset.mul_sum, finset.mul_sum],
    congr' 1,
    rw[finset.sum_range_succ', finset.sum_range_succ, h_first, h_last,
       mul_zero, zero_add, _root_.pow_succ] }
end

/-- The binomial theorem-/
theorem add_pow [comm_semiring α] (x y : α) (n : ℕ) :
  (x + y) ^ n = ∑ m in range (n + 1), x ^ m * y ^ (n - m) * choose n m :=
(commute.all x y).add_pow n

/-- The sum of entries in a row of Pascal's triangle -/
theorem sum_range_choose (n : ℕ) :
  ∑ m in range (n + 1), choose n m = 2 ^ n :=
by simpa using (add_pow 1 1 n).symm

/-
Facts about more specific binomial coefficients and their sums
-/

lemma sum_range_split_halfway (f : nat → nat) (m : nat) :
  ∑ i in range (2 * m + 2), f i = (∑ i in range (m + 1), f i) + ∑ i in (Ico (m + 1) (2 * m + 2)), f i :=
begin
  induction m with m,
  {simp, refl},
  {
    rw sum_range_succ f (2 * (m + 1) + 1),
    rw sum_range_succ f (2 * (m + 1)),
    have s : 2 * m + 2 = 2 * (m + 1), refl,
    rw s at m_ih,
    rw m_ih,
    clear m_ih,
    rw sum_range_succ f (m + 1),
    simp,
    rw add_comm (∑ i in range (m + 1), f i) (∑ i in Ico (m + 2) (2 * (m + 1) + 2), f i),
    rw <- add_assoc (f (m + 1)) _ _,
    rw (@sum_eq_sum_Ico_succ_bot _ _ (m + 1) (2 * (m + 1) + 2) ( by linarith ) f).symm,
    rw @sum_Ico_succ_top _ _ m.succ (2 * m.succ + 1) ( by linarith ) f,
    rw @sum_Ico_succ_top _ _ m.succ (2 * m.succ) ( by linarith ) f,
    ring,
  }
end

lemma sum_range_split (f : nat → nat) (m n : nat) (n_le_m : n ≤ m) :
  ∑ i in range m, f i = (∑ i in range n, f i) + ∑ i in (Ico n m), f i :=
begin
  induction m with m,
  {cases n, simp, exfalso, exact not_succ_le_zero n n_le_m},
  {
    cases le_or_lt n m with n_le_m bad,
    {
      rw sum_range_succ f m,
      rw @sum_Ico_succ_top _ _ n m n_le_m f,
      rw m_ih n_le_m,
      ring,
    },
    {
      have n_eq_m : n = m + 1, exact le_antisymm n_le_m bad,
      subst n_eq_m,
      simp,
    },
  }
end

-- This lemma exists only so that we can instantiate it with `i = m + 1`.
private lemma reflect_sum_lemma (i : nat) (m : nat) (i_bound : i ≤ m + 1) (f : nat → nat) (reflects : ∀ x ≤ 2 * m + 1, f x = f (2 * m + 1 - x)) :
  ∑ j in (Ico (m + 1 - i) (m + 1)), f j = ∑ j in Ico (m + 1) (m + 1 + i), f j :=
begin
  induction i with i,
  { simp },
  {
    have t : (m + 1) + (i + 1) = ((m + 1) + i) + 1, norm_num,
    rw t, clear t,
    rw <- (@sum_Ico_succ_top _ _ (m + 1) (m.succ + i) (by exact nat.le.intro rfl) f).symm,
    rw <- i_ih, clear i_ih,
    have t : f (m.succ + i) = f (m - i), by {
      have munge : m + 1 + i ≤ 2 * m + 1,
        calc m.succ + i ≤ m.succ + m : by exact add_le_add_left (nat.lt_succ_iff.mp i_bound) (nat.succ m)
        ... = m + (m + 1): nat.add_comm (m + 1) m
        ...  = (m + m) + 1 : (nat.add_assoc _ _ _).symm
        ... = 2 * m + 1 : by rw two_mul,
      have v : 2 * m + 1 - (m.succ + i) = m - i,
        calc 2 * m + 1 - (m.succ + i) = 2 * m + 1 - m.succ - i : eq.symm (nat.sub_sub (2 * m + 1) (nat.succ m) i)
            ... = m + m + 1 - m.succ - i : by rw <- two_mul m
            ... = m + (m + 1) - m.succ - i : by rw <- add_assoc m m 1
            ... = m - i : by rw nat.add_sub_cancel m m.succ,
      have reflected : f (m + 1 + i) = f (2 * m + 1 - (m + 1 + i)),
        exact reflects (m.succ + i) munge,
      rw v at reflected,
      exact reflected,
    },
    rw t, clear t,
    {
      rw nat.succ_sub (nat.lt_succ_iff.mp i_bound),
      have s : f (m - i) + ∑ j in (Ico (m - i + 1) (m + 1)), f j = ∑ j in (Ico (m - i) (m + 1)), f j,
        exact (@sum_eq_sum_Ico_succ_bot _ _ (m - i) (m + 1) (nat.sub_lt_succ m i) f).symm,
      simp,
      rw <- s,
      ring,
    },
    exact le_of_lt i_bound,
  }
end

lemma sum_range_reflects_halfway (m : nat) (f : nat → nat) (reflects : ∀ x ≤ 2 * m + 1, f x = f (2 * m + 1 - x)) :
  finset.sum (finset.range m.succ) f = finset.sum (finset.Ico (nat.succ m) (2 * m + 2)) f :=
begin
  have r : 2 * m + 2 = 2 * (m + 1), ring,
  rw r,
  simpa [finset.Ico.zero_bot m.succ, two_mul (m + 1)] using (reflect_sum_lemma (m + 1) m (le_refl _) f reflects),
end

private lemma can_halve (a b : nat) (pr : 2 * a = 2 * b) : a = b := by linarith

lemma sum_range_choose_halfway (m : nat) :
  ∑ i in range (m + 1), nat.choose (2 * m + 1) i = 4 ^ m :=
begin
  let e := sum_range_split_halfway (choose (2 * m + 1)) m,
  rw (sum_range_choose (2 * m + 1)) at e,
  have reflects : ∀ x ≤ 2 * m + 1, choose (2 * m + 1) x = choose (2 * m + 1) (2 * m + 1 - x),
  {
    intros x pr,
    exact eq.symm (@choose_symm (2 * m + 1) x pr),
  },
  rw <- (sum_range_reflects_halfway m (choose (2 * m + 1)) reflects) at e,
  simp,
  have tidy_two_pow : 2 ^ (2 * m + 1) = 2 * (4 ^ m),
    calc 2 ^ (2 * m + 1) = 2 ^ (2 * m) * 2 ^ 1 : nat.pow_add 2 (2 * m) 1
      ... = 4 ^ m * 2 ^ 1 : by { rw nat.pow_mul 2 m 2, refl }
      ... = 2 * (4 ^ m) : by ring,
  rw tidy_two_pow at e,
  rw <- two_mul (∑ j in range (m + 1), choose (2 * m + 1) j) at e,
  exact (eq.symm (can_halve (4 ^ m) _ e)),
end

end binomial
