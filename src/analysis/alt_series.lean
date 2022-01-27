/-
Copyright (c) 2022 Dylan MacKenzie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dylan MacKenzie
-/

import analysis.normed_space.basic

open nat filter finset
open_locale big_operators topological_space

/-!
# Convergence of alternating series

An alternating series is an infinite series of the form
$\sum_{k=0}^{\infty} (-1)^n a_n$ or $\sum_{k=0}^{\infty} (-1)^{n+1} a_n$.

The alternating series test states that an alternating series is convergent if
$\lim_{n\to\infty} a_n = 0$ and $a_{n+1} \leq a_n$.
-/

-- Some useful parity lemmas
namespace parity
lemma odd_succ_even {x: ℕ} (hx: odd x) : even x.succ :=
  even_succ.mpr (odd_iff_not_even.mp hx)

lemma neg_one_pow_of_add_even {m n : ℕ} (hm : even m) :
  (-1 : ℝ) ^ (n + m) = (-1 : ℝ) ^ n :=
begin
  obtain hne | hno := even_or_odd n,
  { simp only [neg_one_pow_of_even hne, neg_one_pow_of_even (even.add_even hne hm)] },
  { simp only [neg_one_pow_of_odd hno, neg_one_pow_of_odd (odd.add_even hno hm)] }
end

lemma neg_one_pow_of_even_add {m n : ℕ} (hm : even m) :
  (-1 : ℝ) ^ (m + n) = (-1 : ℝ) ^ n :=
begin
  rw add_comm m n,
  exact neg_one_pow_of_add_even hm,
end
end parity

-- Alternating series

variables {α : Type*} {β : Type*}
variables [add_comm_monoid α] [topological_space α]
variables a f : ℕ → ℝ

/-- A partial sum, $S_k(a) = \sum_0^k a_k$ -/
def partial_sum (k : ℕ) := ∑ n in range k, a n

/-- The partial sum of an alternating series whose first term is positive -/
def alt_partial_sum (k : ℕ) := ∑ n in range k, (-1)^n * a n

/-- The partial sum of an alternating series whose first term is negative -/
def alt_partial_sum' (k : ℕ) := ∑ n in range k, (-1)^n * -(a n)

/-- An analogue of `infinite_sum.has_sum` defined on `range ℕ` to allow for
conditional convergence -/
def has_sum_nat (f : ℕ → α) (a : α) : Prop := tendsto (λ n, ∑ b in range n, f b) at_top (𝓝 a)

/-- An analogue of `infinite_sum.summable` for `has_sum_nat` -/
def summable_nat (f : ℕ → α) := ∃ x, has_sum_nat f x

open parity

lemma summable_nat_iff_cauchy_seq_partial_sum {f : ℕ  → ℝ} :
  summable_nat f ↔ cauchy_seq (λ n, ∑ b in range n, f b) :=
begin
  apply cauchy_map_iff_exists_tendsto.symm,
  exact complete_of_proper,
  exact at_top_ne_bot,
end

lemma alt_partial_sum_nonneg
  (ha_anti : antitone a)
  (ha_nonneg : ∀ n, 0 ≤ a n)
  : ∀ k, 0 ≤ alt_partial_sum a k :=
begin
  intro k,
  unfold alt_partial_sum,
  induction k using nat.case_strong_induction_on with k hk,
    { simp only [sum_empty, ge_iff_le, range_zero] },

  rw sum_range_succ,
  obtain even | odd := even_or_odd k,
  { rw neg_one_pow_of_even even,
    simp only [one_mul, ge_iff_le],

    refine add_nonneg _ _,
    exact hk k (le_refl k),
    exact ha_nonneg k},

  cases k with k,
    { simp, exact ha_nonneg 0 },

  rw sum_range_succ,
  rw [neg_one_pow_of_even _, neg_one_pow_of_odd odd], swap,
    { rwa [odd_iff_not_even, even_succ, not_not] at odd },
  rw [one_mul, neg_one_mul, add_assoc],

  refine add_nonneg _ _,
    { exact hk k (le_of_lt (lt_succ_self k)) },
  simp only [zero_add, le_add_neg_iff_add_le],
  exact ha_anti (le_of_lt (lt_add_one k)),
end

lemma anti_suffix_is_anti {m : ℕ}
  (ha_anti : antitone a) :
  antitone (λ (n : ℕ), a (m + n)) :=
begin
  intros x y hx,
  apply ha_anti,
  linarith,
end

lemma alt_partial_sum_diff_nonneg
  (ha_anti : antitone a)
  (ha_nonneg : ∀ n, 0 ≤ a n)
  : ∀ n m, m ≤ n → even m → 0 ≤ alt_partial_sum a n - alt_partial_sum a m :=
begin
  unfold alt_partial_sum,
  intros n m hmn hm,
  rw [← sum_Ico_eq_sub _ hmn, sum_Ico_eq_sum_range],
  simp only [neg_one_pow_of_even_add hm],
  apply alt_partial_sum_nonneg,
    { exact anti_suffix_is_anti _ ha_anti },
    { intro x, exact ha_nonneg (m + x) },
end

lemma alt_partial_sum_le_first
  (ha_anti : antitone a)
  (ha_nonneg : ∀ n, 0 ≤ a n)
: ∀ k, alt_partial_sum a k ≤ a 0 :=
begin
  intro k,
  unfold alt_partial_sum,

  induction k using nat.case_strong_induction_on with k hk,
    { simp only [sum_empty, range_zero], exact ha_nonneg 0 },

  rw sum_range_succ,
  obtain even | odd := even_or_odd k, swap,
  { rw [neg_one_pow_of_odd odd, neg_one_mul],
    specialize hk k rfl.ge,
    rw add_neg_le_iff_le_add',

    refine le_trans _ (_: a 0 ≤ a k + a 0),
      { exact hk },
    rw [le_add_iff_nonneg_left],
    exact ha_nonneg k },

  rw [neg_one_pow_of_even even, one_mul],

  cases k with k,
    { simp only [sum_empty, range_zero, zero_add] },

  rw sum_range_succ,
  rw neg_one_pow_of_odd, swap,
    { rwa [even_succ, even_iff_not_odd, not_not] at even },
  rw [neg_one_mul, add_assoc, add_comm],
  specialize hk k (le_succ k),
  apply add_le_of_nonpos_of_le _ hk,
  simp only [add_zero, neg_add_le_iff_le_add],
  exact ha_anti (le_of_lt (lt_add_one k)),
end

lemma alt_partial_sum_diff_le_first
  (ha_anti : antitone a)
  (ha_nonneg : ∀ n, 0 ≤ a n)
  : ∀ n m, m ≤ n → even m → alt_partial_sum a n - alt_partial_sum a m ≤ a m :=
begin
  intros n m hmn hm,
  unfold alt_partial_sum,
  rw [← sum_Ico_eq_sub _ hmn, sum_Ico_eq_sum_range],
  simp only [neg_one_pow_of_even_add hm],

  apply alt_partial_sum_le_first _ (anti_suffix_is_anti a ha_anti),
  finish,
end

-- Used to prove `cauchy_seq` for both `a n` and `-(a n)`
@[nolint ge_or_gt] -- see Note [nolint_ge]
lemma alt_partial_sum_is_cau_seq
  (ha_tendsto_zero : tendsto a at_top (𝓝 0))
  (ha_anti : antitone a)
  (ha_nonneg : ∀ (n : ℕ), 0 ≤ a n) :
  ∀ (ε : ℝ),
    ε > 0 →
    (∃ (N : ℕ),
       ∀ (n : ℕ),
         n ≥ N → |alt_partial_sum a n - alt_partial_sum a N| < ε) :=
begin
  intros ε hε,

  -- Convert `tendsto` to `ε`-based definition of limit
  simp_rw [metric.tendsto_at_top, real.dist_0_eq_abs, abs_of_nonneg (ha_nonneg _)]
    at ha_tendsto_zero,
  specialize ha_tendsto_zero ε hε,
  cases ha_tendsto_zero with m ha_tendsto_zero,

  obtain hme | hmo := even_or_odd m,
  { use m,
    intros n hmn,
    rw [abs_of_nonneg (alt_partial_sum_diff_nonneg a ha_anti ha_nonneg n m hmn hme)],
    apply lt_of_le_of_lt (alt_partial_sum_diff_le_first a ha_anti ha_nonneg n m hmn hme) _,
    finish },
  { use (m+1),
    have hm1e : even (m+1) := odd_succ_even hmo,
    intros n hmn,
    rw [abs_of_nonneg (alt_partial_sum_diff_nonneg a ha_anti ha_nonneg n (m+1) hmn hm1e)],
    apply lt_of_le_of_lt (alt_partial_sum_diff_le_first a ha_anti ha_nonneg n (m+1) hmn hm1e) _,
    apply ha_tendsto_zero,
    exact le_succ m },
end

lemma alt_partial_sum_is_cauchy_seq
  (ha_tendsto_zero : tendsto a at_top (𝓝 0))
  (ha_anti : antitone a)
  (ha_nonneg : ∀ n, 0 ≤ a n)
  : cauchy_seq (alt_partial_sum a) :=
begin
  apply metric.cauchy_seq_iff'.mpr, swap,
    { exact has_bot_nonempty ℕ },

  simp only [real.dist_eq],
  exact alt_partial_sum_is_cau_seq a ha_tendsto_zero ha_anti ha_nonneg,
end

lemma alt_partial_sum_is_cauchy_seq'
  (ha_tendsto_zero : tendsto a at_top (𝓝 0))
  (ha_anti : antitone a)
  (ha_nonneg : ∀ n, 0 ≤ a n)
  : cauchy_seq (alt_partial_sum' a) :=
begin
  apply metric.cauchy_seq_iff'.mpr, swap,
    { exact has_bot_nonempty ℕ },

  unfold alt_partial_sum',
  simp only [real.dist_eq, neg_sub_neg, sum_neg_distrib, mul_neg_eq_neg_mul_symm],

  -- For some reason, `simp_rw [abs_sub_comm]` only works on a hypothesis, not the goal
  have hcs := alt_partial_sum_is_cau_seq,
  unfold alt_partial_sum at hcs,
  simp_rw [abs_sub_comm] at hcs,
  exact hcs a ha_tendsto_zero ha_anti ha_nonneg,
end

/-- The alternating series test for a series whose first term is positive -/
theorem alt_partial_sum_is_summable_nat
  (ha_tendsto_zero : tendsto a at_top (𝓝 0))
  (ha_anti : antitone a)
  (ha_nonneg : ∀ n, 0 ≤ a n)
  : summable_nat (λ n, (-1) ^ n * a n) :=
begin
  apply summable_nat_iff_cauchy_seq_partial_sum.mpr,
  exact alt_partial_sum_is_cauchy_seq (λ (n : ℕ), a n) ha_tendsto_zero ha_anti ha_nonneg,
end

/-- The alternating series test for a series whose first term is negative -/
theorem alt_partial_sum_is_summable_nat'
  (ha_tendsto_zero : tendsto a at_top (𝓝 0))
  (ha_anti : antitone a)
  (ha_nonneg : ∀ n, 0 ≤ a n)
  : summable_nat (λ n, (-1) ^ n * -a n) :=
begin
  apply summable_nat_iff_cauchy_seq_partial_sum.mpr,
  exact alt_partial_sum_is_cauchy_seq' (λ (n : ℕ), a n) ha_tendsto_zero ha_anti ha_nonneg,
end
