/-
Copyright (c) 2021 Thomas Bloom, Alex Kontorovich, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bloom, Alex Kontorovich, Bhavik Mehta
-/

import analysis.special_functions.integrals
import analysis.special_functions.pow
import number_theory.arithmetic_function

noncomputable theory

open_locale big_operators
open real set

/--
Given a function `a : ℕ → M` from the naturals into an additive commutative monoid, this expresses
∑ 1 ≤ n ≤ x, a(n).
-/
-- BM: Formally I wrote this as the sum over the naturals in the closed interval `[1, ⌊x⌋]`.
-- The version in the notes uses sums from 1, mathlib typically uses sums from zero - hopefully
-- this difference shouldn't cause serious issues
def summatory {M : Type*} [add_comm_monoid M] (a : ℕ → M) (x : ℝ) : M :=
∑ n in finset.Icc 1 ⌊x⌋₊, a n

lemma summatory_nat {M : Type*} [add_comm_monoid M] (a : ℕ → M) (n : ℕ) :
  summatory a n = ∑ i in finset.Icc 1 n, a i :=
by simp only [summatory, nat.floor_coe]

lemma summatory_eq_floor {M : Type*} [add_comm_monoid M] (a : ℕ → M) (x : ℝ) :
  summatory a x = summatory a ⌊x⌋₊ :=
by rw [summatory, summatory, nat.floor_coe]

lemma summatory_eq_of_Ico {M : Type*} [add_comm_monoid M] (a : ℕ → M) {n : ℕ} {x : ℝ}
  (hx : x ∈ Ico (n : ℝ) (n + 1)) :
  summatory a x = summatory a n :=
by rw [summatory_eq_floor, nat.floor_eq_on_Ico' _ _ hx]

lemma summatory_eq_of_lt_one {M : Type*} [add_comm_monoid M] (a : ℕ → M) {x : ℝ} (hx : x < 1) :
  summatory a x = 0 :=
begin
  rw [summatory, finset.Icc_eq_empty_of_lt, finset.sum_empty],
  rwa [nat.floor_lt' one_ne_zero, nat.cast_one],
end

@[simp] lemma summatory_zero {M : Type*} [add_comm_monoid M] (a : ℕ → M) : summatory a 0 = 0 :=
summatory_eq_of_lt_one _ zero_lt_one

@[simp] lemma summatory_one {M : Type*} [add_comm_monoid M] (a : ℕ → M) : summatory a 1 = a 1 :=
by simp [summatory]

lemma summatory_succ_sub {M : Type*} [add_comm_group M] (a : ℕ → M) (n : ℕ) :
  a (n + 1) = summatory a (n + 1) - summatory a n :=
begin
  rw [←nat.cast_add_one, summatory_nat, summatory_nat, ←nat.Ico_succ_right,
    finset.sum_Ico_succ_top, nat.Ico_succ_right, add_sub_cancel'],
  simp,
end

lemma summatory_eq_sub {M : Type*} [add_comm_group M] (a : ℕ → M) :
  ∀ n, n ≠ 0 → a n = summatory a n - summatory a (n - 1)
| 0 h := (h rfl).elim
| (n+1) _ := by simpa using summatory_succ_sub a n

lemma abs_summatory_le_sum {M : Type*} [semi_normed_group M] (a : ℕ → M) {x : ℝ} :
  ∥summatory a x∥ ≤ ∑ i in finset.Icc 1 ⌊x⌋₊, ∥a i∥ :=
norm_sum_le _ _

-- BM note to self, this might be useful
-- lemma sum_integral_adjacent_intervals {a : ℕ → α} {n : ℕ}

-- lemma restrict_congr_set (h : s =ᵐ[μ] t) : μ.restrict s = μ.restrict t :=

example {f : ℝ → ℂ} (c : ℂ) (hx : measure_theory.integrable f) :
  measure_theory.integrable (λ x, c * f x) :=
begin
  apply measure_theory.integrable.smul c hx,
  -- library_search,
end

lemma partial_summation_integrable {𝕜 : Type*} [is_R_or_C 𝕜] (a : ℕ → 𝕜) (f : ℝ → 𝕜) (N : ℕ)
  (hf' : interval_integrable f measure_theory.measure_space.volume 1 (N + 1)) :
  interval_integrable (λ x, summatory a x * f x) measure_theory.measure_space.volume 1 (N + 1) :=
begin
  suffices : ∀ k < N,
    interval_integrable (summatory a * f) measure_theory.measure_space.volume (k+1) ((k+1)+1),
  { convert interval_integrable.trans_iterate this using 1,
    simp only [nat.cast_zero, zero_add] },
  intros i hi,
  rw interval_integrable_iff_integrable_Ioc_of_le ((le_add_iff_nonneg_right (i+1:ℝ)).2 zero_le_one),
  rw interval_integrable_iff_integrable_Ioc_of_le at hf',
  refine measure_theory.integrable_on.congr_set_ae _ measure_theory.Ico_ae_eq_Ioc.symm,
  have : eq_on (λ x, summatory a (i + 1) * f x) (summatory a * f) (Ico (i + 1) (i + 1 + 1)),
  { intros x hx,
    simp only [pi.mul_apply],
    rw ←nat.cast_add_one at hx,
    rw [summatory_eq_of_Ico _ hx, nat.cast_add_one] },
  refine measure_theory.integrable_on.congr_fun _ this _,
  refine measure_theory.integrable_on.congr_set_ae _ measure_theory.Ico_ae_eq_Ioc,
  have : Ioc (i + 1 : ℝ) (i + 1 + 1) ⊆ Ioc 1 (N+1),
  { apply Ioc_subset_Ioc,
    { simp only [le_add_iff_nonneg_left, nat.cast_nonneg] },
    simp only [←nat.cast_add_one, nat.cast_le, add_le_add_iff_right],
    rwa nat.succ_le_iff },
  have := measure_theory.integrable_on.mono_set hf' this,
  convert measure_theory.integrable.smul (summatory a (i + 1)) this,
  apply measurable_set_Ico,
  simp only [le_add_iff_nonneg_left, nat.cast_nonneg],
end

lemma partial_summation_integrable_real {𝕜 : Type*} [is_R_or_C 𝕜] (a : ℕ → 𝕜) {f : ℝ → 𝕜} {x : ℝ}
  (hf' : interval_integrable f measure_theory.measure_space.volume 1 x) (hx : 1 ≤ x) :
  interval_integrable (λ y, summatory a y * f y) measure_theory.measure_space.volume 1 x :=
begin
  have one_le_fx : 1 ≤ ⌊x⌋₊,
  { apply nat.le_floor,
    rwa [nat.cast_one] },
  have := partial_summation_integrable a f (⌊x⌋₊ - 1),
  rw [nat.cast_sub one_le_fx, nat.cast_one, sub_add_cancel] at this,
  have i_subset : interval 1 ↑⌊x⌋₊ ⊆ interval 1 x,
  { apply interval_subset_interval_left,
    rw [interval_of_le hx],
    refine ⟨_, _⟩,
    { rw [nat.one_le_cast],
      apply nat.le_floor,
      rwa [nat.cast_one] },
    refine nat.floor_le (zero_le_one.trans hx) },
  apply (this (hf'.mono_set i_subset)).trans,
  rw interval_integrable_iff_integrable_Ioc_of_le (nat.floor_le (zero_le_one.trans hx)),
  refine measure_theory.integrable_on.congr_set_ae _ measure_theory.Ico_ae_eq_Ioc.symm,
  have : eq_on (λ y, summatory a ⌊x⌋₊ * f y) (λ y, summatory a y * f y) (Ico ⌊x⌋₊ x),
  { intros y hy,
    dsimp,
    rw [summatory_eq_floor _ y, eq_comm],
    congr' 2,
    apply nat.floor_eq_on_Ico',
    refine ⟨hy.1, hy.2.trans _⟩,
    apply nat.lt_floor_add_one },
  refine measure_theory.integrable_on.congr_fun _ this measurable_set_Ico,
  refine measure_theory.integrable_on.congr_set_ae _ measure_theory.Ico_ae_eq_Ioc,
  rw interval_integrable_iff_integrable_Ioc_of_le hx at hf',
  apply measure_theory.integrable.smul (summatory a ⌊x⌋₊) (hf'.mono_set _),
  apply Ioc_subset_Ioc_left,
  rw nat.one_le_cast,
  apply nat.le_floor,
  rwa nat.cast_one,
end

/-- A version of partial summation where the upper bound is a natural number, useful to prove the
general case. -/
theorem partial_summation_nat {𝕜 : Type*} [is_R_or_C 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜)
  {N : ℕ} (hN : 1 ≤ N)
  (hf : ∀ i ∈ Icc (1:ℝ) N, has_deriv_at f (f' i) i)
  (hf' : interval_integrable f' measure_theory.measure_space.volume 1 N) :
  ∑ n in finset.Icc 1 N, a n * f n =
    summatory a N * f N - ∫ t in 1..N, summatory a t * f' t :=
begin
  rw ←nat.Ico_succ_right,
  induction N with N ih,
  { simpa only [le_zero_iff] using hN },
  rcases N.eq_zero_or_pos with rfl | hN,
  { simp },
  have hN' : (N : ℝ) ∈ interval (1:ℝ) (N+1),
  { simpa only [zero_le_one, nat.one_le_cast, and_true, le_add_iff_nonneg_right, interval_of_le,
      le_add_iff_nonneg_left, nat.cast_nonneg, mem_Icc] using hN },
  simp only [nat.cast_succ] at *,
  rw [finset.sum_Ico_succ_top nat.succ_pos', ih hN, add_comm, nat.succ_eq_add_one,
    summatory_succ_sub a, sub_mul, sub_add_eq_add_sub, eq_sub_iff_add_eq, add_sub_assoc, add_assoc,
    nat.cast_add_one, add_right_eq_self, sub_add_eq_add_sub, sub_eq_zero, add_comm, ←add_sub_assoc,
    ←sub_add_eq_add_sub, ←eq_sub_iff_add_eq, interval_integral.integral_interval_sub_left,
    ←mul_sub],
  { have : ∀ᵐ (x : ℝ), x ∈ interval_oc (N:ℝ) (N+1) → summatory a x * f' x = summatory a N * f' x,
    { rw [interval_oc_of_le ((le_add_iff_nonneg_right (N:ℝ)).2 zero_le_one)],
      refine (measure_theory.Ico_ae_eq_Ioc : Ico (N:ℝ) (N+1) =ᵐ[_] Ioc _ _).symm.mem_iff.mono _,
      intros x hx' hx,
      rw [summatory_eq_floor, nat.floor_eq_on_Ico' _ _ (hx'.1 hx)] },
    rw [interval_integral.integral_congr_ae this, interval_integral.integral_const_mul,
      interval_integral.integral_eq_sub_of_has_deriv_at],
    { intros x hx,
      apply hf,
      rw ←interval_of_le,
      { exact interval_subset_interval_right hN' hx },
      simp only [le_add_iff_nonneg_left, nat.cast_nonneg] },
    refine hf'.mono_set (interval_subset_interval_right hN') },
  { apply partial_summation_integrable _ _ _ hf' },
  { apply (partial_summation_integrable _ _ _ hf').mono_set (interval_subset_interval_left hN') },
  { intros x hx,
    apply hf _ ⟨hx.1, hx.2.trans _⟩,
    simp only [zero_le_one, le_add_iff_nonneg_right] },
  { apply hf'.mono_set (interval_subset_interval_left hN') }
end

-- BM: I think this can be made stronger by taking a weaker assumption on `f`, maybe something like
-- the derivative is integrable on intervals contained in [1,x]?
-- (and then probably have a corollary where it's enough for the derivative to be integrable on
-- [1, +inf) for convenience's sake)
-- I also think this might be necessary to make this change in order to apply this lemma to things
-- like `f(x) = 1/x`, since that's not cont diff at 0.
theorem partial_summation {𝕜 : Type*} [is_R_or_C 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜) {x : ℝ}
  (hf : ∀ i ∈ Icc (1:ℝ) x, has_deriv_at f (f' i) i)
  (hf' : interval_integrable f' measure_theory.measure_space.volume 1 x) :
  summatory (λ n, a n * f n) x = summatory a x * f x - ∫ t in 1..x, summatory a t * f' t :=
begin
  cases lt_or_le x 1,
  { rw [summatory_eq_of_lt_one _ h, summatory_eq_of_lt_one _ h, zero_mul, zero_sub, zero_eq_neg,
      interval_integral.integral_of_ge h.le, neg_eq_zero,
      interval_integral.integral_Ioc_eq_integral_Ioo, measure_theory.set_integral_congr,
      measure_theory.integral_zero],
    { apply measurable_set_Ioo },
    intros y hy,
    dsimp,
    rw [summatory_eq_of_lt_one _ hy.2, zero_mul] },
  have hx : ↑⌊x⌋₊ ∈ interval 1 x,
  { rw [interval_of_le h, mem_Icc, nat.one_le_cast],
    refine ⟨nat.le_floor _, nat.floor_le (le_trans zero_le_one h)⟩,
    rwa nat.cast_one },
  have hI : interval 1 ↑⌊x⌋₊ ⊆ interval 1 x,
  { apply interval_subset_interval_left hx },
  rw [summatory, partial_summation_nat a f f'],
  { rw [eq_comm, sub_eq_sub_iff_sub_eq_sub, interval_integral.integral_interval_sub_left],
    { have : ∀ y ∈ interval_oc (⌊x⌋₊:ℝ) x, summatory a y * f' y = summatory a ⌊x⌋₊ * f' y,
      { intros y hy,
        rw interval_oc_of_le (nat.floor_le (zero_le_one.trans h)) at hy,
        rw summatory_eq_floor,
        congr' 3,
        rw nat.floor_eq_on_Ico,
        exact ⟨hy.1.le, hy.2.trans_lt (nat.lt_floor_add_one _)⟩ },
      rw [interval_integral.integral_congr_ae (filter.eventually_of_forall this),
        interval_integral.integral_const_mul, summatory_eq_floor, ←mul_sub,
        interval_integral.integral_eq_sub_of_has_deriv_at],
      { intros y hy,
        apply hf,
        rw ←interval_of_le h,
        apply interval_subset_interval_right hx hy },
      apply hf'.mono_set,
      apply interval_subset_interval_right hx },
    exact partial_summation_integrable_real a hf' h,
    apply (partial_summation_integrable_real a hf' h).mono_set hI },
  { apply nat.le_floor,
    rwa [nat.cast_one] },
  { intros i hi,
    apply hf _ ⟨hi.1, hi.2.trans (nat.floor_le (le_trans zero_le_one h))⟩ },
  apply hf'.mono_set hI,
end

-- BM: A definition of the Euler-Mascheroni constant
-- Maybe a different form is a better definition, and in any case it would be nice to show the
-- different definitions are equivalent.
-- This version uses an integral over an infinite interval, which in mathlib is *not* defined
-- as the limit of integrals over finite intervals, but there is a result saying they are equal:
-- see measure_theory.integral.integral_eq_improper: `interval_integral_tendsto_integral_Ioi`
def euler_mascheroni : ℝ := 1 - ∫ t in Ioi 1, int.fract t / t^2

-- vinogradov notation to state things more nicely
-- probably this should be generalised to not be just for ℝ, but I think this works for now
def vinogradov (f : ℝ → ℝ) (g : ℝ → ℝ) : Prop := asymptotics.is_O f g filter.at_top

open filter asymptotics

infix ` ≪ `:50 := vinogradov
-- BM: might want to localise this notation
-- in the measure_theory locale it's used for absolute continuity of measures

-- lemma harmonic_series_estimate :
--   ∃ (g : ℝ → ℝ), is_O g (λ x, x⁻¹) at_top ∧
--     ∀ x, summatory (λ n, (n : ℝ)⁻¹) x = log x + euler_mascheroni + g x :=
-- begin
--   refine ⟨sorry, sorry, λ x, _⟩,
--   have : ∀ x, summatory (λ _, 1) x = ⌊x⌋₊,
--   { intro x,
--     rw [summatory, ←finset.card_eq_sum_ones, nat.card_Icc],
--     refl },
--   have : (∀ (i ∈ Icc 1 x), has_deriv_at (λ y, y ^ (-1:ℤ)) (-i ^ (-2:ℤ)) i),
--   { intros i hi,
--     simpa only [neg_mul_eq_neg_mul_symm, one_mul, int.cast_one, int.cast_neg]
--       using has_deriv_at_zpow (-1) i (or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one hi.1))), },
--   have : (0:ℝ) ≤ -2 ∨ (0:ℝ) ∉ interval 1 x,
--   { right,

--   },
--   have := partial_summation (λ _, (1 : ℝ)) _ _ this
--             (interval_integral.interval_integrable_zpow _).neg,
--   simp only [zpow_neg₀, one_mul, interval_integral.integral_neg, zpow_one, mul_neg_eq_neg_mul_symm,
--     sub_neg_eq_add] at this,
--   rw this,

--   -- simp only [one_div],
-- end

--   is_O (λ x, summatory (λ i, (1 : ℝ) / i) x - log x - euler_mascheroni) (λ x, 1 / x) at_top
--   :=
-- begin
-- end

-- lemma harmonic_series_vinogradov :
--   is_O (λ x, summatory (λ i, (1 : ℝ) / i) x - log x - euler_mascheroni) (λ x, 1 / x) at_top :=
-- begin
--   have : ∀ x, summatory (λ _, 1) x = ⌊x⌋₊,
--   { intro x,
--     rw [summatory, ←finset.card_eq_sum_ones, nat.card_Icc],
--     refl },
--   have : (∀ (i : ℝ), 0 < i → has_deriv_at (λ x, x ^ (-1:ℤ)) (-i ^ (-2:ℤ)) i),
--   { intros i hi,
--     simpa only [neg_mul_eq_neg_mul_symm, one_mul, int.cast_one, int.cast_neg]
--       using has_deriv_at_zpow (-1) i (or.inl hi.ne') },
--   have := partial_summation (λ _, 1) (λ x, x ^ (-1 : ℤ)) (λ x, - x ^ (-2 : ℤ)),
-- end

lemma summatory_log :
  (λ x, summatory (λ i, log i) x - x * log x) ≪ log :=
sorry

namespace nat.arithmetic_function
open_locale arithmetic_function

lemma pow_zero_eq_zeta :
  pow 0 = ζ :=
begin
  ext i,
  simp,
end

lemma sigma_zero_eq_zeta_mul_zeta :
  σ 0 = ζ * ζ :=
by rw [←zeta_mul_pow_eq_sigma, pow_zero_eq_zeta]

lemma sigma_zero_apply_eq_sum_divisors {i : ℕ} :
  σ 0 i = ∑ d in i.divisors, 1 :=
begin
  rw [sigma_apply, finset.sum_congr rfl],
  intros x hx,
  apply pow_zero,
end

lemma sigma_zero_apply_eq_card_divisors {i : ℕ} :
  σ 0 i = i.divisors.card :=
 by rw [sigma_zero_apply_eq_sum_divisors, finset.card_eq_sum_ones]

-- BM: Bounds like these make me tempted to define a relation
-- `equal_up_to p f g` to express that `f - g ≪ p` (probably stated `f - g = O(p)`) and show that
-- (for fixed p) this is an equivalence relation, and that it is increasing in `p`
-- Perhaps this would make it easier to express the sorts of calculations that are common in ANT,
-- especially ones like
-- f₁ = f₂ + O(p)
--    = f₃ + O(p)
--    = f₄ + O(p)
-- since this is essentially using transitivity of `equal_up_to p` three times
lemma hyperbola :
  (λ x, summatory (λ i, σ 0 i) x - x * log x - (2 * euler_mascheroni - 1) * x) ≪ sqrt :=
sorry

-- BM: This might need a lower bound on `n`, maybe just `1 ≤ n` is good enough?
lemma divisor_bound :
  ∃ (g : ℝ → ℝ), g ≪ (λ i, 1 / log (log i)) ∧
    ∀ (n : ℕ), (σ 0 n : ℝ) ≤ n ^ g n :=
sorry

-- BM: Might also need a lower bound on `n`?
lemma weak_divisor_bound (ε : ℝ) (hε : 0 < ε) :
  ∃ C, 0 < C ∧ ∀ n, (σ 0 n : ℝ) ≤ C * (n : ℝ)^ε :=
sorry

lemma big_O_divisor_bound (ε : ℝ) (hε : 0 < ε) :
  asymptotics.is_O (λ n, (σ 0 n : ℝ)) (λ n, (n : ℝ)^ε) filter.at_top :=
sorry

-- BM: I have this defined in another branch, coming to mathlib soon
def von_mangoldt : nat.arithmetic_function ℝ := sorry
localized "notation `Λ` := von_mangoldt" in arithmetic_function

-- BM: this is equivalent to `is_O (λ x, x) (summatory Λ) at_top` (ie the same thing in Landau
-- notation) but the proof gives an explicit bound? So we can show something like
-- `is_O_with c (λ x, x) (summatory Λ) at_top`, with a nice constant `c` (I think the proof I have
-- gives something like c = log 2?)
-- Similarly there's a "for sufficiently large x" hidden in here, we could try to remove that too?
-- Then the statement would be something like
-- lemma explicit_chebyshev_lower (x : ℕ) (hx : x₀ ≤ x) :
--    x ≤ log 2 * summatory Λ x :=
-- which could be helpful
lemma chebyshev_lower :
  (λ x, x) ≪ summatory Λ :=
sorry

-- BM: As above, with c = 2 log 2?
lemma chebyshev_upper :
  summatory Λ ≪ (λ x, x) :=
sorry

/--
Given a function `a : ℕ → M` from the naturals into an additive commutative monoid, this expresses
∑ 1 ≤ p ≤ x, a(p) where `p` is prime.
-/
def prime_summatory {M : Type*} [add_comm_monoid M] (a : ℕ → M) (x : ℝ) : M :=
  ∑ n in (finset.Icc 1 ⌊x⌋₊).filter nat.prime, a n
-- BM: equivalently could say it's `summatory (λ n, if (a n).prime then a n else 0) x`

lemma log_reciprocal :
  (λ x, prime_summatory (λ p, log p / p) x - log x) ≪ (λ _, 1) :=
sorry

lemma prime_counting_asymptotic :
  (λ x, prime_summatory (λ _, 1) x - summatory Λ x / log x) ≪ (λ x, x / (log x)^2) :=
sorry

lemma prime_reciprocal : ∃ b,
  (λ x, prime_summatory (λ p, 1 / p) x - log (log x) - b) ≪ (λ x, 1 / log x) :=
sorry

-- BM: I expect there's a nicer way of stating this but this should be good enough for now
lemma mertens_third :
  ∃ c, (λ x, ∏ p in (finset.Icc 1 ⌊x⌋₊), (1 - 1/p)⁻¹ - c * log x) ≪ (λ _, 1) :=
sorry

end nat.arithmetic_function
