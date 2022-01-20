/-
Copyright (c) 2021 Bhavik Mehta, Thomas Bloom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Thomas Bloom
-/

import data.real.basic
import analysis.special_functions.log
import analysis.special_functions.pow
import order.filter.at_top_bot
import number_theory.arithmetic_function

/-!
# Title

This file should contain a formal proof of https://arxiv.org/pdf/2112.03726.pdf, but for now it
contains associated results useful for that paper.
-/

open_locale big_operators -- this lets me use ∑ and ∏ notation
open filter real
open nat (coprime)

open_locale arithmetic_function
open_locale classical
noncomputable theory

def upper_density (A : set ℕ) : ℝ := limsup at_top
   (λ N : ℕ, (((finset.range(N+1)).filter (λ n, n ∈ A)).card : ℝ) / N)

theorem unit_fractions_upper_density (A : set ℕ) (hA : upper_density A > 0):
   ∃ (S : finset ℕ), (S : set ℕ) ⊆ A ∧ ∑ n in S, (1 / n : ℝ) = 1 :=
sorry

theorem unit_fractions_upper_log_density :
  ∀ᶠ (N : ℕ) in at_top, ∀ A ⊆ finset.range (N+1),
    25 * log (log (log N)) * log N / log (log N) ≤ ∑ n in A, (1 / n : ℝ) →
      ∃ S ⊆ A, ∑ n in S, (1 / n : ℝ) = 1 :=
sorry

-- * sorry is used as a placeholder for things we haven't filled in yet, a finished formal proof
--   would be "sorry-free"
-- * it's easier to write all inequalities as < or ≤ for essentially technical reasons, and it's
--   not too unreadable
-- * `finset.range (N+1)` is the finite set `{0, 1, ..., N}`. Oddly enough, 1/0 is defined to be 0
--   in Lean, so it's actually safe for me to include `0` in the set (in fact equivalent).
--     * the alternative is to have division only defined when the denominator is non-zero, but
--       that turns out to be more inconvenient; instead we allow division by zero but many
--       lemmas about division insist the denominator is non-zero instead
--     * for instance, to divide by `log (log N)` above I'd need to show that it's non-zero, which
--       is obvious but still requires work. Essentially the tradeoff is that the statement doesn't
--       need these proofs, but the proof will; and it's more important for the statement to be
--       readable
-- * I had to write `(1 / n : ℝ)` rather than just `(1 / n)` because otherwise Lean tries to work
--   with `1 / n` as a natural, which means floor division. So I instead say "treat this as a real
--   number" to make the division act sensibly. I could instead talk about rationals, but for
--   the inequality part I've got a real on the LHS anyway, so it would convert to rationals and
--   then to reals, so might as well go straight to ℝ.

-- This is R(A) in the paper.
def rec_sum (A : finset ℕ) : ℚ := ∑ n in A, 1/n

lemma rec_sum_bUnion_disjoint {A : finset (finset ℕ)}
  (hA : (A : set (finset ℕ)).pairwise_disjoint id) : rec_sum (A.bUnion id) = ∑ s in A, rec_sum s :=
by simp only [rec_sum, finset.sum_bUnion hA, id.def]

-- This is A_q in the paper.
def local_part (A : finset ℕ) (q : ℕ) : finset ℕ := A.filter (λ n, q ∣ n ∧ coprime q (n/q) )

-- This is Q_A in the paper.
-- Replace nat.prime here with prime_power
def ppowers_in_set (A : finset ℕ) : set ℕ := { q | nat.prime q ∧ local_part A q ≠ ∅ }

-- For summing over 1/q for q in Q_A, need to know this is a finite set, so
-- I've put the below for now - actually should be ppowers_in_set? Prove this is
-- finite as a lemma?
def fin_ppowers_in_set (A : finset ℕ) : finset ℕ := sorry

-- This is R(A;q) in the paper.
def rec_sum_local (A : finset ℕ) (q : ℕ) : ℚ := ∑ n in local_part A q, q/n

def ppower_rec_sum (A : finset ℕ) : ℚ :=
∑ q in fin_ppowers_in_set A, 1/q

-- Replace nat.prime here with prime_power
def is_smooth (y : ℝ) (n : ℕ) : Prop := ∀ q : ℕ, nat.prime q → q ∣ n → (q : ℝ) ≤ y

-- Prop 1
theorem technical_prop :
  ∀ᶠ (N : ℕ) in at_top, ∀ (A ⊆ finset.range (N+1)) (y z : ℝ),
  (1 ≤ y) → (y ≤ z) → (z ≤ (log N)^((1/500 : ℝ)))
  → (∀ n ∈ A, ( (N:ℝ)^(1-(1:ℝ)/(log(log N))) ≤ n ))
  → 2 / y + (log N)^(-(1/200 : ℝ)) ≤ (rec_sum A : ℝ)
  → (∀ n ∈ A, ∃ d₁ d₂ : ℕ, (d₁ ∣ n) ∧ (d₂ ∣ n) ∧ (y ≤ d₁) ∧ (4*d₁ ≤ d₂) ∧ ((d₂ : ℝ) ≤ z) )
  → (∀ n ∈ A, is_smooth ((N:ℝ)^(1-(6:ℝ)/(log(log N)))) n)
  → (∀ n ∈ A, (((99:ℝ)/100)*log(log N) ≤ ω n ) ∧ ( (ω n : ℝ) ≤ 2*(log (log N))))
  → ∃ S ⊆ A, ∃ d : ℕ, (y ≤ d) ∧ ((d:ℝ) ≤ z) ∧
    rec_sum S = 1/d
  :=
sorry

-- (written before getting anywhere)
-- I have a suspicion that an alternative phrasing might be nicer
-- The ordering of the Sᵢ doesn't actually matter...
-- the idea is that we pick a collection of subsets which has maximum size

-- (written later)
-- the above wasn't really true, I forgot about `nat.find_greatest` which does what's needed
-- but it's still helpful to forget about the ordering of the S_i both here and in general
-- imo it's almost always easier without, and oftentimes the argument never needed the ordering
-- in the first place
-- also `finset.exists_smaller_set` and `finset.exists_intermediate_set` are good to know about

-- Corollary 1
theorem corollary_one :
  ∀ᶠ (N : ℕ) in at_top, ∀ (A ⊆ finset.range (N+1)),
  (∀ n ∈ A, ( (N:ℝ)^(1-(1:ℝ)/(log(log N))) ≤ n ))
  → (log N)^((1/200 : ℝ)) ≤ (rec_sum A : ℝ)
  → (∀ n ∈ A, ∃ p : ℕ, ((p ∣ n) ∧ (5 ≤ p) ∧ ((p:ℝ) ≤ (log N)^((1/500 : ℝ))) ))
  → (∀ n ∈ A, is_smooth ((N:ℝ)^(1-(6:ℝ)/(log(log N)))) n)
  → (∀ n ∈ A, (((99:ℝ)/100)*log(log N) ≤ ω n ) ∧ ( (ω n : ℝ) ≤ 2*(log (log N))))
  → ∃ S ⊆ A, rec_sum S = 1 :=
begin
  filter_upwards [technical_prop, eventually_ge_at_top 1],
  intros N p1 hN₁ A A_upper_bound A_lower_bound hA₁ hA₂ hA₃ hA₄,
  -- `good_set` expresses the families of subsets that we like
  -- instead of saying we have S_1, ..., S_k, I'll say we have k-many subsets (+ same conditions)
  let good_set : finset (finset ℕ) → Prop :=
    λ S, (∀ s ∈ S, s ⊆ A) ∧ (S : set (finset ℕ)).pairwise_disjoint id ∧
      ∀ s, ∃ (d : ℕ), s ∈ S → 1 ≤ d ∧ (d : ℝ) ≤ (log N)^(1/500 : ℝ) ∧ rec_sum s = 1 / d,
    -- the last condition involving `d` is chosen weirdly so that `choose` later gives a more
    -- convenient function
  let P : ℕ → Prop := λ k, ∃ S : finset (finset ℕ), S.card = k ∧ good_set S,
  let k : ℕ := nat.find_greatest P A.card, -- A.card is a trivial upper bound
  have P0 : P 0 := ⟨∅, by simp [good_set]⟩, -- we clearly have that 0 satisfies p by using ∅
  have Pk : P k := nat.find_greatest_spec (nat.zero_le _) P0,
  obtain ⟨S, hk, hS₁, hS₂, hS₃⟩ := Pk,
  choose d' hd'₁ hd'₂ hd'₃ using hS₃,
  let t : ℕ → ℕ := λ d, (S.filter (λ s, d' s = d)).card,
  -- If we do have an appropriate d, take it
  by_cases h : ∃ d : ℕ, 0 < d ∧ d ≤ t d,
  { obtain ⟨d, d_pos, ht⟩ := h,
    -- there are ≥ d things with R(s) = 1/d, pick a subset so we have exactly d
    obtain ⟨T', hT', hd₂⟩ := finset.exists_smaller_set _ _ ht,
    have hT'S := hT'.trans (finset.filter_subset _ _),
    refine ⟨T'.bUnion id, _, _⟩,
    { refine (finset.bUnion_subset_bUnion_of_subset_left _ hT'S).trans _,
      rwa finset.bUnion_subset },
    rw [rec_sum_bUnion_disjoint (hS₂.subset hT'S), finset.sum_congr rfl, finset.sum_const, hd₂,
      nsmul_eq_mul, mul_div_cancel'],
    { rw nat.cast_ne_zero, exact d_pos.ne' },
    intros i hi,
    rw [hd'₃ _ (hT'S hi), (finset.mem_filter.1 (hT' hi)).2] },
  push_neg at h,
  -- otherwise make A' as in the paper
  let A' := A \ S.bUnion id,
  have : (∑ s in S, rec_sum s : ℝ) ≤ (log N)^(1/500 : ℝ),
  { transitivity (∑ d in finset.Icc 1 ⌊(log N)^(1/500 : ℝ)⌋₊, t d / d : ℝ),
    { have : ∀ s ∈ S, d' s ∈ finset.Icc 1 ⌊(log N)^(1/500 : ℝ)⌋₊,
      { intros s hs,
        simp only [finset.mem_Icc, hd'₁ s hs, nat.le_floor (hd'₂ s hs), and_self] },
      rw ←finset.sum_fiberwise_of_maps_to this,
      apply finset.sum_le_sum,
      intros d hd,
      rw [div_eq_mul_one_div, ←nsmul_eq_mul],
      apply finset.sum_le_of_forall_le,
      intros s hs,
      simp only [finset.mem_filter] at hs,
      rw [hd'₃ _ hs.1, hs.2, rat.cast_div, rat.cast_one, rat.cast_coe_nat] },
    refine (finset.sum_le_of_forall_le _ _ 1 _).trans _,
    { simp only [one_div, and_imp, finset.mem_Icc],
      rintro d hd -,
      exact div_le_one_of_le (nat.cast_le.2 ((h d hd).le)) (nat.cast_nonneg _) },
    { simp only [nat.add_succ_sub_one, add_zero, nat.card_Icc, nat.smul_one_eq_coe],
      exact nat.floor_le (rpow_nonneg_of_nonneg (log_nonneg (nat.one_le_cast.2 hN₁)) _) } },
  sorry
end

-- define the X in Lemma 1 as a separate definition?
def X (y z : ℝ) : set ℕ := sorry

-- Lemma 1
lemma sieve_lemma_one  : ∃ C : ℝ,
  ∀ᶠ (N : ℕ) in at_top, ∀ y z : ℝ, (3 ≤ y) → (y < z) → (z ≤ log N) →
   let X : set ℕ := { n : ℕ | ∀ p:ℕ, (prime p) → (p ∣ n) →
   ( ((p:ℝ) < y) ∨ (z < p)) } in
   (((finset.range(2*N)).filter (λ n, n ∈ X ∧ N ≤ n)).card : ℝ) ≤
   C * (log y / log z) * N
    :=
sorry

-- This is Turan's estimate, belongs in basic_estimates probably
lemma turan_primes_estimate : ∃ (C : ℝ), ∀ x : ℝ, (x ≥ 25) →
  (∑ n in finset.Icc 1 ⌊x⌋₊, ((ω n : ℝ) - log(log n))^2
  ≤  C * x * log(log x)  ) :=
 --
--  ≤  ):=
sorry
-- Textbook proof is to expand square, rearrnage sum, write ω n as
-- ∑ p ≤ x, 1_(p∣n)

-- Sieve of Eratosthenes-Legendre, again belongs in basic_estimates
--lemma sieve_eratosthenes :

-- Lemma 2
lemma sieve_lemma_two  : ∃ C : ℝ,
  ∀ᶠ (N : ℕ) in at_top, ∀ y z : ℝ, (2 ≤ y) → (4*y < z) → (z^2 ≤ log N) →
   let Y : set ℕ := { n : ℕ | ∃ p₁ p₂ : ℕ, (p₁ ≠ p₂) ∧ (prime p₁)
   ∧ (prime p₂) ∧ (p₁ ∣ n) ∧ (p₂ ∣ n) ∧ (y ≤ p₁) ∧ (4*p₁ ≤ p₂)
   ∧ ((p₂:ℝ) ≤ z) } in
   (((finset.range(N+1)).filter (λ n, ¬(n ∈ Y))).card : ℝ) ≤
   C * (log y / log z)^(1/2) * N
    :=
sorry

def lcm (A : finset ℕ) : ℕ := A.lcm id

-- This is the set D_I
def interval_rare_ppowers (I: finset ℕ) (A : finset ℕ) (K : ℝ) : set ℕ :=
{ q in ppowers_in_set A |
(((local_part A q).filter (λ n, ∀ x ∈ I, ¬ (n ∣ x))).card : ℝ)
< K/q }

-- Proposition 2
theorem circle_method_prop : ∃ c : ℝ,
  ∀ᶠ (N : ℕ) in at_top, ∀ k M : ℕ, ∀ η K : ℝ,  ∀ A ⊆ finset.range (N+1),
  (M ≤ N) → ((N:ℝ)^(3/4 : ℝ) ≤ M) → (1 ≤ k) → ((k:ℝ) ≤ c*M) →
  (0 < η) → (η < 1) → (2*K ≤ M) → ((N:ℝ)^(3/4:ℝ) ≤ K) →
  (∀ n ∈ A, M ≤ n) →
  (rec_sum A ≤ 2/k) → ((2:ℚ)/k - 1 ≤ rec_sum A ) →
  (k ∣ lcm A) →
  (∀ q ∈ ppowers_in_set A, ((q:ℝ) ≤ c*M/k) ∧
  ((q:ℝ) ≤ c*η*M*K^2 / (N*log N)^2)) →
  (∀ (a : ℕ), let I : finset ℕ := (finset.Icc a ⌊(a:ℝ)+K⌋₊)
  in
  ( ((M:ℝ)/log N ≤ ((A.filter (λ n, ∀ x ∈ I, ¬ (n ∣ x))).card : ℝ)) ∨
    (∃ x ∈ I, ∀ q : ℕ, (q ∈ interval_rare_ppowers I A (η*M)) → q ∣ x)
  ))
  → ∃ S ⊆ A, rec_sum S = 1/k
  :=
sorry


-- Lemma 3
-- TODO: Replace nat.divisors with just the prime power divisors
lemma rest_recip_ppowers : ∃ C : ℝ,
  ∀ᶠ (N : ℕ) in at_top, ∀ n₁ n₂ : ℕ, (n₁ < n₂) → (n₂ ≤ N+n₁) →
  ∑ q in (nat.divisors (int.gcd n₁ n₂)), (1/q : ℝ) ≤
  C * log(log(log N))
 :=
sorry

-- Lemma 4
lemma rec_qsum_lower_bound (ε : ℝ) (hε1 : 0 < ε) (hε2 : ε < 1/2) :
  ∀ᶠ (N : ℕ) in at_top, ∀ A : finset ℕ,
  ((log N)^(-ε/2) ≤ rec_sum A )
  → (∀ n ∈ A, ((1-ε)*log(log N) ≤ ω n ) ∧ ( (ω n : ℝ) ≤ 2*(log (log N))))
  → (1-2*ε)*log(log N) *real.exp(-1) ≤ ∑ q in fin_ppowers_in_set A, (1/q : ℝ)
:=
sorry

-- Lemma 5
lemma find_good_d : ∃ c C : ℝ, ∀ᶠ (N : ℕ) in at_top, ∀ M k : ℝ,
  ∀ A ⊆ finset.range(N+1),
  (M ≤ N) → ((N:ℝ) ≤ M^2) → ((4:ℝ) ≤ k) → (k ≤ c* log(log N))
  → (∀ n ∈ A, M ≤ (n:ℝ) ∧ ((ω n) : ℝ) ≤ (log N)^(1/k)) →
    (∀ q ∈ ppowers_in_set A,
    ((log N)^(-(1/2 : ℝ)) ≤ rec_sum_local A q) →
    (∃ d : ℕ,
    ( M*real.exp(-(log N)^(1-1/k)) < q*d ) ∧
    ( (ω d : ℝ) ≤ (5/log k) * log(log N) ) ∧
    ( C*(rec_sum_local A q) / (log N)^(2/k) ≤
      ∑ n in (local_part A q).filter(λ n, (q*d ∣ n) ∧
        (coprime (q*d) (n/q*d))), (q*d/n : ℝ)  ) ) )
  :=
sorry

-- Proposition 3
theorem force_good_properties :
  ∀ᶠ (N : ℕ) in at_top, ∀ M : ℝ, ∀ A ⊆ finset.range(N+1),
  ((N:ℝ)^2 ≤ M) →
  (∀ n ∈ A, M ≤ (n:ℝ) ∧
    (((99:ℝ)/100)*log(log N) ≤ ω n ) ∧
    ( (ω n : ℝ) ≤ 2*(log (log N)))) →
  ( (log N)^(-(1/101 : ℝ)) ≤ rec_sum A ) →
  (∀ q ∈ ppowers_in_set A,
    ((log N)^(-(1/100 : ℝ)) ≤ rec_sum_local A q )) → (
  (∃ B ⊆ A, ((rec_sum A) ≤ 3*rec_sum B) ∧
  ((ppower_rec_sum B : ℝ) ≤ (2/3)* log(log N)))
  ∨
  (∀ (a : ℕ), let I : finset ℕ := (finset.Icc a
       ⌊(a:ℝ)+M*(N:ℝ)^(-(2:ℝ)/log(log N))⌋₊) in
  ( ((M:ℝ)/log N ≤ ((A.filter (λ n, ∀ x ∈ I, ¬ (n ∣ x))).card : ℝ)) ∨
    (∃ x ∈ I, ∀ q : ℕ, (q ∈ interval_rare_ppowers I A
       (M / (2*q*(log N)^(1/100 : ℝ)))) → q ∣ x)
  ))) :=
sorry

-- Lemma 6
lemma pruning_lemma_one :
  ∀ᶠ (N : ℕ) in at_top, ∀ A ⊆ finset.range(N+1), ∃ B ⊆ A,
  ((rec_sum B : ℝ) ≥ rec_sum A - (log N)^(-(1/200:ℝ))) ∧
  (∀ q ∈ ppowers_in_set B,
  (2:ℝ)*(log N)^(-(1/100:ℝ)) ≤ rec_sum_local B q )
  :=
sorry

-- Lemma 7
lemma pruning_lemma_two :
  ∀ᶠ (N : ℕ) in at_top, ∀ M α : ℝ, ∀ A ⊆ finset.range(N+1),
  ((N:ℝ)^2 ≤ M) → ((2:ℝ)*(log N)^(-(1/200:ℝ)) < α ) →
  (∀ n ∈ A, M ≤ (n:ℝ)) →
  (α + (log N)^(-(1/200:ℝ)) ≤ rec_sum A ) →
  (∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ M*(log N)^(-(1/100:ℝ))) →
  ∃ B ⊆ A, ( (rec_sum B : ℝ) < α) ∧ ( α - 1/M ≤ rec_sum B) ∧
  (∀ q ∈ ppowers_in_set B, (log N)^(-(1/100:ℝ)) ≤
    rec_sum_local B q)
  :=
sorry
