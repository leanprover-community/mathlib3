/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales
-/
import topology.instances.ennreal
import algebra.squarefree

/-!
# Divergence of the Prime Reciprocal Series

This file proves Theorem 81 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).
The theorem states that the sum of the reciprocals of all prime numbers diverges.
The formalization follows Erdős's proof by upper and lower estimates.

## References

https://en.wikipedia.org/wiki/Divergence_of_the_sum_of_the_reciprocals_of_the_primes
-/

open_locale big_operators
open_locale classical
open filter finset

lemma card_le_div_nat {n p : ℕ} (hp : 0 < p) : card {e ∈ range n | p ∣ (e + 1)} ≤ n / p :=
begin
  let f : ℕ → ℕ := λ e, (e + 1) / p - 1,
  let Np := {e ∈ range n | p ∣ (e + 1)},

  have hf : ∀ a : ℕ, a ∈ Np → f a ∈ range (n / p),
  { simp_intros a ha only [Np, sep_def, mem_filter, mem_range],
    obtain ⟨han, ⟨w, hw⟩⟩ := ha,
    simp only [f, mem_range],
    have hnp : n / p ≥ 1,
    { have : 0 < w := by nlinarith,
      rw ← nat.div_self hp,
      exact nat.div_le_div_right (by nlinarith) },
    calc (a + 1) / p - 1 ≤ n / p - 1 : nat.sub_le_sub_right
                                         (nat.div_le_div_right (nat.succ_le_iff.mpr han)) 1
    ...                  < n / p     : nat.sub_lt (zero_lt_one.trans_le hnp) zero_lt_one },

  have hf_inj : ∀ a₁ : ℕ, a₁ ∈ Np → ∀ a₂ : ℕ, a₂ ∈ Np → f a₁ = f a₂ → a₁ = a₂,
  { simp_intros a₁ ha₁ a₂ ha₂ hfeq only [f, Np, sep_def, mem_filter, mem_range],
    obtain ⟨⟨hna₁, ⟨w₁, hw₁⟩⟩, ⟨hna₂, ⟨w₂, hw₂⟩⟩⟩ := ⟨ha₁, ha₂⟩,
    rw [hw₁, hw₂, nat.mul_div_cancel_left w₁ hp, nat.mul_div_cancel_left w₂ hp] at hfeq,
    have hw₁_eq_w₂ : w₁ = w₂, { refine nat.pred_inj _ _ hfeq; nlinarith },
    rw [← add_left_inj 1, hw₁, hw₂, hw₁_eq_w₂] },

  calc  card Np ≤ card (range (n / p)) : card_le_card_of_inj_on f hf hf_inj
  ...           = n / p                : card_range (n / p),
end

lemma card_le_div_real {n p : ℕ} (hp : 0 < p) :
  (card {e ∈ range n | p ∣ (e + 1)} : ℝ) ≤ n * (1 / p) :=
begin
  have hp0 : 0 < (p : ℝ) := nat.cast_pos.mpr hp,
  have hnp : n / p * p ≤ n := nat.div_mul_le_self n p,
  calc  (card {e ∈ range n | p ∣ (e + 1)} : ℝ)
      ≤ ↑(n / p)      : nat.cast_le.mpr (card_le_div_nat hp)
  ... ≤ ↑n / ↑p       : (le_div_iff hp0).mpr (by assumption_mod_cast)
  ... = ↑n * (1 / ↑p) : div_eq_mul_one_div ↑n ↑p,
end

lemma card_eq_card_sdiff_add_card {A B : finset ℕ} (h : A ⊆ B) :
  card B = card (B \ A) + card A :=
(nat.sub_eq_iff_eq_add (card_le_of_subset h)).mp (eq.symm (card_sdiff h))

lemma lemma1_not_hyp_imp_sum_lt_half
  (h : ¬ tendsto (λ n, ∑ p in {p ∈ range n | nat.prime p}, (1 / (p : ℝ))) at_top at_top) :
  ∃ k, ∀ x, ∑ p in {p ∈ range (x + 1) | k < p ∧ nat.prime p}, 1 / (p : ℝ) < 1 / 2 :=
begin
  have h0 : (λ n, ∑ p in {p ∈ range n | nat.prime p}, (1 / (p : ℝ)))
          = λ n, ∑ p in range n, ite (nat.prime p) (1 / (p : ℝ)) 0,
  { simp only [sum_filter, filter_congr_decidable, sep_def] },
  rw h0 at h,

  have hf : ∀ n : ℕ, 0 ≤ ite (nat.prime n) (1 / (n : ℝ)) 0,
  { intro n, split_ifs,
    { simp only [one_div, inv_nonneg, nat.cast_nonneg] },
    { exact rfl.ge } },

  rw ← summable_iff_not_tendsto_nat_at_top_of_nonneg hf at h,
  rw summable_iff_vanishing at h,
  specialize h (set.Ioo (-1 : ℝ) ((1 : ℝ) / 2)) (mem_nhds_sets is_open_Ioo (by norm_num)),
  obtain ⟨s, h⟩ := h,
  obtain ⟨k, hk⟩ := exists_nat_subset_range s,
  use k,
  intro x,

  let P := {p ∈ range (x + 1) | k < p ∧ nat.prime p},
  have hP : P = filter (λ p : ℕ, k < p ∧ nat.prime p) (range (x + 1)),
  { simp only [P, sep_def, filter_congr_decidable] },

  specialize h (filter (λ n : ℕ, k < n) (range (x + 1))) _,
  { rw disjoint_iff_ne,
    simp_intros a ha b hb only [mem_filter],
    exact ((mem_range.mp (hk hb)).trans ha.2).ne' },
  { simpa only [←sum_filter, filter_filter, ←hP] using h.2 },
end

lemma lemma2_range_x_sdiff_M_eq_U {x k : ℕ} :
  range x \ {e ∈ range x | ∀ p : ℕ, (nat.prime p ∧ p ∣ (e + 1)) → p ≤ k} =
  finset.bUnion {p ∈ range (x + 1) | k < p ∧ nat.prime p} (λ p, {e ∈ range x | p ∣ (e + 1)}) :=
begin
  ext e,
  simp only [mem_bUnion, not_and, mem_sdiff, sep_def, mem_filter, mem_range],
  push_neg,
  split,
  { rintros ⟨hex, hexh⟩,
    obtain ⟨p, ⟨hpp, hpe1⟩, hpk⟩ := hexh hex,
    use p,
    split,
    { simp only [mem_filter, mem_range],
      refine ⟨_, hpk, hpp⟩,
      calc p ≤ e + 1 : (nat.le_of_dvd (nat.succ_pos e)) hpe1
      ...    < x + 1 : nat.succ_lt_succ hex },
    { exact ⟨hex, hpe1⟩ } },
  { rintros ⟨p, hpfilter, ⟨hex, hpe1⟩⟩,
    simp only [mem_filter, mem_range] at hpfilter,
    obtain ⟨-, hpk, hpp⟩ := hpfilter,
    rw imp_iff_right hex,
    exact ⟨hex, ⟨p, ⟨hpp, hpe1⟩, hpk⟩⟩ },
end

lemma lemma3_card_U_le_x_mul_sum {x k : ℕ} :
  (card
    (finset.bUnion {p ∈ range (x + 1) | k < p ∧ nat.prime p} (λ p, {e ∈ range x | p ∣ (e + 1)}))
  : ℝ)
  ≤ x * ∑ p in {p ∈ range (x + 1) | k < p ∧ nat.prime p}, 1 / p :=
begin
  let P := {p ∈ range (x + 1) | k < p ∧ nat.prime p},
  let N := λ p, {e ∈ range x | p ∣ (e + 1)},
  have h : card (finset.bUnion P N) ≤ ∑ p in P, card (N p) := card_bUnion_le,

  calc  (card (finset.bUnion P N) : ℝ)
      ≤ ∑ p in P, card (N p)  : by assumption_mod_cast
  ... ≤ ∑ p in P, x * (1 / p) : by { refine sum_le_sum _,
                                     intro p,
                                     simp only [P, sep_def, mem_filter, mem_range],
                                     rintros ⟨-, -, hpp⟩,
                                     simp only [N, card_le_div_real (nat.prime.pos hpp)] }
  ... = x * ∑ p in P, 1 / p   : mul_sum.symm,
end

lemma lemma4_aux_card_M1_le_2_pow_k {x k : ℕ} :
  card {e ∈ range x | squarefree (e + 1) ∧ ∀ p : ℕ, (nat.prime p ∧ p ∣ (e + 1)) → p ≤ k} ≤ 2 ^ k :=
begin
  let M₁ := {e ∈ range x | squarefree (e + 1) ∧ ∀ p : ℕ, (nat.prime p ∧ p ∣ (e + 1)) → p ≤ k},
  let f := λ s, finset.prod s (λ a, a) - 1,
  let K := powerset (image nat.succ (range k)),

  have h : M₁ ⊆ image f K,
  { intros m hm,
    simp only [M₁, sep_def, mem_filter, mem_range] at hm,
    obtain ⟨hmx, hms, hmp⟩ := hm,
    have h' : ∃ a : finset ℕ, a ⊆ image nat.succ (range k) ∧ f a = m,
    { use (m + 1).factors,
      { rwa [multiset.coe_nodup, ← nat.squarefree_iff_nodup_factors (nat.succ_ne_zero m)] },
      split,
      { intro p,
        have h1 : p ∈ (m + 1).factors → ∃ a : ℕ, a < k ∧ a.succ = p,
        { simp_intros hp only [(nat.mem_factors (nat.zero_lt_succ m))],
          exact ⟨p.pred, (nat.pred_lt (nat.prime.ne_zero hp.left)).trans_le ((hmp p) hp),
                nat.succ_pred_eq_of_pos (nat.prime.pos hp.left)⟩ },
        simpa },
      { have h2 : (m + 1).factors.prod - 1 = m,
        { simpa only [nat.prod_factors (nat.zero_lt_succ m)] using nat.succ_sub_one m },
        simp_rw [f], simpa } },
    simpa },

  calc card M₁ ≤ card (image f K)                    : card_le_of_subset h
  ...          ≤ card K                              : card_image_le
  ...          ≤ 2 ^ card (image nat.succ (range k)) : by simp only [K, card_powerset]
  ...          ≤ 2 ^ card (range k)                  : pow_le_pow one_le_two card_image_le
  ...          = 2 ^ k                               : by rw card_range k,
end

lemma lemma4_card_M_le_2_pow_k_mul_sqrt_x {x k : ℕ} :
  card {e ∈ range x | ∀ p : ℕ, (nat.prime p ∧ p ∣ (e + 1)) → p ≤ k} ≤ 2 ^ k * nat.sqrt x :=
begin
  let M := {e ∈ range x | ∀ p : ℕ, (nat.prime p ∧ p ∣ (e + 1)) → p ≤ k},
  let M₁ := {e ∈ range x | squarefree (e + 1) ∧ ∀ p : ℕ, (nat.prime p ∧ p ∣ (e + 1)) → p ≤ k},
  let M₂ := {e ∈ range (nat.sqrt x) | ∀ p : ℕ, (nat.prime p ∧ p ∣ (e + 1)) → p ≤ k},
  let K := finset.product M₁ M₂,
  let f : ℕ × ℕ → ℕ := λ mn, (mn.2 + 1) ^ 2 * (mn.1 + 1) - 1,

  have h1 : M ⊆ image f K,
  { intros m hm,
    simp only [M, M₁, M₂, mem_image, exists_prop, prod.exists, mem_product, sep_def, mem_filter,
               mem_range] at hm ⊢,
    have hm' := m.zero_lt_succ,
    obtain ⟨a, b, hab₁, hab₂⟩ := nat.sq_mul_squarefree_of_pos' hm',
    obtain ⟨ham, hbm⟩ := ⟨dvd.intro_left _ hab₁, dvd.intro _ hab₁⟩,
    refine ⟨a, b, ⟨⟨_, hab₂, λ p hp, _⟩, ⟨_, λ p hp, _⟩⟩, by simp_rw [f, hab₁, m.succ_sub_one]⟩,
    { exact (nat.succ_le_succ_iff.mp (nat.le_of_dvd hm' ham)).trans_lt hm.1 },
    { exact hm.2 p ⟨hp.1, dvd.trans hp.2 ham⟩ },
    { calc b < b + 1        : lt_add_one b
      ...    ≤ (m + 1).sqrt : by simpa only [nat.le_sqrt, pow_two] using nat.le_of_dvd hm' hbm
      ...    ≤ x.sqrt       : nat.sqrt_le_sqrt (nat.succ_le_iff.mpr hm.1) },
    { exact hm.2 p ⟨hp.1, dvd.trans hp.2 (nat.dvd_of_pow_dvd one_le_two hbm)⟩ } },

  have h2 : card M₂ ≤ nat.sqrt x,
  { rw ← card_range (nat.sqrt x), apply card_le_of_subset, simp [M₂] },

  calc card M ≤ card (image f K)   : card_le_of_subset h1
  ...         ≤ card K             : card_image_le
  ...         = card M₁ * card M₂  : card_product M₁ M₂
  ...         ≤ 2 ^ k * x.sqrt     : mul_le_mul' lemma4_aux_card_M1_le_2_pow_k h2,
end

theorem real.tendsto_sum_one_div_prime_at_top :
  tendsto (λ n, ∑ p in {p ∈ range n | nat.prime p}, (1 / (p : ℝ))) at_top at_top :=
begin
  by_contradiction,
  obtain ⟨k, h1⟩ := lemma1_not_hyp_imp_sum_lt_half h,

  let x := 2 ^ (k + 1) * 2 ^ (k + 1),
  let P := {p ∈ range (x + 1) | k < p ∧ nat.prime p},
  let M := {e ∈ range x | ∀ p : ℕ, (nat.prime p ∧ p ∣ (e + 1)) → p ≤ k},
  let N := λ p, {e ∈ range x | p ∣ (e + 1)},
  let U := finset.bUnion {p ∈ range (x + 1) | k < p ∧ nat.prime p} N,

  have h2 : x = card U + card M,
  { rw ← card_range x, simp only [U, M, N, ← lemma2_range_x_sdiff_M_eq_U],
    exact card_eq_card_sdiff_add_card (by simp) },

  have h3 :=
    calc (card U : ℝ) ≤ x * ∑ p in P, 1 / p : lemma3_card_U_le_x_mul_sum
    ...               < x * (1 / 2)         : mul_lt_mul_of_pos_left (h1 x) (by norm_num)
    ...               = x / 2               : mul_one_div x 2,

  have h4 :=
    calc (card M : ℝ) ≤ 2 ^ k * x.sqrt      : by exact_mod_cast lemma4_card_M_le_2_pow_k_mul_sqrt_x
    ...               = 2 ^ k * ↑(2 ^ (k + 1)) : by rw nat.sqrt_eq
    ...               = x / 2               : by field_simp [x, mul_right_comm, ← pow_succ'],

  refine (lt_self_iff_false (x : ℝ)).mp _,
  calc (x : ℝ) = (card U : ℝ) + (card M : ℝ) : by assumption_mod_cast
  ...          < x / 2 + x / 2               : add_lt_add_of_lt_of_le h3 h4
  ...          = x                           : add_halves ↑x,
end
