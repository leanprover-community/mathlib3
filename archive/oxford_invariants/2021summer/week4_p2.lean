/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.intervals
import data.nat.multiplicity
import number_theory.padics.padic_norm

/-!
# The Oxford Invariants Puzzle Challenges - Summer 2021, Week 4, Problem 1

## Original statement

Find all ordered pairs `(n, m)` such that `n ≥ 2` and `n!` does not divide

$$\prod_{i = 1}^{n - 1} (m^i + i!)^{\left\lfloor\frac n i\right\rfloor}$$
`∏ᵢ₌₁ⁿ⁻¹ (m^i + i!)^⌊n / i⌋`


## Comments

Division of naturals in mathlib equals the floor of the corresponding rational. So we replace
`⌊n/i⌋` by `n/i`.

## Formalised statement



## Proof outline


-/

open_locale big_operators nat
open finset nat

lemma nat.pred_mul_geom_sum_le (a b n : ℕ) :
  (b - 1) * ∑ i in range n.succ, a/b^i ≤ a * b - a/b^n :=
calc
  (b - 1) * (∑ (i : ℕ) in range n.succ, a/b^i)
      = ∑ (k : ℕ) in range n, a/b^(k + 1) * b + a * b
        - (∑ (x : ℕ) in range n, a/b^x + a/b^n)
      : by rw [nat.mul_sub_right_distrib, mul_comm, sum_mul, one_mul, sum_range_succ',
          sum_range_succ, pow_zero, nat.div_one]
  ... ≤ ∑ (k : ℕ) in range n, a/b^k + a * b - (∑ (x : ℕ) in range n, a / b^x + a/b^n)
      : begin
        refine nat.sub_le_sub_right (add_le_add_right (sum_le_sum $ λ i _, _) _) _,
        rw [pow_succ', ←nat.div_div_eq_div_mul],
        exact div_mul_le_self _ _,
      end
  ... = a * b - a/b^n : nat.add_sub_add_left _ _ _

lemma nat.geom_sum_le {b : ℕ} (hb : 2 ≤ b) (a n : ℕ) :
  ∑ i in range n, a/b^i ≤ a * b/(b - 1) :=
begin
  refine (nat.le_div_iff_mul_le _ _ $ nat.sub_pos_of_lt hb).2 _,
  cases n,
  { rw [sum_range_zero, zero_mul],
    exact nat.zero_le _ },
  rw mul_comm,
  exact (nat.pred_mul_geom_sum_le a b n).trans (nat.sub_le_self _ _),
end

lemma nat.geom_sum_Ico_le {b : ℕ} (hb : 2 ≤ b) (a n : ℕ) :
  ∑ i in Ico 1 n, a/b^i ≤ a/(b - 1) :=
begin
  cases n,
  { rw [Ico.eq_empty_of_le zero_le_one, sum_empty],
    exact nat.zero_le _ },
  rw ←add_le_add_iff_left a,
  calc
    a + ∑ (i : ℕ) in Ico 1 n.succ, a/b^i
        = a/b^0 + ∑ (i : ℕ) in Ico 1 n.succ, a/b^i : by rw [pow_zero, nat.div_one]
    ... = ∑ i in range n.succ, a/b^i : begin
          rw [range_eq_Ico, ←finset.Ico.insert_succ_bot (zero_lt_succ _), sum_insert],
          exact λ h, zero_lt_one.not_le (Ico.mem.1 h).1,
        end
    ... ≤ a * b/(b - 1) : nat.geom_sum_le hb a _
    ... = (a * 1 + a * (b - 1))/(b - 1)
        : by rw [←mul_add, nat.add_sub_cancel' (one_le_two.trans hb)]
    ... = a + a/(b - 1) : by rw [mul_one, add_mul_div_right _ _ (nat.sub_pos_of_lt hb), add_comm],
end

lemma nat.prime.multiplicity_factorial_le_div_pred {p : ℕ} (hp : p.prime) (n : ℕ) :
  multiplicity p n! ≤ (n/(p - 1) : ℕ) :=
begin
  rw [hp.multiplicity_factorial (lt_succ_self _), enat.coe_le_coe],
  exact nat.geom_sum_Ico_le hp.two_le _ _,
end

variables (m n : ℕ)

theorem week4_p2 (hn : 2 ≤ n) :
  ¬ n! ∣ (∏ i in Ico 1 n, (m^i + i!)^(n/i)) ↔ n.prime ∧ n ∣ m :=
begin
  split, swap,
  { rintro ⟨hnprime, hnm⟩ h,
    obtain ⟨i, hi, h⟩ := (nat.prime_iff.1 hnprime).exists_mem_finset_dvd
      ((dvd_factorial (zero_lt_two.trans_le hn) le_rfl).trans h),
    rw Ico.mem at hi,
    exact hi.2.not_le (hnprime.dvd_factorial.1 $ (nat.dvd_add_right $ dvd_pow hnm
    (lt_of_succ_le hi.1).ne').1 $ hnprime.dvd_of_dvd_pow h) },
  contrapose!,
  rintro h,
  suffices H : ∀ p : ℕ, p.prime →
    multiplicity p n! ≤ multiplicity p ∏ (i : ℕ) in Ico 1 n, (m^i + i!)^(n/i),
  {
    sorry
  },
  rintro p hp,
  by_cases hpn : p ≤ n, swap,
  { rw multiplicity.multiplicity_eq_zero_of_not_dvd ((not_congr hp.dvd_factorial).2 hpn),
    exact zero_le _ },
  rw multiplicity.finset.prod (nat.prime_iff.1 hp),
  by_cases hpm : p ∣ m,
  {
    have : p ≠ n := λ hpn, h (hpn ▸ hp) (hpn ▸ hpm),
    calc
      multiplicity p n!
          = ∑ (i : ℕ) in Ico 1 (log p n).succ, ((n/p^i : ℕ) : enat)
          : begin
            rw [hp.multiplicity_factorial (lt_succ_self _)], -- rw nat.cast_sum,
            sorry
          end
    ... = ∑ (i : ℕ) in (Ico 1 (log p n).succ).image (λ x, p^x), ((n/i : ℕ) : enat)
          : begin
            rw sum_image,
            exact λ x _ y _ h, pow_right_injective hp.two_le h,
          end
      ... ≤ ∑ (i : ℕ) in Ico 1 n, ((n / i : ℕ) : enat) : begin
            refine sum_le_sum_of_subset _,
            rintro i hi,
            obtain ⟨a, ha, rfl⟩ := mem_image.1 hi,
            rw [Ico.mem] at ⊢ ha,
            refine ⟨pow_pos hp.pos _, _⟩,
            have := (nat.pow_le_iff_le_log _ _ _ _).2 (le_of_lt_succ ha.2),
            refine ((nat.pow_le_iff_le_log _ _ _ _).2 (le_of_lt_succ ha.2)).lt_of_ne _,
          end
      ... = ∑ (i : ℕ) in Ico 1 n, multiplicity p ((m^i + i!)^(n/i)) : sorry
  },
  sorry,
  calc
    multiplicity p n!
        ≤ (n/(p - 1) : ℕ) : hp.multiplicity_factorial_le_div_pred n
    ... = (n/(p - 1) : ℕ) • 1 : sorry
    ... ≤ (n/(p - 1)) • multiplicity p (m^(p - 1) + (p - 1)!) : begin
          sorry,
        end
    ... = (λ x, multiplicity p ((m^(p - 1) + (p - 1)!)^(n/(p - 1)))) (p - 1)
        : (multiplicity.pow $ nat.prime_iff.1 hp).symm
    ... ≤ ∑ (i : ℕ) in Ico 1 n, multiplicity p ((m^i + i!)^(n/i))
        : begin
          have H : ∀ i ∈ Ico 1 n, 0 ≤ multiplicity p ((m^i + i!)^(n/i)) := λ _ _, zero_le _,
          exact finset.single_le_sum H (Ico.mem.2
            ⟨hp.pred_pos, succ_le_iff.1 ((succ_pred_prime hp).symm ▸ hpn)⟩),
        end,
end
