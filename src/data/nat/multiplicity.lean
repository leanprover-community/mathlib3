/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import algebra.big_operators.intervals
import data.nat.bitwise
import data.nat.log
import data.nat.parity
import ring_theory.int.basic

/-!
# Natural number multiplicity

This file contains lemmas about the multiplicity function (the maximum prime power dividing a
number) when applied to naturals, in particular calculating it for factorials and binomial
coefficients.

## Multiplicity calculations

* `nat.multiplicity_factorial`: Legendre's Theorem. The multiplicity of `p` in `n!` is
  `n/p + ... + n/p^b` for any `b` such that `n/p^(b + 1) = 0`.
* `nat.multiplicity_factorial_mul`: The multiplicity of `p` in `(p * n)!` is `n` more than that of
  `n!`.
* `nat.multiplicity_choose`: The multiplicity of `p` in `n.choose k` is the number of carries when
  `k` and`n - k` are added in base `p`.

## Other declarations

* `nat.multiplicity_eq_card_pow_dvd`: The multiplicity of `m` in `n` is the number of positive
  natural numbers `i` such that `m ^ i` divides `n`.
* `nat.multiplicity_two_factorial_lt`: The multiplicity of `2` in `n!` is strictly less than `n`.
* `nat.prime.multiplicity_something`: Specialization of `multiplicity.something` to a prime in the
  naturals. Avoids having to provide `p ≠ 1` and other trivialities, along with translating between
  `prime` and `nat.prime`.

## Tags

Legendre, p-adic
-/

open finset nat multiplicity
open_locale big_operators nat

namespace nat

/-- The multiplicity of `m` in `n` is the number of positive natural numbers `i` such that `m ^ i`
divides `n`. This set is expressed by filtering `Ico 1 b` where `b` is any bound greater than
`log m n`. -/
lemma multiplicity_eq_card_pow_dvd {m n b : ℕ} (hm : m ≠ 1) (hn : 0 < n) (hb : log m n < b):
  multiplicity m n = ↑((finset.Ico 1 b).filter (λ i, m ^ i ∣ n)).card :=
calc
  multiplicity m n = ↑(Ico 1 $ ((multiplicity m n).get (finite_nat_iff.2 ⟨hm, hn⟩) + 1)).card
    : by simp
... = ↑((finset.Ico 1 b).filter (λ i, m ^ i ∣ n)).card
    : congr_arg coe $ congr_arg card $ finset.ext $ λ i,
      begin
        rw [mem_filter, Ico.mem, Ico.mem, lt_succ_iff, ←@enat.coe_le_coe i, enat.coe_get,
          ←pow_dvd_iff_le_multiplicity, and.right_comm],
        refine (and_iff_left_of_imp (λ h, _)).symm,
        cases m,
        { rw [zero_pow, zero_dvd_iff] at h,
          exact (hn.ne' h.2).elim,
          { exact h.1 } },
        exact ((pow_le_iff_le_log (succ_lt_succ $ nat.pos_of_ne_zero $ succ_ne_succ.1 hm) hn).1 $
          le_of_dvd hn h.2).trans_lt hb,
      end

namespace prime

lemma multiplicity_one {p : ℕ} (hp : p.prime) : multiplicity p 1 = 0 :=
multiplicity.one_right (prime_iff.mp hp).not_unit

lemma multiplicity_mul {p m n : ℕ} (hp : p.prime) :
  multiplicity p (m * n) = multiplicity p m + multiplicity p n :=
multiplicity.mul $ prime_iff.mp hp

lemma multiplicity_pow {p m n : ℕ} (hp : p.prime) :
  multiplicity p (m ^ n) = n • (multiplicity p m) :=
multiplicity.pow $ prime_iff.mp hp

lemma multiplicity_self {p : ℕ} (hp : p.prime) : multiplicity p p = 1 :=
multiplicity_self (prime_iff.mp hp).not_unit hp.ne_zero

lemma multiplicity_pow_self {p n : ℕ} (hp : p.prime) : multiplicity p (p ^ n) = n :=
multiplicity_pow_self hp.ne_zero (prime_iff.mp hp).not_unit n

/-- **Legendre's Theorem**

The multiplicity of a prime in `n!` is the sum of the quotients `n / p ^ i`. This sum is expressed
over the finset `Ico 1 b` where `b` is any bound greater than `log p n`. -/
lemma multiplicity_factorial {p : ℕ} (hp : p.prime) :
  ∀ {n b : ℕ}, log p n < b → multiplicity p n! = (∑ i in Ico 1 b, n / p ^ i : ℕ)
| 0     b hb := by simp [Ico, hp.multiplicity_one]
| (n+1) b hb :=
  calc multiplicity p (n+1)! = multiplicity p n! + multiplicity p (n+1) :
    by rw [factorial_succ, hp.multiplicity_mul, add_comm]
  ... = (∑ i in Ico 1 b, n / p ^ i : ℕ) + ((finset.Ico 1 b).filter (λ i, p ^ i ∣ n+1)).card :
    by rw [multiplicity_factorial ((log_le_log_of_le $ le_succ _).trans_lt hb),
      ← multiplicity_eq_card_pow_dvd hp.ne_one (succ_pos _) hb]
  ... = (∑ i in Ico 1 b, (n / p ^ i + if p^i ∣ n+1 then 1 else 0) : ℕ) :
    by { rw [sum_add_distrib, sum_boole], simp }
  ... = (∑ i in Ico 1 b, (n + 1) / p ^ i : ℕ) :
    congr_arg coe $ finset.sum_congr rfl $ λ _ _, (succ_div _ _).symm

/-- The multiplicity of `p` in `(p * (n + 1))!` is one more than the sum
  of the multiplicities of `p` in `(p * n)!` and `n + 1`. -/
lemma multiplicity_factorial_mul_succ {n p : ℕ} (hp : p.prime) :
  multiplicity p (p * (n + 1))! = multiplicity p (p * n)! + multiplicity p (n + 1) + 1 :=
begin
  have hp' := prime_iff.mp hp,
  have h0 : 2 ≤ p := hp.two_le,
  have h1 : 1 ≤ p * n + 1 := nat.le_add_left _ _,
  have h2 : p * n + 1 ≤ p * (n + 1), linarith,
  have h3 : p * n + 1 ≤ p * (n + 1) + 1, linarith,
  have hm : multiplicity p (p * n)! ≠ ⊤,
  { rw [ne.def, eq_top_iff_not_finite, not_not, finite_nat_iff],
    exact ⟨hp.ne_one, factorial_pos _⟩ },
  revert hm,
  have h4 : ∀ m ∈ Ico (p * n + 1) (p * (n + 1)), multiplicity p m = 0,
  { intros m hm, apply multiplicity_eq_zero_of_not_dvd,
    rw [← exists_lt_and_lt_iff_not_dvd _ (pos_iff_ne_zero.mpr hp.ne_zero)], rw [Ico.mem] at hm,
    exact ⟨n, lt_of_succ_le hm.1, hm.2⟩ },
  simp_rw [← prod_Ico_id_eq_factorial, multiplicity.finset.prod hp', ← sum_Ico_consecutive _ h1 h3,
    add_assoc], intro h,
  rw [enat.add_left_cancel_iff h, sum_Ico_succ_top h2, multiplicity.mul hp',
    hp.multiplicity_self, sum_congr rfl h4, sum_const_zero, zero_add,
    add_comm (1 : enat)]
end

/-- The multiplicity of `p` in `(p * n)!` is `n` more than that of `n!`. -/
lemma multiplicity_factorial_mul {n p : ℕ} (hp : p.prime) :
  multiplicity p (p * n)! = multiplicity p n! + n :=
begin
  induction n with n ih,
  { simp },
  { simp only [succ_eq_add_one, multiplicity.mul, hp, prime_iff.mp hp, ih,
      multiplicity_factorial_mul_succ, ←add_assoc, enat.coe_one, enat.coe_add, factorial_succ],
    congr' 1,
    rw [add_comm, add_assoc] }
end

/-- A prime power divides `n!` iff it is at most the sum of the quotients `n / p ^ i`.
  This sum is expressed over the set `Ico 1 b` where `b` is any bound greater than `log p n` -/
lemma pow_dvd_factorial_iff {p : ℕ} {n r b : ℕ} (hp : p.prime) (hbn : log p n < b) :
   p ^ r ∣ n! ↔ r ≤ ∑ i in Ico 1 b, n / p ^ i :=
by rw [← enat.coe_le_coe, ← hp.multiplicity_factorial hbn, ← pow_dvd_iff_le_multiplicity]

lemma multiplicity_factorial_le_div_pred {p : ℕ} (hp : p.prime) (n : ℕ) :
  multiplicity p n! ≤ (n/(p - 1) : ℕ) :=
begin
  rw [hp.multiplicity_factorial (lt_succ_self _), enat.coe_le_coe],
  exact nat.geom_sum_Ico_le hp.two_le _ _,
end

lemma multiplicity_choose_aux {p n b k : ℕ} (hp : p.prime) (hkn : k ≤ n) :
  ∑ i in finset.Ico 1 b, n / p ^ i =
  ∑ i in finset.Ico 1 b, k / p ^ i + ∑ i in finset.Ico 1 b, (n - k) / p ^ i +
  ((finset.Ico 1 b).filter (λ i, p ^ i ≤ k % p ^ i + (n - k) % p ^ i)).card :=
calc ∑ i in finset.Ico 1 b, n / p ^ i
    = ∑ i in finset.Ico 1 b, (k + (n - k)) / p ^ i :
    by simp only [nat.add_sub_cancel' hkn]
... = ∑ i in finset.Ico 1 b, (k / p ^ i + (n - k) / p ^ i +
      if p ^ i ≤ k % p ^ i + (n - k) % p ^ i then 1 else 0) :
    by simp only [nat.add_div (pow_pos hp.pos _)]
... = _ : by simp [sum_add_distrib, sum_boole]

/-- The multiplicity of `p` in `choose n k` is the number of carries when `k` and `n - k`
  are added in base `p`. The set is expressed by filtering `Ico 1 b` where `b`
  is any bound greater than `log p n`. -/
lemma multiplicity_choose {p n k b : ℕ} (hp : p.prime) (hkn : k ≤ n) (hnb : log p n < b) :
  multiplicity p (choose n k) =
  ((Ico 1 b).filter (λ i, p ^ i ≤ k % p ^ i + (n - k) % p ^ i)).card :=
have h₁ : multiplicity p (choose n k) + multiplicity p (k! * (n - k)!) =
    ((finset.Ico 1 b).filter (λ i, p ^ i ≤ k % p ^ i + (n - k) % p ^ i)).card +
    multiplicity p (k! * (n - k)!),
  begin
    rw [← hp.multiplicity_mul, ← mul_assoc, choose_mul_factorial_mul_factorial hkn,
        hp.multiplicity_factorial hnb, hp.multiplicity_mul,
        hp.multiplicity_factorial ((log_le_log_of_le hkn).trans_lt hnb),
        hp.multiplicity_factorial (lt_of_le_of_lt (log_le_log_of_le (nat.sub_le_self _ _)) hnb),
        multiplicity_choose_aux hp hkn],
    simp [add_comm],
  end,
(enat.add_right_cancel_iff
  (enat.ne_top_iff_dom.2 $
    by exact finite_nat_iff.2
      ⟨ne_of_gt hp.one_lt, mul_pos (factorial_pos k) (factorial_pos (n - k))⟩)).1
  h₁

/-- A lower bound on the multiplicity of `p` in `choose n k`. -/
lemma multiplicity_le_multiplicity_choose_add {p : ℕ} (hp : p.prime) (n k : ℕ) :
  multiplicity p n ≤ multiplicity p (choose n k) + multiplicity p k :=
if hkn : n < k then by simp [choose_eq_zero_of_lt hkn]
else if hk0 : k = 0 then by simp [hk0]
else if hn0 : n = 0 then by cases k; simp [hn0, *] at *
else begin
  rw [multiplicity_choose hp (le_of_not_gt hkn) (lt_succ_self _),
    multiplicity_eq_card_pow_dvd (ne_of_gt hp.one_lt) (nat.pos_of_ne_zero hk0)
      (lt_succ_of_le (log_le_log_of_le (le_of_not_gt hkn))),
    multiplicity_eq_card_pow_dvd (ne_of_gt hp.one_lt) (nat.pos_of_ne_zero hn0) (lt_succ_self _),
    ← enat.coe_add, enat.coe_le_coe],
  calc ((Ico 1 (log p n).succ).filter (λ i, p ^ i ∣ n)).card
      ≤ ((Ico 1 (log p n).succ).filter (λ i, p ^ i ≤ k % p ^ i + (n - k) % p ^ i) ∪
        (Ico 1 (log p n).succ).filter (λ i, p ^ i ∣ k) ).card :
    card_le_of_subset $ λ i, begin
      have := @le_mod_add_mod_of_dvd_add_of_not_dvd k (n - k) (p ^ i),
      simp [nat.add_sub_cancel' (le_of_not_gt hkn)] at * {contextual := tt},
      tauto
    end
  ... ≤ ((Ico 1 (log p n).succ).filter (λ i, p ^ i ≤ k % p ^ i + (n - k) % p ^ i)).card +
        ((Ico 1 (log p n).succ).filter (λ i, p ^ i ∣ k)).card :
    card_union_le _ _
end

lemma multiplicity_choose_prime_pow {p n k : ℕ} (hp : p.prime)
  (hkn : k ≤ p ^ n) (hk0 : 0 < k) :
  multiplicity p (choose (p ^ n) k) + multiplicity p k = n :=
le_antisymm
  (have hdisj : disjoint
      ((Ico 1 n.succ).filter (λ i, p ^ i ≤ k % p ^ i + (p ^ n - k) % p ^ i))
      ((Ico 1 n.succ).filter (λ i, p ^ i ∣ k)),
    by simp [disjoint_right, *, dvd_iff_mod_eq_zero, nat.mod_lt _ (pow_pos hp.pos _)]
        {contextual := tt},
  begin
    rw [multiplicity_choose hp hkn (lt_succ_self _),
      multiplicity_eq_card_pow_dvd (ne_of_gt hp.one_lt) hk0
        (lt_succ_of_le (log_le_log_of_le hkn)),
      ← enat.coe_add, enat.coe_le_coe, log_pow hp.one_lt,
      ← card_disjoint_union hdisj, filter_union_right],
    have filter_le_Ico := (Ico 1 n.succ).card_filter_le _,
    rwa Ico.card 1 n.succ at filter_le_Ico,
  end)
  (by rw [← hp.multiplicity_pow_self];
    exact multiplicity_le_multiplicity_choose_add hp _ _)

end prime

lemma multiplicity_two_factorial_lt : ∀ {n : ℕ} (h : n ≠ 0), multiplicity 2 n! < n :=
begin
  have h2 := prime_iff.mp prime_two,
  refine binary_rec _ _,
  { contradiction },
  { intros b n ih h,
    by_cases hn : n = 0,
    { subst hn, simp at h, simp [h, one_right h2.not_unit, enat.zero_lt_one] },
    have : multiplicity 2 (2 * n)! < (2 * n : ℕ),
    { rw [prime_two.multiplicity_factorial_mul],
      refine (enat.add_lt_add_right (ih hn) (enat.coe_ne_top _)).trans_le _,
      rw [two_mul], norm_cast },
    cases b,
    { simpa [bit0_eq_two_mul n] },
    { suffices : multiplicity 2 (2 * n + 1) + multiplicity 2 (2 * n)! < ↑(2 * n) + 1,
      { simpa [succ_eq_add_one, multiplicity.mul, h2, prime_two, nat.bit1_eq_succ_bit0,
          bit0_eq_two_mul n] },
      rw [multiplicity_eq_zero_of_not_dvd (two_not_dvd_two_mul_add_one n), zero_add],
      refine this.trans _, exact_mod_cast lt_succ_self _ }}
end

end nat
