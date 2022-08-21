/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import algebra.big_operators.intervals
import algebra.geom_sum
import data.nat.bitwise
import data.nat.log
import data.nat.parity
import ring_theory.int.basic
import data.nat.factorization.basic

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

--------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------

-- TODO: Write versions of all these lemmas in terms of factorization instead of multiplicity

--------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------

-- Temp: Yaël is going to PR some lemmas about intervals
lemma Icc_insert_succ (n : ℕ): Icc 1 n.succ = insert n.succ (Icc 1 n) :=
 by { rw [←insert_erase (mem_Icc.2 ⟨succ_le_succ (zero_le n), rfl.le⟩),
      Icc_erase_right, Ico_succ_right] }

lemma pos_of_mem_Ico_one {n x : ℕ} (hx : x ∈ Ico 1 n) : 0 < x :=
succ_le_iff.mp (mem_Ico.1 hx).1

--------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------

-- TODO: PR these

lemma factorization_eq_zero_of_not_dvd {n p : ℕ} (h : ¬ p ∣ n) : n.factorization p = 0 :=
begin
  rw factorization_eq_zero_iff', simp [h],
end


lemma pow_eq_one_iff_of_ne_one (p r : ℕ) (hp : p ≠ 1) : p ^ r = 1 ↔ r = 0 :=
begin
  refine ⟨_, _⟩,
  { intro h,
    by_contra H,
    cases hp ((pow_eq_one_iff H).1 h) },
  { rintro rfl, simp },
end

lemma factorization_pow_self {p : ℕ} (pp : p.prime) (n : ℕ) : (p ^ n).factorization p = n :=
by simp [pp.factorization]


lemma factorization_eq_zero_of_remainder {p r : ℕ} (i : ℕ) (hr : ¬ p ∣ r) :
  (p * i + r).factorization p = 0 :=
begin
  apply factorization_eq_zero_of_not_dvd,
  rwa ←nat.dvd_add_iff_right ((dvd.intro i rfl)),
end

lemma factorization_eq_zero_iff_remainder {p r : ℕ} (i : ℕ) (pp : p.prime) (hr0 : r ≠ 0) :
  (¬ p ∣ r) ↔ (p * i + r).factorization p = 0 :=
begin
  refine ⟨factorization_eq_zero_of_remainder i, λ h, _⟩,
  rcases eq_or_ne i 0 with rfl | hi0, {
    simp only [mul_zero, zero_add] at h,
    simpa [pp, hr0] using (factorization_eq_zero_iff' _ _).1 h },
  rw factorization_eq_zero_iff' at h,
  simp only [pp, hr0, not_true, add_eq_zero_iff, and_false, or_false, false_or] at h,
  contrapose! h,
  rwa ←nat.dvd_add_iff_right ((dvd.intro i rfl)),
end




--------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------

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
        rw [mem_filter, mem_Ico, mem_Ico, lt_succ_iff, ←@part_enat.coe_le_coe i, part_enat.coe_get,
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

-- ^^^^ The counterparts of these are all already in data.nat.factorization.basic
--------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------
-- vvv Versions translated into `factorization` vvv

/-- **Legendre's Theorem**
The multiplicity of a prime in `n!` is the sum of the quotients `n / p ^ i` for `i ∈ Ico 1 n`. -/
lemma factorization_factorial {p : ℕ} (pp : p.prime) {n : ℕ} :
  n!.factorization p = (∑ i in Icc 1 n, n / p ^ i : ℕ) :=
begin
  induction n with n IHn, { simp },
  simp_rw [Icc_insert_succ, sum_insert (λ H, not_succ_le_self n (mem_Icc.1 H).2),
    nat.div_eq_zero (lt_pow_self pp.one_lt n.succ), zero_add, succ_div, sum_add_distrib, ←IHn,
    factorial_succ, factorization_mul (succ_ne_zero n) (factorial_ne_zero n), add_comm],
  simp [factorization_eq_card_pow_dvd n.succ pp, ←Ico_succ_right],
end

/--
The multiplicity of a prime in `n!` is the sum of the quotients `n / p ^ i`.
This sum is expressed over the finset `Ico 1 (log p n).succ`. -/
lemma factorization_factorial' {p : ℕ} (hp : p.prime) (n : ℕ) :
  ∀ {n : ℕ}, n!.factorization p = (∑ i in Ico 1 (log p n).succ, n / p ^ i : ℕ) :=
begin
  intro n,
  rcases n.eq_zero_or_pos with rfl | hn0, { simp },
  rcases lt_or_le n p with hnp | hnp, {
    have : log p n = 0, { rw log_eq_zero_iff, simp [hnp] },
    simp [this],
    rw factorization_eq_zero_iff',
    right, left,
    rw hp.dvd_factorial,
    simp [hnp] },
  rw factorization_factorial hp,
  rw ←Ico_succ_right,
  have := @sum_Ico_consecutive ℕ _ _ 1 (log p n).succ n.succ _ _,
  rw ←this,
  simp,
  {
    rintro x hx1 hx2,
    refine nat.div_eq_zero ((lt_pow_iff_log_lt hp.one_lt hn0).2 (succ_le_iff.1 hx1)),
   },
  { apply succ_le_succ,
    rw ←pow_le_iff_le_log hp.one_lt hn0,
    simp,
    exact succ_le_iff.mpr hn0,
  },
  { apply succ_le_succ,
    apply le_of_lt,
    rw ← lt_pow_iff_log_lt hp.one_lt hn0,
    exact lt_pow_self hp.one_lt n,
  },
end


/--
The multiplicity of a prime in `n!` is the sum of the quotients `n / p ^ i`.
This sum is expressed over the finset `Ico 1 b` where `b` is any bound greater than `log p n`. -/
lemma factorization_factorial'' {p : ℕ} (hp : p.prime) :
  ∀ {n b : ℕ}, log p n < b → n!.factorization p = (∑ i in Ico 1 b, n / p ^ i : ℕ) :=
begin
  rintro n b hbn,
  rcases n.eq_zero_or_pos with rfl | hn0, { simp },
  rw factorization_factorial' hp b,
  rw ← @sum_Ico_consecutive ℕ _ _ 1 (log p n).succ b _ (succ_le_iff.2 hbn),
  { simp,
    rintro x hx1 hx2,
    exact nat.div_eq_zero ((lt_pow_iff_log_lt hp.one_lt hn0).2 (succ_le_iff.1 hx1)) },
  { apply succ_le_succ, simp, },
end


/-- The multiplicity of `p` in `(p * (n + 1))!` is one more than the sum
  of the multiplicities of `p` in `(p * n)!` and `n + 1`. -/
lemma factorization_factorial_mul_succ {n p : ℕ} (hp : p.prime) :
  (p * (n + 1))!.factorization p = (p * n)!.factorization p + (n + 1).factorization p + 1 :=
begin

  have h1 : 1 ≤ p * n + 1 := nat.le_add_left _ _,
  have h2 : p * n + 1 ≤ p * (n + 1), linarith [hp.two_le],
  have h3 : p * n + 1 ≤ p * (n + 1) + 1, linarith,
  have h4 : ∀ m : ℕ, m ∈ Ico (p * n + 1) (p * (n + 1)) → m.factorization p = 0,
  { intros m hm,
    apply factorization_eq_zero_of_not_dvd,
    rw [← not_dvd_iff_between_consec_multiples _ (pos_iff_ne_zero.mpr hp.ne_zero)],
    rw [mem_Ico] at hm,
    exact ⟨n, lt_of_succ_le hm.1, hm.2⟩ },

  simp_rw [← prod_Ico_id_eq_factorial],
  simp_rw [factorization_prod (λ x hx, (pos_of_mem_Ico_one hx).ne')],
  rw ←sum_Ico_consecutive _ h1 h3,
  rw add_assoc,
  simp only [sum_apply', finsupp.coe_add, pi.add_apply],
  simp,

  rw [sum_Ico_succ_top h2],
  have := sum_eq_zero_iff.2 h4,
  simp [this],

  rw factorization_mul hp.ne_zero (succ_ne_zero n),
  simp,
  have : p.factorization p = 1, { simp [hp] },
  rw this,
  rw add_comm,

  -- intros x hx1 hx2,
  -- apply factorization_eq_zero_of_not_dvd,
  -- rw ←not_dvd_iff_between_consec_multiples x hp.pos,
  -- refine ⟨n, succ_le_iff.mp hx1, hx2⟩,
end


/-- The multiplicity of `p` in `(p * n)!` is `n` more than that of `n!`. -/
lemma factorization_factorial_mul {n p : ℕ} (hp : p.prime) :
  (p * n)!.factorization p = n!.factorization p + n :=
begin
  induction n with n ih, { simp },
  rw [factorization_factorial_mul_succ hp, ih, factorial_succ n, succ_eq_add_one,
      factorization_mul (succ_ne_zero n) (factorial_ne_zero n),  finsupp.coe_add, pi.add_apply],
  ring_nf,
end

/-- A prime power divides `n!` iff it is at most the sum of the quotients `n / p ^ i`.
  This sum is expressed over the set `Ico 1 b` where `b` is any bound greater than `log p n` -/
lemma pow_dvd_factorial_iff {p : ℕ} {n r b : ℕ} (hp : p.prime) (hbn : log p n < b) :
   p ^ r ∣ n! ↔ r ≤ ∑ i in Ico 1 b, n / p ^ i :=
begin
  rw ←factorization_factorial'' hp hbn,
  exact hp.pow_dvd_iff_le_factorization (factorial_ne_zero n),
end

lemma factorization_factorial_le_div_pred {p : ℕ} (hp : p.prime) (n : ℕ) :
  n!.factorization p ≤ (n/(p - 1) : ℕ) :=
by { rw hp.factorization_factorial, apply nat.geom_sum_Ico_le hp.two_le }



-- #exit



lemma factorization_choose_aux {p n b k : ℕ} (hp : p.prime) (hkn : k ≤ n) :
  ∑ i in finset.Ico 1 b, n / p ^ i =
  ∑ i in finset.Ico 1 b, k / p ^ i + ∑ i in finset.Ico 1 b, (n - k) / p ^ i +
  ((finset.Ico 1 b).filter (λ i, p ^ i ≤ k % p ^ i + (n - k) % p ^ i)).card :=
calc ∑ i in finset.Ico 1 b, n / p ^ i
    = ∑ i in finset.Ico 1 b, (k + (n - k)) / p ^ i :
    by simp only [add_tsub_cancel_of_le hkn]
... = ∑ i in finset.Ico 1 b, (k / p ^ i + (n - k) / p ^ i +
      if p ^ i ≤ k % p ^ i + (n - k) % p ^ i then 1 else 0) :
    by simp only [nat.add_div (pow_pos hp.pos _)]
... = _ : by simp [sum_add_distrib, sum_boole]


/-- The multiplicity of `p` in `choose n k` is the number of carries when `k` and `n - k`
  are added in base `p`. The set is expressed by filtering `Ico 1 b` where `b`
  is any bound greater than `log p n`. -/
lemma factorization_choose {p n k b : ℕ} (hp : p.prime) (hkn : k ≤ n) (hnb : log p n < b) :
  (choose n k).factorization p =
  ((Ico 1 b).filter (λ i, p ^ i ≤ k % p ^ i + (n - k) % p ^ i)).card :=
begin
  have h1 := (choose_pos hkn).ne',
  have h2 : (n.choose k * k! * (n - k)!).factorization p = n!.factorization p,
  { rw choose_mul_factorial_mul_factorial hkn },
  rw [factorization_mul (mul_ne_zero_iff.2 ⟨h1, factorial_ne_zero k⟩) (factorial_ne_zero (n-k)),
      factorization_mul h1 (factorial_ne_zero k)] at h2,
  simp_rw [finsupp.add_apply] at h2,
  rw [←@add_right_cancel_iff _ _ ((k!.factorization) p + ((n - k)!.factorization) p),
      ←add_assoc, h2,
      factorization_factorial'' hp hnb, factorization_choose_aux hp hkn,
      add_comm, add_right_inj,
      factorization_factorial'' hp (lt_of_le_of_lt (log_mono_right tsub_le_self) hnb),
      factorization_factorial'' hp (lt_of_le_of_lt (log_mono_right hkn) hnb)],
end


-- /-- A lower bound on the multiplicity of `p` in `choose n k`. -/
-- lemma multiplicity_le_multiplicity_choose_add {p : ℕ} (hp : p.prime) : ∀ (n k : ℕ),
--   multiplicity p n ≤ multiplicity p (choose n k) + multiplicity p k
-- | _     0     := by simp
-- | 0     (_+1) := by simp
-- | (n+1) (k+1) :=
-- begin
--   rw ← hp.multiplicity_mul,
--   refine multiplicity_le_multiplicity_of_dvd_right _,
--   rw [← succ_mul_choose_eq],
--   exact dvd_mul_right _ _
-- end

-- /-- A lower bound on the multiplicity of `p` in `choose n k`.
-- Note that this needs more assumptions on `n` and `k` than the corresponding lemma
-- `multiplicity_le_multiplicity_choose_add`. -/
-- lemma factorization_le_factorization_choose_add {p n k : ℕ} (hp : p.prime) (hk0 : k ≠ 0)
--   (hnk: k ≤ n) : n.factorization p ≤ (choose n k).factorization p + k.factorization p :=
-- begin
--   have h1 := multiplicity_le_multiplicity_choose_add hp n k ,
--   rcases eq_or_ne n 0 with rfl | hn0, { simp },
--   rw [multiplicity_eq_factorization hp hn0, multiplicity_eq_factorization hp hk0,
--       multiplicity_eq_factorization hp (choose_pos hnk).ne'] at h1,
--   norm_cast at h1,
--   exact h1,
-- end

/-- A lower bound on the multiplicity of `p` in `choose n k`.
Note that this needs more assumptions on `n` and `k` than the corresponding lemma
`multiplicity_le_multiplicity_choose_add`. -/
lemma factorization_le_factorization_choose_add {p : ℕ} (hp : p.prime) :
  ∀ {n k : ℕ}, k ≠ 0 → k ≤ n → n.factorization p ≤ (choose n k).factorization p + k.factorization p
| _     0     := by simp
| 0     (_+1) := by simp
| (n+1) (k+1) := by
  { rintro hk hkn,
    rw [←finsupp.add_apply,
      ←factorization_mul (λ H, not_lt_of_le hkn (choose_eq_zero_iff.1 H)) hk, ←succ_mul_choose_eq],
    have h1 := mul_ne_zero (succ_ne_zero n) ((choose_pos (succ_le_succ_iff.1 hkn)).ne'),
    have h2 := (factorization_le_iff_dvd (succ_ne_zero n) h1).2 (dvd_mul_right (n+1) (n.choose k)),
    exact finsupp.le_def.1 h2 p }


-- ^^^ Versions translated into `factorization` ^^^
--------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------
-- vvv Versions to translate into `factorization` vvv

-- lemma multiplicity_choose_prime_pow {p n k : ℕ} (hp : p.prime)
--   (hkn : k ≤ p ^ n) (hk0 : 0 < k) :
--   multiplicity p (choose (p ^ n) k) + multiplicity p k = n := sorry


-- lemma factorization_choose_prime_pow {p n k : ℕ} (hp : p.prime) (hkn : k ≤ p ^ n) (hk0 : 0 < k) :
--   (choose (p ^ n) k).factorization p + k.factorization p = n :=
-- begin
--   have H := multiplicity_choose_prime_pow hp hkn hk0,
--   have h1 := λ H, not_lt_of_le hkn (choose_eq_zero_iff.1 H),
--   rw [multiplicity_eq_factorization hp h1, multiplicity_eq_factorization hp hk0.ne'] at H,
--   norm_cast at H,
--   exact part_enat.coe_inj.1 H,
-- end

lemma factorization_choose_prime_pow {p n k : ℕ} (hp : p.prime) (hkn : k ≤ p ^ n) (hk0 : 0 < k) :
  (choose (p ^ n) k).factorization p + k.factorization p = n :=
begin
  refine le_antisymm _ _,
  { rw [factorization_choose hp hkn (lt_succ_self _), log_pow hp.one_lt,
        factorization_eq_card_pow_dvd k hp, ←card_disjoint_union],
    swap,
    { simp only [disjoint_right, mem_filter, mem_Ico, not_and, not_le, and_imp],
      rintro a - - h3,
      simp [dvd_iff_mod_eq_zero.1 h3, nat.mod_lt _ (pow_pos hp.pos _)] },
    rw [Ico_filter_pow_dvd_eq hp hk0.ne' hkn, ←Ico_succ_right, filter_union_right],
    refine le_trans ((Ico 1 n.succ).card_filter_le _) _,
    simp },
  { apply (factorization_pow_self hp n).symm.le.trans,
    exact factorization_le_factorization_choose_add hp hk0.ne' hkn },
end

end prime

-- lemma multiplicity_two_factorial_lt : ∀ {n : ℕ} (h : n ≠ 0), multiplicity 2 n! < n := sorry

-- lemma factorization_two_factorial_lt : ∀ {n : ℕ} (h : n ≠ 0), n!.factorization 2 < n :=
-- begin
--   rintro n hn0,
--   have H := multiplicity_two_factorial_lt hn0,
--   rw multiplicity_eq_factorization prime_two (factorial_ne_zero n) at H,
--   exact part_enat.coe_lt_coe.1 H,
-- end

lemma factorization_two_factorial_lt {n : ℕ} : (n ≠ 0) →  n!.factorization 2 < n :=
begin
  have H : ∀ i, (i!.factorization) 2 < i → ((2 * i)!.factorization) 2 < 2 * i,
  { intros i h,
    rw [prime_two.factorization_factorial_mul, two_mul],
    simp [h] },
  apply even_odd_rec n (λ n, (n ≠ 0) → n!.factorization 2 < n),
  { simp },
  { exact λ i hi2 hi3, H i (hi2 (mul_ne_zero_iff.1 hi3).2) },
  { rintro i hi2 hi3,
    rcases eq_or_ne i 0 with rfl | hi0, { simp },
    refine lt_of_le_of_lt _ ((H i (hi2 hi0)).trans (lt_succ_self _)),
    simp [factorial_succ, factorization_mul (succ_ne_zero _) (factorial_ne_zero _),
          factorization_eq_zero_of_remainder i (mt nat.dvd_one.1 (succ_succ_ne_one 0))] },
end

-- ^^^ Versions to translate into `factorization` ^^^
--------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------

-- vvv Original versions vvv

--------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------

#exit

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
    by rw [multiplicity_factorial ((log_mono_right $ le_succ _).trans_lt hb),
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
    rw [← not_dvd_iff_between_consec_multiples _ (pos_iff_ne_zero.mpr hp.ne_zero)],
    rw [mem_Ico] at hm,
    exact ⟨n, lt_of_succ_le hm.1, hm.2⟩ },
  simp_rw [← prod_Ico_id_eq_factorial, multiplicity.finset.prod hp', ← sum_Ico_consecutive _ h1 h3,
    add_assoc], intro h,
  rw [part_enat.add_left_cancel_iff h, sum_Ico_succ_top h2, multiplicity.mul hp',
    hp.multiplicity_self, sum_congr rfl h4, sum_const_zero, zero_add,
    add_comm (1 : part_enat)]
end

/-- The multiplicity of `p` in `(p * n)!` is `n` more than that of `n!`. -/
lemma multiplicity_factorial_mul {n p : ℕ} (hp : p.prime) :
  multiplicity p (p * n)! = multiplicity p n! + n :=
begin
  induction n with n ih,
  { simp },
  { simp only [succ_eq_add_one, multiplicity.mul, hp, prime_iff.mp hp, ih,
      multiplicity_factorial_mul_succ, ←add_assoc, nat.cast_one, nat.cast_add, factorial_succ],
    congr' 1,
    rw [add_comm, add_assoc] }
end

/-- A prime power divides `n!` iff it is at most the sum of the quotients `n / p ^ i`.
  This sum is expressed over the set `Ico 1 b` where `b` is any bound greater than `log p n` -/
lemma pow_dvd_factorial_iff {p : ℕ} {n r b : ℕ} (hp : p.prime) (hbn : log p n < b) :
   p ^ r ∣ n! ↔ r ≤ ∑ i in Ico 1 b, n / p ^ i :=
by rw [← part_enat.coe_le_coe, ← hp.multiplicity_factorial hbn, ← pow_dvd_iff_le_multiplicity]

lemma multiplicity_factorial_le_div_pred {p : ℕ} (hp : p.prime) (n : ℕ) :
  multiplicity p n! ≤ (n/(p - 1) : ℕ) :=
begin
  rw [hp.multiplicity_factorial (lt_succ_self _), part_enat.coe_le_coe],
  exact nat.geom_sum_Ico_le hp.two_le _ _,
end

lemma multiplicity_choose_aux {p n b k : ℕ} (hp : p.prime) (hkn : k ≤ n) :
  ∑ i in finset.Ico 1 b, n / p ^ i =
  ∑ i in finset.Ico 1 b, k / p ^ i + ∑ i in finset.Ico 1 b, (n - k) / p ^ i +
  ((finset.Ico 1 b).filter (λ i, p ^ i ≤ k % p ^ i + (n - k) % p ^ i)).card :=
calc ∑ i in finset.Ico 1 b, n / p ^ i
    = ∑ i in finset.Ico 1 b, (k + (n - k)) / p ^ i :
    by simp only [add_tsub_cancel_of_le hkn]
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
        hp.multiplicity_factorial ((log_mono_right hkn).trans_lt hnb),
        hp.multiplicity_factorial (lt_of_le_of_lt (log_mono_right tsub_le_self) hnb),
        multiplicity_choose_aux hp hkn],
    simp [add_comm],
  end,
(part_enat.add_right_cancel_iff
  (part_enat.ne_top_iff_dom.2 $
    by exact finite_nat_iff.2
      ⟨ne_of_gt hp.one_lt, mul_pos (factorial_pos k) (factorial_pos (n - k))⟩)).1
  h₁

/-- A lower bound on the multiplicity of `p` in `choose n k`. -/
lemma multiplicity_le_multiplicity_choose_add {p : ℕ} (hp : p.prime) : ∀ (n k : ℕ),
  multiplicity p n ≤ multiplicity p (choose n k) + multiplicity p k
| _     0     := by simp
| 0     (_+1) := by simp
| (n+1) (k+1) :=
begin
  rw ← hp.multiplicity_mul,
  refine multiplicity_le_multiplicity_of_dvd_right _,
  rw [← succ_mul_choose_eq],
  exact dvd_mul_right _ _
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
        (lt_succ_of_le (log_mono_right hkn)),
      ← nat.cast_add, part_enat.coe_le_coe, log_pow hp.one_lt,
      ← card_disjoint_union hdisj, filter_union_right],
    have filter_le_Ico := (Ico 1 n.succ).card_filter_le _,
    rwa card_Ico 1 n.succ at filter_le_Ico,
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
    { subst hn, simp at h, simp [h, one_right h2.not_unit, part_enat.zero_lt_one] },
    have : multiplicity 2 (2 * n)! < (2 * n : ℕ),
    { rw [prime_two.multiplicity_factorial_mul],
      refine (part_enat.add_lt_add_right (ih hn) (part_enat.coe_ne_top _)).trans_le _,
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
