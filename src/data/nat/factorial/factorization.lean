/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Stuart Presnell
-/
import algebra.big_operators.intervals
import algebra.geom_sum
import data.nat.bitwise
import data.nat.log
import data.nat.parity
import ring_theory.int.basic
import data.nat.factorization.basic

/-!
# Factorizations of factorials

This file contains lemmas about the factorization of factorials.

TODO: Update this docstring

## Multiplicity calculations

* `nat.multiplicity_factorial`: Legendre's Theorem. The multiplicity of `p` in `n!` is
  `n/p + ... + n/p^b` for any `b` such that `n/p^(b + 1) = 0`.
* `nat.multiplicity_factorial_mul`: The multiplicity of `p` in `(p * n)!` is `n` more than that of
  `n!`.

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


-- TODO: Update these `open`s
open finset nat multiplicity
open_locale big_operators nat

namespace nat

--------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------

-- Temp: Yaël is going to PR some lemmas about intervals
@[simp]
lemma Icc_insert_succ (n : ℕ): insert n.succ (Icc 1 n) = Icc 1 n.succ :=
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


--------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------


namespace prime

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
  simp_rw [←Icc_insert_succ, sum_insert (λ H, not_succ_le_self n (mem_Icc.1 H).2),
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




end prime

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

-- ^^^ Versions translated into `factorization` ^^^
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
