/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import algebra.is_prime_pow
import number_theory.arithmetic_function
import analysis.special_functions.log

namespace nat
namespace arithmetic_function

open finset

open_locale arithmetic_function

/-- `log` as an arithmetic function `ℕ → ℝ`. Note this is in the `nat.arithmetic_function`
namespace to indicate that it is bundled as an `arithmetic_function` rather than being the usual
real logarithm. -/
noncomputable def log : arithmetic_function ℝ :=
⟨λ n, real.log n, by simp⟩

@[simp] lemma log_apply {n : ℕ} : log n = real.log n := rfl

/-- In the case when `n` is a prime power, `min_fac` will give the appropriate prime. -/
noncomputable def von_mangoldt : arithmetic_function ℝ :=
⟨λ n, if is_prime_pow n then real.log (min_fac n) else 0, if_neg not_is_prime_pow_zero⟩

localized "notation `Λ` := nat.arithmetic_function.von_mangoldt" in arithmetic_function

lemma von_mangoldt_apply {n : ℕ} :
  Λ n = if is_prime_pow n then real.log (min_fac n) else 0 := rfl

@[simp] lemma von_mangoldt_apply_one : Λ 1 = 0 := by simp [von_mangoldt_apply]

lemma is_prime_pow_pow_iff {n k : ℕ} (hk : k ≠ 0) :
  is_prime_pow (n ^ k) ↔ is_prime_pow n :=
begin
  simp only [is_prime_pow_iff_unique_prime_dvd],
  apply exists_unique_congr,
  simp only [and.congr_right_iff],
  intros p hp,
  exact ⟨hp.dvd_of_dvd_pow, λ t, t.trans (dvd_pow_self _ hk)⟩,
end

lemma von_mangoldt_apply_pow {n k : ℕ} (hk : k ≠ 0) : Λ (n ^ k) = Λ n :=
by simp only [von_mangoldt_apply, is_prime_pow_pow_iff hk, pow_min_fac hk]

lemma von_mangoldt_apply_prime {p : ℕ} (hp : p.prime) : Λ p = real.log p :=
by rw [von_mangoldt_apply, prime.min_fac_eq hp, if_pos (nat.prime_iff.1 hp).is_prime_pow]

open_locale big_operators

lemma von_mangoldt_sum {n : ℕ} :
  ∑ i in n.divisors, Λ i = real.log n :=
begin
  refine rec_on_prime_coprime _ _ _ n,
  { simp },
  { intros p k hp,
    rw [sum_divisors_prime_pow hp, cast_pow, real.log_pow, finset.sum_range_succ', pow_zero,
      von_mangoldt_apply_one],
    simp [von_mangoldt_apply_pow (nat.succ_ne_zero _), von_mangoldt_apply_prime hp] },
  intros a b ha' hb' hab ha hb,
  simp only [von_mangoldt_apply, ←sum_filter] at ha hb ⊢,
  rw [mul_divisors_filter_prime_pow hab, filter_union,
    sum_union (disjoint_divisors_filter_prime_pow hab), ha, hb, nat.cast_mul,
    real.log_mul (nat.cast_ne_zero.2 ha'.ne') (nat.cast_ne_zero.2 hb'.ne')],
end

lemma von_mangoldt_mul_zeta : Λ * ζ = log :=
by { ext n, rw [coe_mul_zeta_apply, von_mangoldt_sum], refl }

lemma log_mul_moebius_eq_von_mangoldt : log * μ = Λ :=
by rw [←von_mangoldt_mul_zeta, mul_assoc, coe_zeta_mul_coe_moebius, mul_one]

lemma sum_moebius_mul_log_eq {n : ℕ} :
  ∑ d in n.divisors, (μ d : ℝ) * log d = - Λ n :=
begin
  simp only [←log_mul_moebius_eq_von_mangoldt, mul_comm log, mul_apply, log_apply, int_coe_apply,
    ←finset.sum_neg_distrib, neg_mul_eq_mul_neg],
  rw sum_divisors_antidiagonal (λ i j, (μ i : ℝ) * -real.log j),
  have : ∑ (i : ℕ) in n.divisors, (μ i : ℝ) * -real.log (n / i : ℕ) =
         ∑ (i : ℕ) in n.divisors, ((μ i : ℝ) * real.log i - μ i * real.log n),
  { apply sum_congr rfl,
    simp only [and_imp, int.cast_eq_zero, mul_eq_mul_left_iff, ne.def, neg_inj, mem_divisors],
    intros m mn hn,
    have : (m : ℝ) ≠ 0,
    { rw [cast_ne_zero],
      rintro rfl,
      exact hn (by simpa using mn) },
    rw [nat.cast_dvd mn this, real.log_div (cast_ne_zero.2 hn) this, neg_sub, mul_sub] },
  rw [this, sum_sub_distrib, ←sum_mul, ←int.cast_sum, ←coe_mul_zeta_apply, eq_comm, sub_eq_self,
    moebius_mul_coe_zeta, mul_eq_zero, int.cast_eq_zero],
  rcases eq_or_ne n 1 with hn | hn;
  simp [hn],
end

end arithmetic_function
end nat
