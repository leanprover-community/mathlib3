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

lemma is_prime_pow_dvd_coprime {n a b : ℕ} (hab : coprime a b) (hn : is_prime_pow n) :
  n ∣ a * b ↔ n ∣ a ∨ n ∣ b :=
begin
  rcases eq_or_ne a 0 with rfl | ha,
  { simp only [coprime_zero_left] at hab,
    simp [hab, filter_singleton, not_is_prime_pow_one] },
  rcases eq_or_ne b 0 with rfl | hb,
  { simp only [coprime_zero_right] at hab,
    simp [hab, filter_singleton, not_is_prime_pow_one] },
  refine ⟨_, λ h, or.elim h (λ i, i.trans (dvd_mul_right _ _)) (λ i, i.trans (dvd_mul_left _ _))⟩,
  obtain ⟨p, k, hp, hk, rfl⟩ := (is_prime_pow_nat_iff _).1 hn,
  simp only [prime_pow_dvd_iff_le_factorization _ _ _ hp (mul_ne_zero ha hb),
    factorization_mul ha hb, prime_pow_dvd_iff_le_factorization _ _ _ hp ha,
    prime_pow_dvd_iff_le_factorization _ _ _ hp hb, pi.add_apply, finsupp.coe_add],
  have : a.factorization p = 0 ∨ b.factorization p = 0,
  { rw [←finsupp.not_mem_support_iff, ←finsupp.not_mem_support_iff, ←not_and_distrib, ←mem_inter],
    exact λ t, factorization_disjoint_of_coprime hab t },
  cases this;
  simp [this, imp_or_distrib],
end

lemma disjoint_divisors_filter_prime_pow {a b : ℕ} (hab : coprime a b) :
  disjoint (a.divisors.filter is_prime_pow) (b.divisors.filter is_prime_pow) :=
begin
  simp only [disjoint_left, mem_filter, and_imp, mem_divisors, not_and],
  rintro n han ha hn hbn hb -,
  exact hn.ne_one (eq_one_of_dvd_coprimes hab han hbn),
end

lemma mul_divisors_filter_prime_pow {a b : ℕ} (hab : coprime a b) :
  (a * b).divisors.filter is_prime_pow = (a.divisors ∪ b.divisors).filter is_prime_pow :=
begin
  rcases eq_or_ne a 0 with rfl | ha,
  { simp only [coprime_zero_left] at hab,
    simp [hab, filter_singleton, not_is_prime_pow_one] },
  rcases eq_or_ne b 0 with rfl | hb,
  { simp only [coprime_zero_right] at hab,
    simp [hab, filter_singleton, not_is_prime_pow_one] },
  ext n,
  simp only [ha, hb, mem_union, mem_filter, nat.mul_eq_zero, and_true, and.congr_left_iff, ne.def,
    not_false_iff, mem_divisors, or_self],
  apply is_prime_pow_dvd_coprime hab,
end

/-- Given `P 0`, `P 1`, and `P (p ^ k)` for positive prime powers, and a way to extend `P a` and
`P b` to `P (a * b)` when `a, b` are coprime, you can define `P` for all natural numbers. -/
@[elab_as_eliminator]
def rec_on_pos_prime_coprime' {P : ℕ → Sort*} (hp : ∀ p n : ℕ, prime p → 0 < n → P (p ^ n))
  (h0 : P 0) (h1 : P 1) (h : ∀ a b, 0 < a → 0 < b → coprime a b → P a → P b → P (a * b)) :
  ∀ a, P a :=
rec_on_prime_pow h0 h1 $ λ a p n hp' hpa ha,
  (h (p ^ n) a (pow_pos hp'.pos _) (nat.pos_of_ne_zero (λ t, by simpa [t] using hpa))
  (prime.coprime_pow_of_not_dvd hp' hpa).symm
  (if h : n = 0 then eq.rec h1 h.symm else hp p n hp' $ nat.pos_of_ne_zero h) ha)

/-- Given `P 0`, `P (p ^ k)` for all prime powers, and a way to extend `P a` and `P b` to
`P (a * b)` when `a, b` are coprime, you can define `P` for all natural numbers. -/
@[elab_as_eliminator]
def rec_on_prime_coprime' {P : ℕ → Sort*} (h0 : P 0) (hp : ∀ p n : ℕ, prime p → P (p ^ n))
  (h : ∀ a b, 0 < a → 0 < b → coprime a b → P a → P b → P (a * b)) : ∀ a, P a :=
rec_on_pos_prime_coprime' (λ p n h _, hp p n h) h0 (hp 2 0 prime_two) h

lemma von_mangoldt_sum {n : ℕ} :
  ∑ i in n.divisors, Λ i = real.log n :=
begin
  refine rec_on_prime_coprime' _ _ _ n,
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

@[to_additive]
lemma prod_divisors_antidiagonal {M : Type*} [comm_monoid M] (f : ℕ → ℕ → M) {n : ℕ} :
  ∏ i in n.divisors_antidiagonal, f i.1 i.2 = ∏ i in n.divisors, f i (n / i) :=
begin
  refine prod_bij (λ i _, i.1) _ _ _ _,
  { intro i,
    apply fst_mem_divisors_of_mem_antidiagonal },
  { rintro ⟨i, j⟩ hij,
    simp only [mem_divisors_antidiagonal, ne.def] at hij,
    rw [←hij.1, nat.mul_div_cancel_left],
    apply nat.pos_of_ne_zero,
    rintro rfl,
    simp only [zero_mul] at hij,
    apply hij.2 hij.1.symm },
  { simp only [and_imp, prod.forall, mem_divisors_antidiagonal, ne.def],
    rintro i₁ j₁ ⟨i₂, j₂⟩ h - (rfl : i₂ * j₂ = _) h₁ (rfl : _ = i₂),
    simp only [nat.mul_eq_zero, not_or_distrib, ←ne.def] at h₁,
    rw mul_right_inj' h₁.1 at h,
    simp [h] },
  simp only [and_imp, exists_prop, mem_divisors_antidiagonal, exists_and_distrib_right, ne.def,
    exists_eq_right', mem_divisors, prod.exists],
  rintro _ ⟨k, rfl⟩ hn,
  exact ⟨⟨k, rfl⟩, hn⟩,
end

@[to_additive]
lemma prod_divisors_antidiagonal' {M : Type*} [comm_monoid M] (f : ℕ → ℕ → M) {n : ℕ} :
  ∏ i in n.divisors_antidiagonal, f i.1 i.2 = ∏ i in n.divisors, f (n / i) i :=
begin
  rw [←map_swap_divisors_antidiagonal, finset.prod_map],
  exact prod_divisors_antidiagonal (λ i j, f j i),
end

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
