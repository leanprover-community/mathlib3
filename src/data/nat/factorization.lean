/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/
import data.nat.prime
import data.nat.mul_ind

/-!
# Prime factorizations

 `n.factorization` is the finitely supported function `ℕ →₀ ℕ`
 mapping each prime factor of `n` to its multiplicity in `n`.  For example, since 2000 = 2^4 * 5^3,
  * `factorization 2000 2` is 4
  * `factorization 2000 5` is 3
  * `factorization 2000 k` is 0 for all other `k : ℕ`.

## TODO

* As discussed in this Zulip thread:
https://leanprover.zulipchat.com/#narrow/stream/217875/topic/Multiplicity.20in.20the.20naturals
We have lots of disparate ways of talking about the multiplicity of a prime
in a natural number, including `factors.count`, `padic_val_nat`, `multiplicity`,
and the material in `data/pnat/factors`.  Move some of this material to this file,
prove results about the relationships between these definitions,
and (where appropriate) choose a uniform canonical way of expressing these ideas.

* Moreover, the results here should be generalised to an arbitrary unique factorization monoid
with a normalization function, and then deduplicated.  The basics of this have been started in
`ring_theory/unique_factorization_domain`.

-/

open nat finset list finsupp
open_locale big_operators

namespace nat

/-- `n.factorization` is the finitely supported function `ℕ →₀ ℕ`
 mapping each prime factor of `n` to its multiplicity in `n`. -/
noncomputable def factorization (n : ℕ) : ℕ →₀ ℕ := (n.factors : multiset ℕ).to_finsupp

@[simp] lemma factors_count_eq {n p : ℕ} : n.factors.count p = n.factorization p :=
by simp [factorization]

lemma eq_of_count_factors_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
  (h : ∀ p : ℕ, a.factorization p = b.factorization p) : a = b :=
eq_of_perm_factors ha hb (by simpa only [list.perm_iff_count, factors_count_eq] using h)

/-- Every nonzero natural number has a unique prime factorization -/
lemma factorization_inj : set.inj_on factorization { x : ℕ | x ≠ 0 } :=
λ a ha b hb h, eq_of_count_factors_eq
  (zero_lt_iff.mpr ha) (zero_lt_iff.mpr hb) (λ p, by simp [h])

@[simp] lemma factorization_zero : factorization 0 = 0  :=
by simp [factorization]

@[simp] lemma factorization_one : factorization 1 = 0 :=
by simp [factorization]

/-- The support of `n.factorization` is exactly `n.factors.to_finset` -/
@[simp] lemma support_factorization {n : ℕ} :
  n.factorization.support = n.factors.to_finset :=
by simpa [factorization, multiset.to_finsupp_support]

lemma factor_iff_mem_factorization {n p : ℕ} : p ∈ n.factorization.support ↔ p ∈ n.factors :=
by simp only [support_factorization, list.mem_to_finset]

/-- The only numbers with empty prime factorization are `0` and `1` -/
lemma factorization_eq_zero_iff (n : ℕ) : n.factorization = 0 ↔ n = 0 ∨ n = 1 :=
by simp [factorization, add_equiv.map_eq_zero_iff, multiset.coe_eq_zero]

/-- For positive `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
lemma count_factors_mul_of_pos {p a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
  list.count p (a * b).factors = list.count p a.factors + list.count p b.factors :=
by rw [perm_iff_count.mp (perm_factors_mul_of_pos ha hb) p, count_append]

/-- For nonzero `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
@[simp] lemma factorization_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
  (a * b).factorization = a.factorization + b.factorization :=
by { ext p, simp only [add_apply, ←factorization_eq_count,
  count_factors_mul_of_pos (zero_lt_iff.mpr ha) (zero_lt_iff.mpr hb)] }

/-- For any `p`, the power of `p` in `n^k` is `k` times the power in `n` -/
lemma factorization_pow (n k : ℕ) :
  factorization (n^k) = k • n.factorization :=
begin
  induction k with k ih,
  { simp },
  rcases n.eq_zero_or_pos with rfl | hn,
  { simp },
  rw [pow_succ, factorization_mul hn.ne' (pow_ne_zero _ hn.ne'), ih, succ_eq_one_add, add_smul,
    one_smul],
end

/-- For coprime `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
lemma count_factors_mul_of_coprime {p a b : ℕ} (hab : coprime a b)  :
  list.count p (a * b).factors = list.count p a.factors + list.count p b.factors :=
by rw [perm_iff_count.mp (perm_factors_mul_of_coprime hab) p, count_append]

/-- If `p` is a prime factor of `a` then the power of `p` in `a` is the same that in `a * b`,
for any `b` coprime to `a`. -/
lemma factors_count_eq_of_coprime_left {p a b : ℕ} (hab : coprime a b) (hpa : p ∈ a.factors) :
  list.count p (a * b).factors = list.count p a.factors :=
begin
  rw count_factors_mul_of_coprime hab,
  simpa only [count_eq_zero_of_not_mem (coprime_factors_disjoint hab hpa)],
end

lemma pow_factors_count_dvd (n p : ℕ) :
  p ^ n.factors.count p ∣ n :=
begin
  by_cases hp : p.prime,
  { apply dvd_of_factors_subperm (pow_ne_zero _ hp.ne_zero),
    rw [hp.factors_pow, list.subperm_ext_iff],
    intros q hq,
    simp [list.eq_of_mem_repeat hq] },
  { rw count_eq_zero_of_not_mem (mt prime_of_mem_factors hp),
    simp },
end

/-- If `p` is a prime factor of `b` then the power of `p` in `b` is the same that in `a * b`,
for any `a` coprime to `b`. -/
lemma factors_count_eq_of_coprime_right {p a b : ℕ} (hab : coprime a b) (hpb : p ∈ b.factors) :
  list.count p (a * b).factors = list.count p b.factors :=
by { rw mul_comm, exact factors_count_eq_of_coprime_left (coprime_comm.mp hab) hpb }

/-- For `b > 0`, the power of `p` in `a * b` is at least that in `a` -/
lemma le_factors_count_mul_left {p a b : ℕ} (hb : 0 < b) :
  list.count p a.factors ≤ list.count p (a * b).factors :=
begin
  rcases a.eq_zero_or_pos with rfl | ha,
  { simp },
  { rw [perm.count_eq (perm_factors_mul_of_pos ha hb) p, count_append p], simp },
end

/-- For `a > 0`, the power of `p` in `a * b` is at least that in `b` -/
lemma le_factors_count_mul_right {p a b : ℕ} (ha : 0 < a) :
  list.count p b.factors ≤ list.count p (a * b).factors :=
by { rw mul_comm, apply le_factors_count_mul_left ha }

/-- The only prime factor of prime `p` is `p` itself, with multiplicity `1` -/
@[simp] lemma prime.factorization {p : ℕ} (hp : prime p) :
  p.factorization = single p 1 :=
begin
  ext q,
  rw [factorization_eq_count, factors_prime hp, single_apply, count_singleton', if_congr eq_comm];
  refl,
end

/-- For prime `p` the only prime factor of `p^k` is `p` with multiplicity `k` -/
@[simp] lemma prime.factorization_pow {p k : ℕ} (hp : prime p) :
  factorization (p^k) = single p k :=
by simp [factorization_pow, hp.factorization]

/-! ### Factorizations of pairs of coprime numbers -/

/-- The prime factorizations of coprime `a` and `b` are disjoint -/
lemma factorization_disjoint_of_coprime {a b : ℕ} (hab : coprime a b) :
  disjoint a.factorization.support b.factorization.support :=
by simpa only [support_factorization]
  using disjoint_to_finset_iff_disjoint.mpr (coprime_factors_disjoint hab)

/-- For coprime `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
lemma factorization_mul_of_coprime {a b : ℕ} (hab : coprime a b) :
  (a * b).factorization = a.factorization + b.factorization :=
begin
  ext q,
  simp only [finsupp.coe_add, add_apply, factorization_eq_count, count_factors_mul_of_coprime hab],
end

/-- For coprime `a` and `b` the prime factorization `a * b` is the union of those of `a` and `b` -/
lemma factorization_mul_support_of_coprime {a b : ℕ} (hab : coprime a b) :
  (a * b).factorization.support = a.factorization.support ∪ b.factorization.support :=
begin
  rw factorization_mul_of_coprime hab,
  exact support_add_eq (factorization_disjoint_of_coprime hab),
end

lemma factorization_mul_support_of_pos {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
  (a * b).factorization.support = a.factorization.support ∪ b.factorization.support :=
begin
  ext q,
  simp only [finset.mem_union, factor_iff_mem_factorization],
  rw mem_factors_mul_of_pos ha.bot_lt hb.bot_lt,
end

end nat
