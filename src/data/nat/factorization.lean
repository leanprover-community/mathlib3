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
-/

open nat finset list finsupp
open_locale big_operators

namespace nat

/-- `n.factorization` is the finitely supported function `ℕ →₀ ℕ`
 mapping each prime factor of `n` to its multiplicity in `n`. -/
noncomputable def factorization (n : ℕ) : ℕ →₀ ℕ := (n.factors : multiset ℕ).to_finsupp

lemma factorization_eq_count {n p : ℕ} : n.factorization p = list.count p n.factors :=
by simp [factorization]

/-- Every nonzero natural number has a unique prime factorization -/
lemma factorization_inj : set.inj_on factorization { x : ℕ | x ≠ 0 } :=
λ a ha b hb h, eq_of_count_factors_eq
  (zero_lt_iff.mpr ha) (zero_lt_iff.mpr hb) (λ p, by simp [←factorization_eq_count, h])

@[simp] lemma factorization_zero : factorization 0 = 0  :=
by simp [factorization]

@[simp] lemma factorization_one : factorization 1 = 0 :=
by simp [factorization]

/-- The support of `n.factorization` is exactly `n.factors.to_finset` -/
@[simp] lemma support_factorization {n : ℕ} :
  n.factorization.support = n.factors.to_finset :=
by simpa [factorization, multiset.to_finsupp_support]

lemma factor_iff_mem_factorization {n p : ℕ} :
  (p ∈ n.factorization.support) ↔ (p ∈ n.factors) :=
by simp only [support_factorization, list.mem_to_finset]

/-- The only numbers with empty prime factorization are `0` and `1` -/
lemma factorization_eq_zero_iff (n : ℕ) : n.factorization = 0 ↔ n = 0 ∨ n = 1 :=
by simp [factorization, add_equiv.map_eq_zero_iff, multiset.coe_eq_zero]

/-- For nonzero `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
@[simp] lemma factorization_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
  (a * b).factorization = a.factorization + b.factorization :=
by { ext p, simp only [add_apply, factorization_eq_count,
  count_factors_mul_of_pos (zero_lt_iff.mpr ha) (zero_lt_iff.mpr hb)] }

/-- For any `p`, the power of `p` in `n^k` is `k` times the power in `n` -/
lemma factorization_pow {n k : ℕ} :
  factorization (n^k) = k • n.factorization :=
begin
  ext p,
  simp only [algebra.id.smul_eq_mul, finsupp.coe_smul, pi.smul_apply],
  simp only [factorization_eq_count, factors_count_pow],
end

/-- The only prime factor of prime `p` is `p` itself, with multiplicity `1` -/
@[simp] lemma prime.factorization {p : ℕ} (hp : prime p) :
  p.factorization = single p 1 :=
begin
  ext q,
  rw [factorization_eq_count, factors_prime hp],
  by_cases hqp : q = p,
  { rw hqp, simp },
  { rw finsupp.single_eq_of_ne (ne.symm hqp),
    exact count_eq_zero_of_not_mem ((not_iff_not_of_iff list.mem_singleton).mpr hqp) },
end

/-- For prime `p` the only prime factor of `p^k` is `p` with multiplicity `k` -/
@[simp] lemma prime.factorization_pow {p k : ℕ} (hp : prime p) :
  factorization (p^k) = single p k :=
by simp [factorization_pow, prime.factorization hp]

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
  simp only [finsupp.coe_add, pi.add_apply, factorization_eq_count],
  simp only [count_factors_mul_of_coprime hab],
end

/-- For coprime `a` and `b` the prime factorization `a * b` is the union of those of `a` and `b` -/
lemma factorization_mul_support_of_coprime {a b : ℕ} (hab : coprime a b) :
  (a * b).factorization.support =
    a.factorization.support ∪ b.factorization.support :=
begin
  rw factorization_mul_of_coprime hab,
  exact support_add_eq (factorization_disjoint_of_coprime hab),
end

/-- For any multiplicative function `f` with `f 1 = 1` and any `n > 0`,
we can evaluate `f n` by evaluating `f` at `p ^ k` over the factorization of `n` -/
lemma multiplicative_factorization {n : ℕ} {β : Type*} [comm_monoid β] {f : ℕ → β}
  (hn : 0 < n)
  (h_mult : ∀ x y : ℕ, coprime x y → f(x * y) = f x * f y)
  (hf : f 1 = 1) :
f n = n.factorization.prod (λ p k, f(p ^ k)) :=
begin
  apply @nat.rec_on_pos_prime_coprime
    (λ n, (0 < n) → (f n = n.factorization.prod (λ p k, f(p ^ k)))),

  -- Case for positive prime power p^k
  { intros p k hp hk hpk,
    rw prime.factorization_pow hp,
    rw finsupp.prod_single_index _,
    simpa using hf },

  -- Case for 0, trivially
  { simp },

  -- Case for 1
  { rintros -, rw [factorization_one, hf], simp },

  -- Case for coprime a and b
  { intros a b hab ha hb hab_pos,
    rw h_mult a b hab,
    rw ha (pos_of_mul_pos_right hab_pos (b.zero_le)),
    rw hb (pos_of_mul_pos_left hab_pos (a.zero_le)),
    rw factorization_mul_of_coprime hab,
    rw ←prod_add_index_of_disjoint,
    convert (factorization_disjoint_of_coprime hab),
      },

  exact hn,
end

end nat
