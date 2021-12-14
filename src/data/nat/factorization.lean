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

/-- Every positive natural number has a unique prime factorization -/
lemma factorization_eq_iff {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
  a.factorization = b.factorization ↔ a = b :=
⟨λ h, eq_of_count_factors_eq ha hb (λ p, by simp [←factorization_eq_count, h]), λ h, by rw h⟩

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
lemma factorization_eq_nil_iff (n : ℕ) : n.factorization = 0 ↔ n = 0 ∨ n = 1 :=
by simp [factorization, add_equiv.map_eq_zero_iff, multiset.coe_eq_zero]

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

end nat
