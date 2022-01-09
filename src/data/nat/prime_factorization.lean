/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/
import data.nat.prime
import data.nat.mul_ind
import data.nat.factorization

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
open_locale nat  -- to enable φ notation

namespace nat

/-- For `n > 0`, the product of `p_i ^ k_i` over the prime factorization of `n` equals `n`
THIS IS PROVED AS A ONE-LINE COROLLARY OF `multiplicative_factorization`;
THIS IS JUST INCLUDED HERE TO SHOW THAT IT CAN BE PROVED WITHOUT/BEFORE THAT LEMMA
-/
lemma factorization_prod_pow {n : ℕ} (hn : 0 < n) :
  n = n.factorization.prod pow :=
begin
  rw ←finsupp.prod_to_multiset,
  simp only [factorization, multiset.coe_prod, multiset.to_finsupp_to_multiset],
  exact (prod_factors hn).symm,
end


---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

/-- If a product over `n.factorization` doesn't use the multiplicities of the prime factors
then it's equal to the corresponding product over `n.factors.to_finset` -/
lemma rebase_prod_factorization {n : ℕ} {β : Type*} [comm_monoid β] (f : ℕ → β) :
  n.factorization.prod (λ p k, f p) = ∏ p in n.factors.to_finset, (f p) :=
by { apply prod_congr support_factorization, simp }

---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
-- From Bhavik Mehta's `prime-powers`

variables (n : ℕ)
def is_prime_pow : Prop :=
  ∃ (p k : ℕ), p.prime ∧ 0 < k ∧ p ^ k = n

lemma is_prime_pow_def :
  n.is_prime_pow ↔ ∃ (p k : ℕ), p.prime ∧ 0 < k ∧ p ^ k = n := iff.rfl

lemma not_is_prime_pow_zero : ¬ is_prime_pow 0 := sorry



lemma factorization_prod_pow_eq_self (n : ℕ) (hn : 0 < n) : n.factorization.prod pow = n := sorry

lemma is_prime_pow_iff_factorization_single :
  n.is_prime_pow ↔ ∃ p k : ℕ, 0 < k ∧ n.factorization = single p k :=
begin
  rw is_prime_pow_def,
    split,
    { rintros ⟨p, k, pp, hk, hn⟩, use [p, k, hk], simp [←hn, factorization_pow, pp.factorization] },
    { rintros ⟨p, k, hk, hn⟩,
      use [p, k],
      split,
      { apply prime_of_mem_factors,
        rw [←factor_iff_mem_factorization, hn],
        simp [ne_of_gt hk] },
      use hk,
      rcases n.eq_zero_or_pos with rfl | hn0,
      { rw [factorization_zero, eq_comm, single_eq_zero] at hn,
        subst hn,
        cases nat.lt_asymm hk hk },
      { rw [←factorization_prod_pow_eq_self n hn0, hn], simp } },
end


/-- If the factorization of `n` contains just one prime `p` then `n` is a power of `p` -/
lemma prime_pow_of_factorization_single {n p k : ℕ} (hn : 0 < n)
  (h : n.factorization = single p k) : n = p ^ k :=
by { rw [←factorization_prod_pow_eq_self n hn, h], simp }

---------------------------------------------------------------------------------------------------


end nat
