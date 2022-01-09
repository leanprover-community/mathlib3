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

/-- For `n > 0`, the product of `p_i ^ k_i` over the prime factorization of `n` equals `n` -/
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

/-- If the factorization of `n` contains just one prime `p` then `n` is a power of `p` -/
lemma prime_pow_of_factorization_single {n p k : ℕ} (hn : 0 < n)
  (h : n.factorization = single p k) : n = p ^ k :=
by { rw [factorization_prod_pow hn, h], simp }

---------------------------------------------------------------------------------------------------


end nat
