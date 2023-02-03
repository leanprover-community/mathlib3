/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/

import data.nat.factors
import data.set.finite

/-!
# Prime numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains some results about prime numbers which depend on finiteness of sets.
-/

namespace nat

/-- A version of `nat.exists_infinite_primes` using the `set.infinite` predicate. -/
lemma infinite_set_of_prime : {p | prime p}.infinite :=
set.infinite_of_not_bdd_above not_bdd_above_set_of_prime

/-- If `a`, `b` are positive, the prime divisors of `a * b` are the union of those of `a` and `b` -/
lemma factors_mul_to_finset {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
  (a * b).factors.to_finset = a.factors.to_finset ∪ b.factors.to_finset :=
(list.to_finset.ext $ λ x, (mem_factors_mul ha hb).trans list.mem_union.symm).trans $
  list.to_finset_union _ _

lemma pow_succ_factors_to_finset (n k : ℕ) :
  (n^(k+1)).factors.to_finset = n.factors.to_finset :=
begin
  rcases eq_or_ne n 0 with rfl | hn,
  { simp },
  induction k with k ih,
  { simp },
  rw [pow_succ, factors_mul_to_finset hn (pow_ne_zero _ hn), ih, finset.union_idempotent]
end

lemma pow_factors_to_finset (n : ℕ) {k : ℕ} (hk : k ≠ 0) :
  (n^k).factors.to_finset = n.factors.to_finset :=
begin
  cases k,
  { simpa using hk },
  rw pow_succ_factors_to_finset
end

/-- The only prime divisor of positive prime power `p^k` is `p` itself -/
lemma prime_pow_prime_divisor {p k : ℕ} (hk : k ≠ 0) (hp : prime p) :
  (p^k).factors.to_finset = {p} :=
by simp [pow_factors_to_finset p hk, factors_prime hp]

lemma factors_mul_to_finset_of_coprime {a b : ℕ} (hab : coprime a b) :
  (a * b).factors.to_finset = a.factors.to_finset ∪ b.factors.to_finset :=
(list.to_finset.ext $ mem_factors_mul_of_coprime hab).trans $ list.to_finset_union _ _

end nat
