/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/

import algebra.geom_sum
import ring_theory.ideal.quotient

/-!
# Basic results in number theory

This file should contain basic results in number theory. So far, it only contains the essential
lemma in the construction of the ring of Witt vectors.

## Main statement

`dvd_sub_pow_of_dvd_sub` proves that for elements `a` and `b` in a commutative ring `R` and for
all natural numbers `p` and `k` if `p` divides `a-b` in `R`, then `p ^ (k + 1)` divides
`a ^ (p ^ k) - b ^ (p ^ k)`.
-/

section

open ideal ideal.quotient

lemma dvd_sub_pow_of_dvd_sub {R : Type*} [comm_ring R] {p : ℕ}
  {a b : R} (h : (p : R) ∣ a - b) (k : ℕ) :
  (p^(k+1) : R) ∣ a^(p^k) - b^(p^k) :=
begin
  induction k with k ih,
  { rwa [pow_one, pow_zero, pow_one, pow_one] },
  rw [pow_succ' p k, pow_mul, pow_mul, ← geom_sum₂_mul, pow_succ],
  refine mul_dvd_mul _ ih,
  let I : ideal R := span {p},
  let f : R →+* ideal.quotient I := mk I,
  have hp : (p : ideal.quotient I) = 0,
  { rw [← f.map_nat_cast, eq_zero_iff_mem, mem_span_singleton] },
  rw [← mem_span_singleton, ← ideal.quotient.eq] at h,
  rw [← mem_span_singleton, ← eq_zero_iff_mem, ring_hom.map_geom_sum₂,
      ring_hom.map_pow, ring_hom.map_pow, h, geom_sum₂_self, hp, zero_mul],
end

end
