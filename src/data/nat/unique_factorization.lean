/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/

import data.nat.associated
import ring_theory.unique_factorization_domain

/-#

# Unique factorization in `ℕ`

This file defines the `unique_factorization_monoid` structure on the natural numbers.

## Main results

 * `nat.irreducible_iff_prime`: a non-unit natural number is only divisible by `1` iff it is prime
 * `nat.unique_factorization_monoid`: the natural numbers have unique factorization into irreducibles
 * `nat.factors_eq`: the multiset of elements of `nat.factors` is equal to the factors
   given by the `unique_factorization_monoid` instance

## Tags

prime factorization, prime factors, unique factorization, unique factors
-/

namespace nat

instance : wf_dvd_monoid ℕ :=
⟨begin
  apply rel_hom.well_founded _ (with_top.well_founded_lt nat.lt_wf),
  refine ⟨λ x, if x = 0 then ⊤ else x, _⟩,
  intros a b h,
  cases a,
  { exfalso, revert h, simp [dvd_not_unit] },
  cases b,
  {simp [succ_ne_zero, with_top.coe_lt_top]},
  cases dvd_and_not_dvd_iff.2 h with h1 h2,
  simp only [succ_ne_zero, with_top.coe_lt_coe, if_false],
  apply lt_of_le_of_ne (nat.le_of_dvd (nat.succ_pos _) h1) (λ con, h2 _),
  rw con,
end⟩

instance : unique_factorization_monoid ℕ :=
⟨λ _, nat.irreducible_iff_prime⟩

end nat

open unique_factorization_monoid

theorem nat.factors_eq {n : ℕ} : factors n = n.factors :=
begin
  cases n, {refl},
  rw [← multiset.rel_eq, ← associated_eq_eq],
  apply factors_unique (irreducible_of_factor) _,
  { rw [multiset.coe_prod, nat.prod_factors (nat.succ_pos _)],
    apply factors_prod (nat.succ_ne_zero _) },
  { apply_instance },
  { intros x hx,
    rw [nat.irreducible_iff_prime, ← nat.prime_iff],
    apply nat.mem_factors hx, }
end
