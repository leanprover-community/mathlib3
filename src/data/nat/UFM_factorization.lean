/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/
-- import data.nat.prime
import data.nat.mul_ind
import ring_theory.unique_factorization_domain

/-!
# Prime factorizations

 `factorization n` is the finitely supported function `α →₀ ℕ`
 mapping each prime factor of `n` to its multiplicity in `n`.  For example, since 2000 = 2^4 * 5^3,
  * `factorization 2000 2` is 4
  * `factorization 2000 5` is 3
  * `factorization 2000 k` is 0 for all other `k : α`.
-/

-- open nat finset list finsupp
open finsupp multiset
open_locale big_operators



-- jcommelin: "I think this definition should be generalized to a unique factorization monoid that also has a normalization function.
-- TODO: Finish this, move to `ring_theory/unique_factorization_domain`?
section UFM
variables {α : Type*} [cancel_comm_monoid_with_zero α] [unique_factorization_monoid α]
variables [normalization_monoid α] [decidable_eq α]

open unique_factorization_monoid

noncomputable def factorization (n : α) : α →₀ ℕ := (normalized_factors n).to_finsupp
-- (normalized_factors n).to_finsupp

lemma factorization_eq_count {n p : α} : factorization n p = count p (normalized_factors n) :=
by simp [factorization]

@[simp] lemma factorization_zero : factorization 0 = 0 := by simp [factorization]

@[simp] lemma factorization_one : factorization 1 = 0 := by simp [factorization]

/-- For nonzero `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
@[simp] lemma factorization_mul {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) :
  factorization (a * b) = factorization a + factorization b :=
by simp [factorization, normalized_factors_mul ha hb]

/-- The support of `n.factorization` is exactly `n.factors.to_finset` -/
@[simp] lemma support_factorization {n : α} :
  (factorization n).support = (normalized_factors n).to_finset :=
by simp [factorization, multiset.to_finsupp_support]

lemma factor_iff_mem_factorization {n p : α} :
  (p ∈ (factorization n ).support) ↔ (p ∈ n.factors) :=
by simp only [support_factorization, list.mem_to_finset]


lemma factorization_inj : set.inj_on factorization { x : α | x ≠ 0 } :=
begin
  simp [factorization],

  intros a ha b hb h,
  simp at ha hb,
  -- library_search,
  have := @factors_unique α _ _,
  --  eq_of_count_factors_eq (zero_lt_iff.mpr ha) (zero_lt_iff.mpr hb) _,
  -- intros p,
  -- have := (λ p, by simp [←factorization_eq_count, h]),
  sorry,
end


end UFM

-- TODO: GENERALISE ALL THIS


-- /-- The only numbers with empty prime factorization are `0` and `1` -/
-- lemma factorization_eq_zero_iff (n : α) : n.factorization = 0 ↔ n = 0 ∨ n = 1 :=
-- by simp [factorization, add_equiv.map_eq_zero_iff, multiset.coe_eq_zero]

-- /-- For nonzero `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
-- @[simp] lemma factorization_mul {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) :
--   (a * b).factorization = a.factorization + b.factorization :=
-- by { ext p, simp only [add_apply, factorization_eq_count,
--   count_factors_mul_of_pos (zero_lt_iff.mpr ha) (zero_lt_iff.mpr hb)] }

-- /-- For any `p`, the power of `p` in `n^k` is `k` times the power in `n` -/
-- lemma factorization_pow {n k : α} :
--   factorization (n^k) = k • n.factorization :=
-- by { ext p, simp [factorization_eq_count, factors_count_pow] }

-- /-- The only prime factor of prime `p` is `p` itself, with multiplicity `1` -/
-- @[simp] lemma prime.factorization {p : α} (hp : prime p) :
--   p.factorization = single p 1 :=
-- begin
--   ext q,
--   rw [factorization_eq_count, factors_prime hp, single_apply, count_singleton', if_congr eq_comm];
--   refl,
-- end

-- /-- For prime `p` the only prime factor of `p^k` is `p` with multiplicity `k` -/
-- @[simp] lemma prime.factorization_pow {p k : α} (hp : prime p) :
--   factorization (p^k) = single p k :=
-- by simp [factorization_pow, hp.factorization]
