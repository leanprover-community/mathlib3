/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/
-- import data.nat.prime
-- import data.nat.mul_ind
import ring_theory.unique_factorization_domain

/-!
# Prime factorizations

For a unique factorization monoid `α` with a normalization function, `factorization n` is the
finitely supported function `α →₀ ℕ` mapping each prime factor of `n` to its multiplicity in `n`.
For example, since 2000 = 2^4 * 5^3,
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

lemma factorization_eq_count {n p : α} : factorization n p = count p (normalized_factors n) :=
by simp [factorization]

@[simp] lemma factorization_zero : factorization (0 : α) = 0 := by simp [factorization]

@[simp] lemma factorization_one : factorization (1 : α) = 0 := by simp [factorization]

/-- The support of `factorization n` is exactly `n.factors.to_finset` -/
@[simp] lemma support_factorization {n : α} :
  (factorization n).support = (normalized_factors n).to_finset :=
by simp [factorization, multiset.to_finsupp_support]

-- This is pretty trivial: delete it?
-- Is this used anywhere?  Can any uses be replaced with `support_factorization`?
-- Maybe the version for ℕ is more substantial?
lemma norm_factor_iff_mem_factorization {n p : α} :
  p ∈ (factorization n).support ↔ p ∈ normalized_factors n :=
by simp [support_factorization]

/-- For nonzero `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
@[simp] lemma factorization_mul {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) :
  factorization (a * b) = factorization a + factorization b :=
by simp [factorization, normalized_factors_mul ha hb]

/-- For any `p`, the power of `p` in `n^k` is `k` times the power in `n` -/
lemma factorization_pow {x : α} {n : ℕ} :
  factorization (x^n) = n • (factorization x) :=
by { ext, simp [factorization] }

-- /-- The only numbers with empty prime factorization are `0` and `1` -/
-- lemma factorization_eq_zero_iff (n : α) : factorization n = 0 ↔ n = 0 ∨ n = 1 :=
-- begin
--   split,
--     { simp only [add_equiv.map_eq_zero_iff, factorization],
--       intros h,
--       -- suggest,
--       -- have := normalized_factors,
--   --     -- rw h at this,
--       sorry},
--     { rintro (rfl | rfl), exact factorization_zero, exact factorization_one },
-- end


lemma factorization_inj' (a b: α) (ha: a ≠ 0) (hb: b ≠ 0) (h: factorization a = factorization b) :
   associated a b :=
begin
  simp only [factorization, add_equiv.apply_eq_iff_eq] at h,
  have ha' := normalized_factors_prod ha,
  rw h at ha',
  exact associated.trans ha'.symm (normalized_factors_prod hb),
end


-- lemma factorization_inj : set.inj_on factorization { x : α | x ≠ 0 } :=
-- begin
--   -- simp [factorization],

--   intros a ha b hb h,
--   simp at ha hb,
--   simp [factorization] at h,
--   -- library_search,

--   have ha' := normalized_factors_prod ha,
--   have hb' := normalized_factors_prod hb,
--   -- rw h at this,

--   have := irreducible_of_normalized_factor a,
--   have := @factors_unique α _ _ (normalized_factors a) (normalized_factors b),
--   --  eq_of_count_factors_eq (zero_lt_iff.mpr ha) (zero_lt_iff.mpr hb) _,
--   -- intros p,
--   -- have := (λ p, by simp [←factorization_eq_count, h]),
--   sorry,
-- end



end UFM

-- TODO: GENERALISE ALL THIS





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
