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

 `n.factorization` is the finitely supported function `ℕ →₀ ℕ`
 mapping each prime factor of `n` to its multiplicity in `n`.  For example, since 2000 = 2^4 * 5^3,
  * `factorization 2000 2` is 4
  * `factorization 2000 5` is 3
  * `factorization 2000 k` is 0 for all other `k : ℕ`.
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
