/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import number_theory.zsqrtd.gaussian_int

/-!
# Sums of two squares

Proof of Fermat's theorem on the sum of two squares. Every prime congruent to 1 mod 4 is the sum
of two squares.

# Todo

Fully characterize the natural numbers that are the sum of two squares: those such that for every
prime p congruent to 3 mod 4, the largest power of p dividing them is even.
-/

section Fermat

open gaussian_int

/-- **Fermat's theorem on the sum of two squares**. Every prime congruent to 1 mod 4 is the sum
of two squares. Also known as **Fermat's Christmas theorem**. -/
lemma nat.prime.sq_add_sq {p : ℕ} [fact p.prime] (hp : p % 4 = 1) :
  ∃ a b : ℕ, a ^ 2 + b ^ 2 = p :=
begin
  apply sq_add_sq_of_nat_prime_of_not_irreducible p,
  rw [principal_ideal_ring.irreducible_iff_prime, prime_iff_mod_four_eq_three_of_nat_prime p, hp],
  norm_num
end

/-- A slightly stronger version of the two-squares theorem for prime numbers. -/
-- It probably makes sense to replace `nat.prime.sq_add_sq` by this version.
theorem nat.prime.sq_add_sq' {p : ℕ} [pp : fact (nat.prime p)] (hp : p % 4 ≠ 3) :
  ∃ (a b : ℕ), a ^ 2 + b ^ 2 = p :=
begin
  unfreezingI {rcases pp.1.eq_two_or_odd with rfl | h},
  { exact ⟨1, 1, rfl⟩, },
  { exact nat.prime.sq_add_sq ((nat.odd_mod_four_iff.mp h).resolve_right hp), }
end

end Fermat
