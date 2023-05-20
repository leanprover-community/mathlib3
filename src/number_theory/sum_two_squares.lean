/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import number_theory.zsqrtd.gaussian_int
import tactic.linear_combination

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

/-- **Fermat's theorem on the sum of two squares**. Every prime not congruent to 3 mod 4 is the sum
of two squares. Also known as **Fermat's Christmas theorem**. -/
theorem nat.prime.sq_add_sq {p : ℕ} [pp : fact (nat.prime p)] (hp : p % 4 ≠ 3) :
  ∃ (a b : ℕ), a ^ 2 + b ^ 2 = p :=
begin
  unfreezingI {rcases pp.1.eq_two_or_odd with rfl | h},
  { exact ⟨1, 1, rfl⟩, },
  { apply sq_add_sq_of_nat_prime_of_not_irreducible p,
    rwa [principal_ideal_ring.irreducible_iff_prime, prime_iff_mod_four_eq_three_of_nat_prime p], }
end

end Fermat

/-!
### Generalities on sums of two squares
-/

section general

/-- The set of sums of two squares is closed under multiplication in any commutative ring.
See also `sq_add_sq_mul_sq_add_sq`. -/
lemma sq_add_sq_mul {R} [comm_ring R] {a b x y u v : R} (ha : a = x ^ 2 + y ^ 2)
  (hb : b = u ^ 2 + v ^ 2) : ∃ r s : R, a * b = r ^ 2 + s ^ 2 :=
⟨x * u - y * v, x * v + y * u, by {rw [ha, hb], ring}⟩

/-- The set of naturals numbers that are sums of two squqares is closed under multiplication. -/
lemma nat.sq_add_sq_mul {a b x y u v : ℕ} (ha : a = x ^ 2 + y ^ 2) (hb : b = u ^ 2 + v ^ 2) :
  ∃ r s : ℕ, a * b = r ^ 2 + s ^ 2 :=
begin
  zify at ha hb ⊢,
  obtain ⟨r, s, h⟩ := sq_add_sq_mul ha hb,
  refine ⟨r.nat_abs, s.nat_abs, _⟩,
  simpa only [int.coe_nat_abs, sq_abs],
end

end general
