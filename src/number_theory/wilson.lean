/-
Copyright (c) 2022 John Nicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicol
-/
import number_theory.legendre_symbol.gauss_eisenstein_lemmas

/-!
# Wilson's theorem.

This file contains a proof of Wilson's theorem.

The heavy lifting is mostly done by the previous `wilsons_lemma`,
but here we also prove the other logical direction.

This could be generalized to similar results about finite abelian groups.

## References

* [Wilson's Theorem](https://en.wikipedia.org/wiki/Wilson%27s_theorem)

## TODO

* Move `wilsons_lemma` into this file, and give it a descriptive name.
-/

open_locale nat

namespace nat
variable {n : ℕ}

/-- For `n ≠ 1`, `(n-1)!` is congruent to `-1` modulo `n` only if n is prime. -/
lemma prime_of_fac_equiv_neg_one
  (h : ((n - 1)! : zmod n) = -1) (h1 : n ≠ 1) : prime n :=
begin
  rcases eq_or_ne n 0 with rfl | h0,
  { norm_num at h },
  replace h1 : 1 < n := n.two_le_iff.mpr ⟨h0, h1⟩,
  by_contradiction h2,
  obtain ⟨m, hm1, hm2 : 1 < m, hm3⟩ := exists_dvd_of_not_prime2 h1 h2,
  have hm : m ∣ (n - 1)! := nat.dvd_factorial (pos_of_gt hm2) (le_pred_of_lt hm3),
  refine hm2.ne' (nat.dvd_one.mp ((nat.dvd_add_right hm).mp (hm1.trans _))),
  rw [←zmod.nat_coe_zmod_eq_zero_iff_dvd, cast_add, cast_one, h, add_left_neg],
end

/-- **Wilson's Theorem**: For `n ≠ 1`, `(n-1)!` is congruent to `-1` modulo `n` iff n is prime. -/
theorem prime_iff_fac_equiv_neg_one (h : n ≠ 1) :
  prime n ↔ ((n - 1)! : zmod n) = -1 :=
begin
  refine ⟨λ h1, _, λ h2, prime_of_fac_equiv_neg_one h2 h⟩,
  haveI := fact.mk h1,
  exact zmod.wilsons_lemma n,
end

end nat
