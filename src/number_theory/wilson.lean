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

-/

open_locale nat

namespace nat

/-- For `n > 1`, `(n-1)!` is congruent to `-1` modulo `n` only if n is prime. --/
private lemma wilsons_theorem_only_if_direction  (n : ℕ) [hyp: n > 1] :
(((n - 1)! : zmod n) = -1)  → (prime n):=
begin
  intro h,
  have hp2: ((n - 1)! + 1 : zmod n) = 0,
  rw h,
  simp,
  have hn_divides: n ∣(n-1)! + 1,
  rw ← zmod.nat_coe_zmod_eq_zero_iff_dvd,
  exact hp2,

  by_contradiction h2,
  obtain ⟨m⟩  := exists_dvd_of_not_prime2 hyp h2,
  have m_leq_n_minus_one : m ≤ (n-1),
  cases h_1.right,
  rw lt_iff_add_one_le at right,
  rw nat.add_le_to_le_sub at right,
  exact right,
  exact le_of_lt hyp,

  have hm_divides_fact : (m ∣(n-1)!),
  refine nat.dvd_factorial _ m_leq_n_minus_one,
  cases h_1.right,
  exact pos_of_gt left,
  cases h_1.left,
  rw h_2 at hn_divides hm_divides_fact,

  clear h h_2 h2 hp2 hyp m_leq_n_minus_one,

  have m_is_one: (m = 1), from
    nat.dvd_one.mp
    ((nat.dvd_add_right hm_divides_fact).mp (dvd_of_mul_right_dvd hn_divides)),

  cases h_1.right,
  linarith,
end

/-- **Wilson's Theorem**: For `n > 1`, `(n-1)!` is congruent to `-1` modulo `n` iff n is prime. --/
theorem wilsons_theorem (n : ℕ) [hyp: n > 1] :
  (prime n) ↔ (((n - 1)! : zmod n) = -1) :=
begin
  split,
  { intro hp, rw ← zmod.wilsons_lemma _, exact fact_iff.mpr hp },
  { apply wilsons_theorem_only_if_direction _, exact hyp }
end

end nat
