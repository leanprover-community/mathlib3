/-
Copyright (c) 2022 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
import algebra.parity
import data.nat.factorization

/-! ### Square root of squares

Throughout mathlib, there are several types `α` for which a notion of `sqrt` has been defined.
For instance, `nat.sqrt`, `int.sqrt`, `nnreal.sqrt`, and `real.sqrt`. In most cases, `sqrt x` is
defined as the greatest `y ∈ α` such that `y * y ≤ x` or `0` if no such `y` exists.

But this definition has some limits. For example, it's not true for `rat.sqrt`. (Indeed, the
squares are dense in the positive reals, so such a definintion can't work for the rationals.)

The following definition offers a different take on how to handle the "undefined" aspect of
`sqrt`. Specifically, in `ℕ`, if `¬is_square x`, then we'll define `sqrt0 x = 0`. Otherwise, we'll
define `sqrt0 x` as the (unique) `y` such that `x = y * y`.

`TODO`: For now, we only define `sqrt0` for the natural numbers. This could be generalized to a
`unique_factorization_monoid`, but there is a choice to make about units. Consider `ℤ` where we
would like `sqrt0 1 = 1` but `(-1 : ℤ) * (-1) = 1` as well. In number theory, there are ways to
consistently make this choice in totally real fields, but it gets tricky in any other instance.
As such, before having a specific need to address, we leave this for future considerations.
-/

section sqrt0

namespace nat

/-- If `x` is a square, return its square root. Else, return 0. -/
def sqrt0 (x : ℕ) := ite (is_square x) (sqrt x) 0

lemma sqrt0_zero : sqrt0 0 = 0 := by simp only [sqrt0, is_square_zero, if_true, sqrt_zero]

lemma sqrt0_one : sqrt0 1 = 1 := by simp only [sqrt0, is_square_one, if_true, sqrt_one]

lemma sqrt0_square {x : ℕ} (hsquare : is_square x) : sqrt0 x = sqrt x :=
by simp only [sqrt0, hsquare, if_true]

lemma sqrt0_not_square {x : ℕ} (hsquare : ¬is_square x) : sqrt0 x = 0 :=
by simp only [sqrt0, hsquare, if_false]

lemma sqrt0_prime {p : ℕ} (hp : nat.prime p) : sqrt0 p = 0 :=
begin
  simp only [sqrt0, ite_eq_right_iff],
  intros p,
  exfalso,
  exact (nat.prime_iff.mp hp).not_square p,
end

lemma sqrt0_eq {n : ℕ} : sqrt0 (n * n) = n :=
begin
  have : is_square (n * n), use n,
  simp only [sqrt0, sqrt_eq, this, if_true],
end

/-- `sqrt0` is multiplicative. Note that coprimality is necessary. -/
lemma sqrt0_mul {a b : ℕ} (hab : a.coprime b) : sqrt0 (a * b) = (sqrt0 a) * (sqrt0 b) :=
begin
  by_cases ha : is_square a,
  { by_cases hb : is_square b,
    { have : is_square (a * b), exact ha.mul_is_square hb,
      simp only [sqrt0, ha, hb, this, if_true],
      cases ha with a' ha',
      cases hb with b' hb',
      have : a' * a' * (b' * b') = (a' * b') * (a' * b'), ring,
      rw [ha', hb', this],
      rw [sqrt_eq, sqrt_eq, sqrt_eq], },
    { have : ¬(is_square a ∧ is_square b), simp only [hb, and_false, not_false_iff],
      simp [sqrt0, ha, hb, (is_square_mul hab).not.mpr this], }, },
  { have : ¬(is_square a ∧ is_square b), simp only [ha, false_and, not_false_iff],
    simp [sqrt0, ha, (is_square_mul hab).not.mpr this], },
end

end nat

end sqrt0
