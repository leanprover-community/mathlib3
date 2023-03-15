/-
Copyright (c) 2022 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/

import data.nat.basic

/-! # A recursion principle based on even and odd numbers. 

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.-/

namespace nat

/-- Recursion principle on even and odd numbers: if we have `P 0`, and for all `i : ℕ` we can
extend from `P i` to both `P (2 * i)` and `P (2 * i + 1)`, then we have `P n` for all `n : ℕ`.
This is nothing more than a wrapper around `nat.binary_rec`, to avoid having to switch to
dealing with `bit0` and `bit1`. -/
@[elab_as_eliminator]
def even_odd_rec {P : ℕ → Sort*} (h0 : P 0)
  (h_even : ∀ n (ih : P n), P (2 * n))
  (h_odd : ∀ n (ih : P n), P (2 * n + 1)) (n : ℕ) : P n :=
begin
  refine @binary_rec P h0 (λ b i hi, _) n,
  cases b,
  { simpa [bit, bit0_val i] using h_even i hi },
  { simpa [bit, bit1_val i] using h_odd i hi },
end

@[simp] lemma even_odd_rec_zero (P : ℕ → Sort*) (h0 : P 0)
  (h_even : ∀ i, P i → P (2 * i)) (h_odd : ∀ i, P i → P (2 * i + 1)) :
  @even_odd_rec _ h0 h_even h_odd 0 = h0 := binary_rec_zero _ _

@[simp] lemma even_odd_rec_even (n : ℕ) (P : ℕ → Sort*) (h0 : P 0)
  (h_even : ∀ i, P i → P (2 * i)) (h_odd : ∀ i, P i → P (2 * i + 1))
  (H : h_even 0 h0 = h0) :
  @even_odd_rec _ h0 h_even h_odd (2 * n) = h_even n (even_odd_rec h0 h_even h_odd n) :=
begin
  convert binary_rec_eq _ ff n,
  { exact (bit0_eq_two_mul _).symm },
  { exact (bit0_eq_two_mul _).symm },
  { apply heq_of_cast_eq, refl },
  { exact H }
end

@[simp] lemma even_odd_rec_odd (n : ℕ) (P : ℕ → Sort*) (h0 : P 0)
  (h_even : ∀ i, P i → P (2 * i)) (h_odd : ∀ i, P i → P (2 * i + 1))
  (H : h_even 0 h0 = h0) :
  @even_odd_rec _ h0 h_even h_odd (2 * n + 1) = h_odd n (even_odd_rec h0 h_even h_odd n) :=
begin
  convert binary_rec_eq _ tt n,
  { exact (bit0_eq_two_mul _).symm },
  { exact (bit0_eq_two_mul _).symm },
  { apply heq_of_cast_eq, refl },
  { exact H }
end

end nat
