/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Eric Wieser
-/
import algebra.char_p.basic

/-! # `char_p R 0` and `char_zero R` need not coincide for semirings

For rings, the two notions coincide.

In fact, `char_p.of_char_zero` shows that `char_zero R` implies `char_p R 0` for any `char_zero`
`add_monoid R` with `1`.
The reverse implication holds for any `add_left_cancel_monoid R` with `1`, by `char_p_to_char_zero`.

This file shows that there are semiring `R` for which `char_p R 0` holds and `char_zero R` does not.

The example is `{0, 1}` with saturating addition.
-/

@[simp] lemma add_one_eq_one (x : with_zero unit) : x + 1 = 1 :=
with_zero.cases_on x (by refl) (λ h, by refl)

lemma with_zero_unit_char_p_zero : char_p (with_zero unit) 0 :=
⟨λ x, by cases x; simp⟩

lemma with_zero_unit_not_char_zero : ¬ char_zero (with_zero unit) :=
λ ⟨h⟩, h.ne (by simp : 1 + 1 ≠ 0 + 1) (by simp)
