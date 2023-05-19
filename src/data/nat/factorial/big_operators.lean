/-
Copyright (c) 2022 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Pim Otte
-/
import data.nat.factorial.basic
import algebra.big_operators.order

/-!
# Factorial with big operators

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains some lemmas on factorials in combination with big operators.

While in terms of semantics they could be in the `basic.lean` file, importing 
`algebra.big_operators.basic` leads to a cyclic import.

-/

open_locale nat big_operators

namespace nat

variables {α : Type*} (s : finset α) (f : α → ℕ)

lemma prod_factorial_pos : 0 < ∏ i in s, (f i)! :=
finset.prod_pos (λ i _, factorial_pos (f i))

lemma prod_factorial_dvd_factorial_sum : (∏ i in s, (f i)!) ∣ (∑ i in s, f i)! :=
begin
  classical,
  induction s using finset.induction with a' s' has ih,
  { simp only [finset.sum_empty, finset.prod_empty, factorial], },
  { simp only [finset.prod_insert has, finset.sum_insert has],
    refine dvd_trans (mul_dvd_mul_left ((f a')!) ih) _,
    apply nat.factorial_mul_factorial_dvd_factorial_add, },
end

end nat
