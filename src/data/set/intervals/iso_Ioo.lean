/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import order.monotone.odd
import tactic.field_simp

/-!
# Order isomorphism between a linear ordered field and `(-1, 1)`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we provide an order isomorphism `order_iso_Ioo_neg_one_one` between the open interval
`(-1, 1)` in a linear ordered field and the whole field.
-/

open set

/-- In a linear ordered field, the whole field is order isomorphic to the open interval `(-1, 1)`.
We consider the actual implementation to be a "black box", so it is irreducible.
-/
@[irreducible] def order_iso_Ioo_neg_one_one (k : Type*) [linear_ordered_field k] :
  k ≃o Ioo (-1 : k) 1 :=
begin
  refine strict_mono.order_iso_of_right_inverse _ _ (λ x, x / (1 - |x|)) _,
  { refine cod_restrict (λ x, x / (1 + |x|)) _ (λ x, abs_lt.1 _),
    have H : 0 < 1 + |x|, from (abs_nonneg x).trans_lt (lt_one_add _),
    calc |x / (1 + |x|)| = |x| / (1 + |x|) : by rw [abs_div, abs_of_pos H]
                     ... < 1               : (div_lt_one H).2 (lt_one_add _) },
  { refine (strict_mono_of_odd_strict_mono_on_nonneg _ _).cod_restrict _,
    { intro x, simp only [abs_neg, neg_div] },
    { rintros x (hx : 0 ≤ x) y (hy : 0 ≤ y) hxy,
      simp [abs_of_nonneg, mul_add, mul_comm x y, div_lt_div_iff,
        hx.trans_lt (lt_one_add _), hy.trans_lt (lt_one_add _), *] } },
  { refine λ x, subtype.ext _,
    have : 0 < 1 - |(x : k)|, from sub_pos.2 (abs_lt.2 x.2),
    field_simp [abs_div, this.ne', abs_of_pos this] }
end
