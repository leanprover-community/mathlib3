/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.group_with_zero.power
import algebra.order.field
/-!
# Powers of elements of linear ordered fields

Some results on integer powers of elements of a linear ordered field.
These results are in their own file because they depend both on
`linear_ordered_field` and on `zpow`; neither should be obviously
an ancestor of the other.
-/

section
variables {R : Type*} [linear_ordered_field R] {a : R}

lemma pow_minus_two_nonneg : 0 ≤ a^(-2 : ℤ) :=
begin
  simp only [inv_nonneg, zpow_neg],
  change 0 ≤ a ^ ((2 : ℕ) : ℤ),
  rw zpow_coe_nat,
  apply sq_nonneg,
end

end
