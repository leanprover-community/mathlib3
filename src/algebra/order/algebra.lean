/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import algebra.algebra.basic
import algebra.order.module

/-!
# Ordered algebras

An ordered algebra is an ordered semiring, which is an algebra over an ordered commutative semiring,
for which scalar multiplication is "compatible" with the two orders.

The prototypical example is 2x2 matrices over the reals or complexes (or indeed any C^* algebra)
where the ordering the one determined by the positive cone of positive operators,
i.e. `A ≤ B` iff `B - A = star R * R` for some `R`.
(We don't yet have this example in mathlib.)

## Implementation

Because the axioms for an ordered algebra are exactly the same as those for the underlying
module being ordered, we don't actually introduce a new class, but just use the `ordered_smul`
mixin.

## Tags

ordered algebra
-/

section ordered_algebra

variables {R A : Type*} {a b : A} {r : R}

variables [ordered_comm_ring R] [ordered_ring A] [algebra R A] [ordered_smul R A]

lemma algebra_map_monotone : monotone (algebra_map R A) :=
λ a b h,
begin
  rw [algebra.algebra_map_eq_smul_one, algebra.algebra_map_eq_smul_one, ←sub_nonneg, ←sub_smul],
  transitivity (b - a) • (0 : A),
  { simp, },
  { exact smul_le_smul_of_nonneg zero_le_one (sub_nonneg.mpr h) }
end

end ordered_algebra

section instances

variables {R : Type*} [linear_ordered_comm_ring R]

instance linear_ordered_comm_ring.to_ordered_smul : ordered_smul R R :=
{ smul_lt_smul_of_pos       := ordered_semiring.mul_lt_mul_of_pos_left,
  lt_of_smul_lt_smul_of_pos := λ a b c w₁ w₂, (mul_lt_mul_left w₂).mp w₁ }

end instances
