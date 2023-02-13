/-
Copyright (c) 2018 Louis Carlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Carlin, Mario Carneiro
-/
import algebra.euclidean_domain.defs
import algebra.field.defs
import algebra.group_with_zero.units.lemmas
import data.nat.order.basic
import data.int.order.basic

/-!
# Instances for Euclidean domains

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

* `int.euclidean_domain`: shows that `ℤ` is a Euclidean domain.
* `field.to_euclidean_domain`: shows that any field is a Euclidean domain.

-/

instance int.euclidean_domain : euclidean_domain ℤ :=
{ add := (+),
  mul := (*),
  one := 1,
  zero := 0,
  neg := has_neg.neg,
  quotient := (/),
  quotient_zero := int.div_zero,
  remainder := (%),
  quotient_mul_add_remainder_eq := λ a b, int.div_add_mod _ _,
  r := λ a b, a.nat_abs < b.nat_abs,
  r_well_founded := measure_wf (λ a, int.nat_abs a),
  remainder_lt := λ a b b0, int.coe_nat_lt.1 $
    by { rw [int.nat_abs_of_nonneg (int.mod_nonneg _ b0), int.coe_nat_abs],
      exact int.mod_lt _ b0 },
  mul_left_not_lt := λ a b b0, not_lt_of_ge $
    by {rw [← mul_one a.nat_abs, int.nat_abs_mul],
      exact mul_le_mul_of_nonneg_left (int.nat_abs_pos_of_ne_zero b0) (nat.zero_le _) },
  .. int.comm_ring,
  .. int.nontrivial }

@[priority 100] -- see Note [lower instance priority]
instance field.to_euclidean_domain {K : Type*} [field K] : euclidean_domain K :=
{ add := (+),
  mul := (*),
  one := 1,
  zero := 0,
  neg := has_neg.neg,
  quotient := (/),
  remainder := λ a b, a - a * b / b,
  quotient_zero := div_zero,
  quotient_mul_add_remainder_eq := λ a b,
    by { classical, by_cases b = 0; simp [h, mul_div_cancel'] },
  r := λ a b, a = 0 ∧ b ≠ 0,
  r_well_founded := well_founded.intro $ λ a, acc.intro _ $ λ b ⟨hb, hna⟩,
    acc.intro _ $ λ c ⟨hc, hnb⟩, false.elim $ hnb hb,
  remainder_lt := λ a b hnb, by simp [hnb],
  mul_left_not_lt := λ a b hnb ⟨hab, hna⟩, or.cases_on (mul_eq_zero.1 hab) hna hnb,
  .. ‹field K› }
