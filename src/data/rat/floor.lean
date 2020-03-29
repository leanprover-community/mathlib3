/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Kappelmann
-/
import data.rat.order
import data.rat.cast
import algebra.floor
/-!
# Floor Function for Rational Numbers

## Summary

We define the `floor` function and the `floor_ring` instance on `ℚ`.

## Tags

rat, rationals, ℚ, floor
-/

namespace rat

/-- `floor q` is the largest integer `z` such that `z ≤ q` -/
protected def floor : ℚ → ℤ
| ⟨n, d, h, c⟩ := n / d

protected theorem le_floor {z : ℤ} : ∀ {r : ℚ}, z ≤ rat.floor r ↔ (z : ℚ) ≤ r
| ⟨n, d, h, c⟩ := begin
  simp [rat.floor],
  rw [num_denom'],
  have h' := int.coe_nat_lt.2 h,
  conv { to_rhs,
    rw [coe_int_eq_mk, rat.le_def zero_lt_one h', mul_one] },
  exact int.le_div_iff_mul_le h'
end

instance : floor_ring ℚ :=
{ floor := rat.floor, le_floor := @rat.le_floor }

protected lemma floor_def {q : ℚ} : ⌊q⌋ = q.num / q.denom := by { cases q, refl }

end rat
