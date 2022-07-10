/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import data.nat.lattice

/-!
-/

@[derive [has_zero, add_comm_monoid_with_one, canonically_ordered_comm_semiring, nontrivial,
  canonically_linear_ordered_add_monoid, has_sub, has_ordered_sub, complete_linear_order,
  linear_ordered_add_comm_monoid_with_top]]
def enat : Type := with_top ℕ

notation `ℕ∞` := with_top ℕ

namespace enat

instance : can_lift ℕ∞ ℕ := with_top.can_lift

def to_nat : monoid_with_zero_hom ℕ∞ ℕ :=
{ to_fun := with_top.untop' 0,
  map_one' := rfl,
  map_zero' := rfl,
  map_mul' := with_top.untop'_zero_mul }



end enat
