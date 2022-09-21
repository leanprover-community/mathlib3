/-
Copyright (c) 2021 Alex Kontorovich, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/
import topology.algebra.const_mul_action
import topology.instances.real
import tactic.linear_combination

/-!
# The topology on the quotient group `ℝ / a ℤ`

-/

open add_subgroup

variables {a : ℝ}

/-- The action on `ℝ` by right multiplication of its the subgroup `zmultiples a` (the multiples of
`a:ℝ`) is properly discontinuous. -/
instance : properly_discontinuous_vadd (zmultiples a).opposite ℝ :=
(zmultiples a).properly_discontinuous_vadd_opposite_of_tendsto_cofinite
  (add_subgroup.tendsto_zmultiples_subtype_cofinite a)

/-- The quotient of `ℝ` by the subgroup `zmultiples a` (the multiples of `a:ℝ`) is Hausdorff. -/
instance : t2_space (ℝ ⧸ zmultiples a) := t2_space_of_properly_discontinuous_vadd_of_t2_space

variables [fact (0 < a)]

local notation `π` := quotient_add_group.mk' (zmultiples a)

/-- Under the map from `ℝ` to its quotient by `zmultiples a` (the multiples of `a:ℝ`), the image of
the interval [0, a) is the whole quotient. -/
lemma real.surj_on_quotient_Ico : set.surj_on π (set.Ico 0 a) set.univ :=
begin
  rintros x₀ -,
  apply @quotient.induction_on ℝ (quotient_add_group.left_rel (zmultiples a))
    (λ x, x ∈ quotient.mk' '' set.Ico 0 a),
  intros x,
  obtain ⟨k, hk, -⟩ := exists_unique_add_zsmul_mem_Ico (fact.out _ : 0 < a) x 0,
  refine ⟨x + k • a, _, _⟩,
  { simpa using hk },
  refine quotient_add_group.eq'.mpr _,
  use - k,
  simp,
  push_cast,
  ring,
end

/-- The quotient of `ℝ` by the subgroup `zmultiples a` (the multiples of `a:ℝ`) is compact. -/
instance : compact_space (ℝ ⧸ zmultiples a) :=
(real.surj_on_quotient_Ico.mono set.Ico_subset_Icc_self (set.subset.refl _)).compact_space
  is_compact_Icc
  continuous_quotient_mk

/-- The quotient of `ℝ` by the subgroup `zmultiples a` (the multiples of `a:ℝ`) is normal. -/
instance : normal_space (ℝ ⧸ zmultiples a) := normal_of_compact_t2
