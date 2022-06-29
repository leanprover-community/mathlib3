/-
Copyright (c) 2021 Alex Kontorovich, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/
import topology.algebra.const_mul_action
import topology.instances.real

/-!
# The topology on the quotient group `ℝ / a ℤ`
-/

open add_subgroup

variables {a : ℝ} [fact (0 < a)]

instance : has_continuous_const_vadd (zmultiples a).opposite ℝ :=
sorry
-- follows by `to_additive` of `smul_comm_class.has_continuous_const_smul`

instance : properly_discontinuous_vadd (zmultiples a).opposite ℝ :=
{ finite_disjoint_inter_image := begin
    sorry
  end }

instance : t2_space (ℝ ⧸ zmultiples a) := t2_space_of_properly_discontinuous_vadd_of_t2_space

-- check, remove later
example : topological_add_group (ℝ ⧸ zmultiples a) := by apply_instance

lemma foo {X : Type*} [topological_space X] {s : set X} (hs : is_compact s) {Y : Type*}
  [topological_space Y] {f : X → Y} (hf : continuous f) (hf' : set.surj_on f s set.univ) :
  compact_space Y :=
sorry

local notation `π` := (quotient.mk' : ℝ → ℝ ⧸ zmultiples a)

lemma baz₁ : set.surj_on π (set.Ico 0 a) set.univ :=
begin
  sorry -- archimedean
end

lemma baz₂ : set.surj_on π (set.Ioc 0 a) set.univ :=
begin
  sorry
end

instance : compact_space (ℝ ⧸ zmultiples a) :=
foo is_compact_Icc continuous_quotient_mk $ baz₁.mono set.Ico_subset_Icc_self (set.subset.refl _)

instance : normal_space (ℝ ⧸ zmultiples a) := normal_of_compact_t2
