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

/-- A discrete subgroup of a topological group `G` acts on `G` properly discontinuously on the left.
-/
def zz {G : Type*} [add_group G] [topological_space G] [topological_add_group G]
  {H : add_subgroup G} (hH : filter.tendsto H.subtype filter.cofinite (filter.cocompact G)) :
  properly_discontinuous_vadd H G :=
{ finite_disjoint_inter_image := begin
    intros K L hK hL,
    have H : set.finite _ := hH ((hL.prod hK).image continuous_sub).compl_mem_cocompact,
    convert H,
    ext x,
    rcases x with ⟨(x:G), hx⟩,
    change (_ ≠ ∅) ↔ _,
    simp only [set.image_vadd, set.image_prod, set.image2_sub, compl_compl, set.mem_preimage,
      coe_mk, set.ne_empty_iff_nonempty, set.preimage_compl],
    congrm (∃ ℓ, _),
    simp only [set.mem_inter_eq, coe_mk, exists_and_distrib_left],
    rw and_comm,
    congrm _ ∧ (∃ k, _ ∧ _),
    change (x + k = ℓ) ↔ ℓ - k = x,
    rw sub_eq_iff_eq_add,
    exact comm,
  end }

/-- A discrete subgroup of an abelian topological group `G` acts on `G` properly discontinuously on
the right. -/
def zz' {G : Type*} [add_comm_group G] [topological_space G] [topological_add_group G]
  {H : add_subgroup G} (hH : filter.tendsto H.subtype filter.cofinite (filter.cocompact G)) :
  properly_discontinuous_vadd H.opposite G :=
{ finite_disjoint_inter_image := begin
    intros K L hK hL,
    have H : set.finite _ := hH ((hL.prod hK).image continuous_sub).compl_mem_cocompact,
    convert H,
    ext x,
    rcases x with ⟨(x:G), hx⟩,
    change (_ ≠ ∅) ↔ _,
    simp only [set.image_vadd, set.image_prod, set.image2_sub, compl_compl, set.mem_preimage,
      coe_mk, set.ne_empty_iff_nonempty, set.preimage_compl],
    congrm (∃ ℓ, _),
    simp only [set.mem_inter_eq, coe_mk, exists_and_distrib_left],
    rw and_comm,
    congrm _ ∧ (∃ k, _ ∧ _),
    change (k + x = ℓ) ↔ ℓ - k = x,
    rw sub_eq_iff_eq_add,
    rw add_comm,
    exact comm,
  end }

variables {a : ℝ}

instance : has_continuous_const_vadd (zmultiples a).opposite ℝ :=
sorry
-- follows by `to_additive` of `smul_comm_class.has_continuous_const_smul`

/-- The action on `ℝ` by right multiplication of its the subgroup `zmultiples a` (the multiples of
`a:ℝ`) is properly discontinuous. -/
instance : properly_discontinuous_vadd (zmultiples a).opposite ℝ :=
zz' (add_subgroup.tendsto_zmultiples_subtype_cofinite a)

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
