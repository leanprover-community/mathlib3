/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import analysis.locally_convex.balanced_core_hull
import analysis.locally_convex.with_seminorms
import analysis.convex.gauge

/-!
# Absolutely convex sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A set is called absolutely convex or disked if it is convex and balanced.
The importance of absolutely convex sets comes from the fact that every locally convex
topological vector space has a basis consisting of absolutely convex sets.

## Main definitions

* `gauge_seminorm_family`: the seminorm family induced by all open absolutely convex neighborhoods
of zero.

## Main statements

* `with_gauge_seminorm_family`: the topology of a locally convex space is induced by the family
`gauge_seminorm_family`.

## Todo

* Define the disked hull

## Tags

disks, convex, balanced
-/


open normed_field set
open_locale big_operators nnreal pointwise topology

variables {𝕜 E F G ι : Type*}

section nontrivially_normed_field

variables (𝕜 E) {s : set E}

variables [nontrivially_normed_field 𝕜] [add_comm_group E] [module 𝕜 E]
variables [module ℝ E] [smul_comm_class ℝ 𝕜 E]
variables [topological_space E] [locally_convex_space ℝ E] [has_continuous_smul 𝕜 E]

lemma nhds_basis_abs_convex : (𝓝 (0 : E)).has_basis
  (λ (s : set E), s ∈ 𝓝 (0 : E) ∧ balanced 𝕜 s ∧ convex ℝ s) id :=
begin
  refine (locally_convex_space.convex_basis_zero ℝ E).to_has_basis (λ s hs, _)
    (λ s hs, ⟨s, ⟨hs.1, hs.2.2⟩, rfl.subset⟩),
  refine ⟨convex_hull ℝ (balanced_core 𝕜 s), _, convex_hull_min (balanced_core_subset s) hs.2⟩,
  refine ⟨filter.mem_of_superset (balanced_core_mem_nhds_zero hs.1) (subset_convex_hull ℝ _), _⟩,
  refine ⟨balanced_convex_hull_of_balanced (balanced_core_balanced s), _⟩,
  exact convex_convex_hull ℝ (balanced_core 𝕜 s),
end

variables [has_continuous_smul ℝ E] [topological_add_group E]

lemma nhds_basis_abs_convex_open : (𝓝 (0 : E)).has_basis
  (λ (s : set E), (0 : E) ∈ s ∧ is_open s ∧ balanced 𝕜 s ∧ convex ℝ s) id :=
begin
  refine (nhds_basis_abs_convex 𝕜 E).to_has_basis _ _,
  { rintros s ⟨hs_nhds, hs_balanced, hs_convex⟩,
    refine ⟨interior s, _, interior_subset⟩,
    exact ⟨mem_interior_iff_mem_nhds.mpr hs_nhds, is_open_interior,
      hs_balanced.interior (mem_interior_iff_mem_nhds.mpr hs_nhds), hs_convex.interior⟩ },
  rintros s ⟨hs_zero, hs_open, hs_balanced, hs_convex⟩,
  exact ⟨s, ⟨hs_open.mem_nhds hs_zero, hs_balanced, hs_convex⟩, rfl.subset⟩,
end

end nontrivially_normed_field

section absolutely_convex_sets

variables [topological_space E] [add_comm_monoid E] [has_zero E] [semi_normed_ring 𝕜]
variables [has_smul 𝕜 E] [has_smul ℝ E]

variables (𝕜 E)

/-- The type of absolutely convex open sets. -/
def abs_convex_open_sets :=
{ s : set E // (0 : E) ∈ s ∧ is_open s ∧ balanced 𝕜 s ∧ convex ℝ s }

instance abs_convex_open_sets.has_coe : has_coe (abs_convex_open_sets 𝕜 E) (set E) := ⟨subtype.val⟩

namespace abs_convex_open_sets

variables {𝕜 E}

lemma coe_zero_mem (s : abs_convex_open_sets 𝕜 E) : (0 : E) ∈ (s : set E) := s.2.1

lemma coe_is_open (s : abs_convex_open_sets 𝕜 E) : is_open (s : set E) := s.2.2.1

lemma coe_nhds (s : abs_convex_open_sets 𝕜 E) : (s : set E) ∈ 𝓝 (0 : E) :=
s.coe_is_open.mem_nhds s.coe_zero_mem

lemma coe_balanced (s : abs_convex_open_sets 𝕜 E) : balanced 𝕜 (s : set E) := s.2.2.2.1

lemma coe_convex (s : abs_convex_open_sets 𝕜 E) : convex ℝ (s : set E) := s.2.2.2.2

end abs_convex_open_sets

instance : nonempty (abs_convex_open_sets 𝕜 E) :=
begin
  rw ←exists_true_iff_nonempty,
  dunfold abs_convex_open_sets,
  rw subtype.exists,
  exact ⟨set.univ, ⟨mem_univ 0, is_open_univ, balanced_univ, convex_univ⟩, trivial⟩,
end

end absolutely_convex_sets

variables [is_R_or_C 𝕜]
variables [add_comm_group E] [topological_space E]
variables [module 𝕜 E] [module ℝ E] [is_scalar_tower ℝ 𝕜 E]
variables [has_continuous_smul ℝ E]

variables (𝕜 E)

/-- The family of seminorms defined by the gauges of absolute convex open sets. -/
noncomputable
def gauge_seminorm_family : seminorm_family 𝕜 E (abs_convex_open_sets 𝕜 E) :=
λ s, gauge_seminorm s.coe_balanced s.coe_convex (absorbent_nhds_zero s.coe_nhds)

variables {𝕜 E}

lemma gauge_seminorm_family_ball (s : abs_convex_open_sets 𝕜 E) :
  (gauge_seminorm_family 𝕜 E s).ball 0 1 = (s : set E) :=
begin
  dunfold gauge_seminorm_family,
  rw seminorm.ball_zero_eq,
  simp_rw gauge_seminorm_to_fun,
  exact gauge_lt_one_eq_self_of_open s.coe_convex s.coe_zero_mem s.coe_is_open,
end

variables [topological_add_group E] [has_continuous_smul 𝕜 E]
variables [smul_comm_class ℝ 𝕜 E] [locally_convex_space ℝ E]

/-- The topology of a locally convex space is induced by the gauge seminorm family. -/
lemma with_gauge_seminorm_family : with_seminorms (gauge_seminorm_family 𝕜 E) :=
begin
  refine seminorm_family.with_seminorms_of_has_basis _ _,
  refine (nhds_basis_abs_convex_open 𝕜 E).to_has_basis (λ s hs, _) (λ s hs, _),
  { refine ⟨s, ⟨_, rfl.subset⟩⟩,
    convert (gauge_seminorm_family _ _).basis_sets_singleton_mem ⟨s, hs⟩ one_pos,
    rw [gauge_seminorm_family_ball, subtype.coe_mk] },
  refine ⟨s, ⟨_, rfl.subset⟩⟩,
  rw seminorm_family.basis_sets_iff at hs,
  rcases hs with ⟨t, r, hr, rfl⟩,
  rw [seminorm.ball_finset_sup_eq_Inter _ _ _ hr],
  -- We have to show that the intersection contains zero, is open, balanced, and convex
  refine ⟨mem_Inter₂.mpr (λ _ _, by simp [seminorm.mem_ball_zero, hr]),
    is_open_bInter (to_finite _) (λ S _, _),
    balanced_Inter₂ (λ _ _, seminorm.balanced_ball_zero _ _),
    convex_Inter₂ (λ _ _, seminorm.convex_ball _ _ _)⟩,
  -- The only nontrivial part is to show that the ball is open
  have hr' : r = ‖(r : 𝕜)‖ * 1 := by simp [abs_of_pos hr],
  have hr'' : (r : 𝕜) ≠ 0 := by simp [hr.ne'],
  rw [hr', ← seminorm.smul_ball_zero hr'', gauge_seminorm_family_ball],
  exact S.coe_is_open.smul₀ hr''
end
