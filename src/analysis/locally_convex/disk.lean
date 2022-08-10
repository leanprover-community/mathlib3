/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import analysis.locally_convex.balanced_core_hull
import analysis.locally_convex.with_seminorms
import analysis.seminorm
import analysis.convex.combination
import analysis.convex.gauge
import analysis.complex.basic
import analysis.normed_space.is_R_or_C
import topology.algebra.module.locally_convex


/-!
# Disk

## Main definitions

* `foo_bar`

## Main statements

* `foo_bar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/


open normed_field set
open_locale big_operators nnreal pointwise topological_space

variables {𝕜 E F G ι : Type*}

section test

variables [is_R_or_C 𝕜]
variables [add_comm_group E] [module 𝕜 E]
variables (x : ℝ) (z : 𝕜) (v : E)

end test

section nontrivially_normed_field
variables [nontrivially_normed_field 𝕜] [add_comm_group E] [normed_space ℝ 𝕜] [module 𝕜 E]
variables [module ℝ E] [is_scalar_tower ℝ 𝕜 E]

variables {s : set E} (p : seminorm 𝕜 E)

lemma disked_iff_pointwise_add_subset : (balanced 𝕜 s ∧ convex ℝ s)
  ↔ ∀ (a b : 𝕜) (ha : ∥a∥ + ∥b∥ ≤ 1), a • s + b • s ⊆ s :=
begin
  split,
  {
    intros h a b h',
    by_cases he : s.nonempty,
    { cases h with h1 h2,
      by_cases h'' : ∥a∥ + ∥b∥ = 0,
      { simp_rw [add_eq_zero_iff' (norm_nonneg a) (norm_nonneg b), norm_eq_zero] at h'',
        rw [h''.1, h''.2],
        rw set.zero_smul_set he,
        rw [add_zero, zero_subset],
        exact balanced.zero_mem_nonempty h1 he },
      set a' := ∥a∥/(∥a∥ + ∥b∥),
      set b' := ∥b∥/(∥a∥ + ∥b∥),
      have ha' : 0 ≤ a' :=
      div_nonneg (norm_nonneg a) (add_nonneg (norm_nonneg a) (norm_nonneg b)),
      have hb' : 0 ≤ b' :=
      div_nonneg (norm_nonneg b) (add_nonneg (norm_nonneg a) (norm_nonneg b)),
      have hab' : a' + b' = 1 :=
      begin
        rw [←add_div, div_self],
        exact h'',
      end,
      intros z hz,
      rw mem_add at hz,
      rcases hz with ⟨x,y,hx,hy,hz⟩,
      rw mem_smul_set at hx,
      rcases hx with ⟨x',hx',hx⟩,
      rw mem_smul_set at hy,
      rcases hy with ⟨y',hy',hy⟩,
      rw [←hz, ←hx, ←hy],
      rw convex_iff_pointwise_add_subset at h2,
      specialize h2 ha' hb' hab',
      specialize h1 ((∥a∥ + ∥b∥) • 1),
      --refine subset.trans _ (h1 _ h'),
      --refine set.add_subset_add _ _,
      {

        sorry,
      },
      sorry },
    { rw set.not_nonempty_iff_eq_empty at he,
      simp_rw [he, smul_set_empty, add_empty] },
  },
  intros h,
  split,
  { by_cases h' : s.nonempty,
    { intros a ha,
      specialize h 0 a,
      simp only [norm_zero, zero_add] at h,
      specialize h ha,
      rw [set.zero_smul_set h', zero_add] at h,
      exact h },
    { rw set.not_nonempty_iff_eq_empty at h',
      rw h',
      exact balanced.emptyset },
  },
  rw convex_iff_pointwise_add_subset,
  intros a b ha hb h',
  specialize h (a • 1) (b • 1),
  have h' : ∥a • (1:𝕜)∥ + ∥b • (1:𝕜)∥ ≤ 1 :=
  by simp_rw [norm_smul, norm_one, mul_one, real.norm_of_nonneg ha, real.norm_of_nonneg hb, h'],
  specialize h h',
  simp at h,
  exact h,
end

variables [smul_comm_class ℝ 𝕜 E]

lemma balanced_convex_hull_of_balanced (hs : balanced 𝕜 s) : balanced 𝕜 (convex_hull ℝ s) :=
begin
  rw balanced_iff_smul_mem,
  intros a ha x hx,
  rw convex_hull_eq at hx ⊢,
  simp only [exists_prop, exists_and_distrib_left, mem_set_of_eq] at hx ⊢,
  rcases hx with ⟨ι, t, f, f', h, hsum, hpos, hx⟩,
  use [ι, t, f, a • f'],
  refine ⟨λ i hi, hs.smul_mem ha (h _ hi), hsum, hpos, _⟩,
  rw ←hx,
  simp_rw [finset.center_mass, finset.smul_sum],
  refine finset.sum_congr rfl (λ y hy, _),
  simp_rw [pi.smul_apply, ←mul_smul, smul_comm],
end

--variables (𝕜 E)
variables (𝕜 E)

variables [topological_space E] [locally_convex_space ℝ E] [has_continuous_smul 𝕜 E]
variables [has_continuous_smul ℝ E]

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

def abs_convex_nhds_sets :=
{ s // s ∈ 𝓝 (0 : E) ∧ balanced 𝕜 s ∧ convex ℝ s }

instance : has_coe (abs_convex_nhds_sets 𝕜 E) (set E) := ⟨subtype.val⟩

namespace abs_convex_nhds_sets

lemma coe_nhds (s : abs_convex_nhds_sets 𝕜 E) : ↑s ∈ 𝓝 (0 : E) := s.2.1
lemma coe_balanced (s : abs_convex_nhds_sets 𝕜 E) : balanced 𝕜 (s : set E) := s.2.2.1
lemma coe_convex (s : abs_convex_nhds_sets 𝕜 E) : convex ℝ (s : set E) := s.2.2.2

end abs_convex_nhds_sets

instance : nonempty (abs_convex_nhds_sets 𝕜 E) :=
begin
  rw ←exists_true_iff_nonempty,
  dunfold abs_convex_nhds_sets,
  rw subtype.exists,
  exact ⟨set.univ, ⟨filter.univ_mem, balanced_univ, convex_univ⟩, trivial⟩,
end

end nontrivially_normed_field

variables [is_R_or_C 𝕜]
variables [add_comm_group E] [topological_space E] [topological_add_group E]
variables [module 𝕜 E] [module ℝ E] [is_scalar_tower ℝ 𝕜 E] [has_continuous_smul 𝕜 E]
variables [smul_comm_class ℝ 𝕜 E] [locally_convex_space ℝ E] [has_continuous_smul ℝ E]

variables (𝕜 E)

noncomputable
def maximal_seminorm_family : seminorm_family 𝕜 E (abs_convex_nhds_sets 𝕜 E) :=
λ s, gauge_seminorm s.2.2.1 s.2.2.2 (absorbent_nhds_zero s.2.1)

variables {𝕜 E}

lemma maximal_seminorm_family_to_fun (s : abs_convex_nhds_sets 𝕜 E) (x : E) :
  maximal_seminorm_family 𝕜 E s x = gauge s.1 x :=
begin
  dunfold maximal_seminorm_family,
  rw gauge_seminorm_to_fun,
end

lemma maximal_seminorm_family_ball (s : abs_convex_nhds_sets 𝕜 E) :
  (maximal_seminorm_family 𝕜 E s).ball 0 1 = interior (s : set E) :=
begin
  dunfold maximal_seminorm_family,
  rw seminorm.ball_zero_eq,
  simp_rw gauge_seminorm_to_fun,
  ext,
  simp,
  simp_rw gauge_def,
  sorry,
end

lemma with_maximal_seminorm_family : with_seminorms (maximal_seminorm_family 𝕜 E) :=
begin
  refine seminorm_family.with_seminorms_of_has_basis _ _,
  refine filter.has_basis.to_has_basis (nhds_basis_abs_convex 𝕜 E) (λ s hs, _) (λ s hs, _),
  { refine ⟨interior s, ⟨_, interior_subset⟩⟩,
    rw seminorm_family.basis_sets_iff,
    refine ⟨{⟨s, hs⟩}, 1, one_pos, _⟩,
    simp only [finset.sup_singleton],
    rw maximal_seminorm_family_ball,
    simp only [subtype.coe_mk] },
  refine ⟨s, ⟨_, rfl.subset⟩⟩,
  rw seminorm_family.basis_sets_iff at hs,
  rcases hs with ⟨t, r, hr, hs⟩,
  rw seminorm.ball_finset_sup_eq_Inter _ _ _ hr at hs,
  rw hs,
  -- We have to show that the intersection is a zero neighborhood, balanced, and convex
  refine ⟨_, balanced_Inter₂ (λ _ _, seminorm.balanced_ball_zero _ _),
    convex_Inter₂ (λ _ _, seminorm.convex_ball _ _ _)⟩,
  -- Only the zero neighbor is nontrivial
  rw [filter.bInter_finset_mem],
  intros i hi,
  rw ←mul_one r,
  rw ←real.norm_of_nonneg (le_of_lt hr),
  have h' : ∥r∥ = ∥(r : 𝕜)∥ := by sorry,
  have hr' : 0 < ∥(r : 𝕜)∥ := by sorry,
    --have hr' : 0 < ∥r∥ := by {rw real.norm_of_nonneg (le_of_lt hr), exact hr},
  rw h',
  rw ←@seminorm.smul_ball_zero 𝕜 E _ _ _ (maximal_seminorm_family 𝕜 E i) _ 1 hr',
    --rw ←smul_zero (r : 𝕜),
    sorry,
    /-refine set_smul_mem_nhds_smul _ (ne_of_gt hr),
    simp only [smul_zero],
    rw maximal_seminorm_family_ball,
    simp only [subtype.val_eq_coe, interior_mem_nhds],
    exact abs_convex_nhds_sets.coe_nhds 𝕜 E i -/ -- },
  --refine balanced_Inter₂ (λ _ _, seminorm.balanced_ball_zero _ _),
end


-- Need to show that
-- scaling is preserved
