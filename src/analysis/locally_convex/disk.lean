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
variables [has_continuous_smul ℝ E] [topological_add_group E]

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

lemma nhds_basis_abs_convex_open : (𝓝 (0 : E)).has_basis
  (λ (s : set E), (0 : E) ∈ s ∧ is_open s ∧ balanced 𝕜 s ∧ convex ℝ s) id :=
begin
  refine (nhds_basis_abs_convex 𝕜 E).to_has_basis _ _,
  {
    rintros s ⟨hs_nhds, hs_balanced, hs_convex⟩,
    use interior s,
    refine ⟨_, interior_subset⟩,
    refine ⟨mem_interior_iff_mem_nhds.mpr hs_nhds, is_open_interior, _, hs_convex.interior⟩,
    {
      sorry,
    },
  },
  rintros s ⟨hs_zero, hs_open, hs_balanced, hs_convex⟩,
  exact ⟨s, ⟨hs_open.mem_nhds hs_zero, hs_balanced, hs_convex⟩, rfl.subset⟩,
end

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

end nontrivially_normed_field

variables [is_R_or_C 𝕜]
variables [add_comm_group E] [topological_space E] [topological_add_group E]
variables [module 𝕜 E] [module ℝ E] [is_scalar_tower ℝ 𝕜 E] [has_continuous_smul 𝕜 E]
variables [smul_comm_class ℝ 𝕜 E] [locally_convex_space ℝ E] [has_continuous_smul ℝ E]

namespace abs_convex_open_sets

lemma Ioi_smul_nonempty (s : abs_convex_open_sets 𝕜 E) (x : E) :
  {r ∈ Ioi (0 : ℝ) | x ∈ r • (s : set E)}.nonempty :=
begin
  have : absorbent 𝕜 (s : set E) := absorbent_nhds_zero s.coe_nhds,
  rcases this x with ⟨r, hr, h⟩,
  have hr' : r ≤ ∥(r : 𝕜)∥ :=
  begin
    rw is_R_or_C.norm_of_real,
    rw [real.norm_eq_abs],
    exact le_abs_self _,
  end,
  use r,
  simp only [mem_sep_eq, mem_Ioi],
  refine ⟨hr, _⟩,
  convert h r hr',
  rw is_R_or_C.of_real_alg,
  simp only [smul_one_smul],
end

end abs_convex_open_sets

variables (𝕜 E)

noncomputable
def maximal_seminorm_family : seminorm_family 𝕜 E (abs_convex_open_sets 𝕜 E) :=
λ s, gauge_seminorm s.coe_balanced s.coe_convex (absorbent_nhds_zero s.coe_nhds)

variables {𝕜 E}

lemma maximal_seminorm_family_ball (s : abs_convex_open_sets 𝕜 E) :
  (maximal_seminorm_family 𝕜 E s).ball 0 1 = (s : set E) :=
begin
  dunfold maximal_seminorm_family,
  rw seminorm.ball_zero_eq,
  simp_rw gauge_seminorm_to_fun,
  exact gauge_lt_one_eq_self_of_open s.coe_convex s.coe_zero_mem s.coe_is_open,
end

@[simp] lemma coe_norm {𝕜 : Type*} (r : ℝ) [is_R_or_C 𝕜] : ∥(r : 𝕜)∥ = ∥r∥ :=
by rw [is_R_or_C.of_real_alg, norm_smul, cstar_ring.norm_one, mul_one]


lemma with_maximal_seminorm_family : with_seminorms (maximal_seminorm_family 𝕜 E) :=
begin
  refine seminorm_family.with_seminorms_of_has_basis _ _,
  refine filter.has_basis.to_has_basis (nhds_basis_abs_convex_open 𝕜 E) (λ s hs, _) (λ s hs, _),
  { refine ⟨s, ⟨_, rfl.subset⟩⟩,
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
  -- We have to show that the intersection contains zero, is open, balanced, and convex
  refine ⟨mem_Inter₂.mpr (λ _ _, by simp [seminorm.mem_ball_zero, hr]),
    is_open_bInter (to_finite _) (λ _ _, _),
    balanced_Inter₂ (λ _ _, seminorm.balanced_ball_zero _ _),
    convex_Inter₂ (λ _ _, seminorm.convex_ball _ _ _)⟩,
  -- The only nontrivial part is to show that the ball is open
  have hr' : r = ∥(r : 𝕜)∥ * 1 := by simp [abs_of_pos hr],
  have hr'' : (r : 𝕜) ≠ 0 := by simp [ne_of_gt hr],
  rw hr',
  rw ←seminorm.smul_ball_zero (norm_pos_iff.mpr hr''),
  refine is_open.smul₀ _ hr'',
  rw maximal_seminorm_family_ball,
  exact abs_convex_open_sets.coe_is_open _,
end
