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

#check (x • (1 : 𝕜)) • v

end test

section module
variables [nondiscrete_normed_field 𝕜] [add_comm_group E] [normed_space ℝ 𝕜] [module 𝕜 E]
--variables [module ℝ E] [is_scalar_tower ℝ 𝕜 E]

variables {s : set E} (p : seminorm 𝕜 E)

lemma balanced.emptyset : balanced 𝕜 (∅ : set E) :=
λ _ _, by { rw smul_set_empty }

lemma balanced.zero_mem_nonempty (h : balanced 𝕜 s) (hs : s.nonempty) : (0 : E) ∈ s :=
begin
  sorry,
end

lemma balanced_iff : balanced 𝕜 s ↔ ∀ (x ∈ s) (a : 𝕜) (ha : ∥a∥ ≤ 1), a • x ∈ s :=
begin
  refine ⟨λ h x hx a ha, set.mem_of_subset_of_mem (h a ha) (set.smul_mem_smul_set hx), _⟩,
  rintros h a ha x ⟨y, hy, hx⟩,
  rw ←hx,
  exact h y hy a ha,
end

lemma balanced_mem_iff (h : balanced 𝕜 s) {x : E} {a : 𝕜} (ha : ∥a∥ = 1) : x ∈ s ↔ a • x ∈ s :=
begin
  refine ⟨λ h', (balanced_iff.mp h) x h' _ (le_of_eq ha), λ h', _⟩,
  have ha' : a ≠ 0 :=
  by { rw [←norm_ne_zero_iff, ha], exact one_ne_zero },
  rw [←one_smul 𝕜 x, ←inv_mul_cancel ha', mul_smul],
  refine balanced_iff.mp h (a • x) h' _ _,
  simp[ha],
end

lemma balanced.symmetric (h : balanced 𝕜 s) (x : E) (hx : x ∈ s) : -x ∈ s :=
by { convert (balanced_iff.mp h) x hx (-1) (by simp), simp }

lemma balanced.Inter_finset {t : finset ι} {f : ι → set E}
  (h : ∀ i ∈ t, balanced 𝕜 (f i)) : balanced 𝕜 (⋂ (i ∈ t), f i) :=
begin
  classical,
  induction t using finset.induction_on with i t ht hi,
  { simp only [Inter_false, Inter_univ], exact balanced_univ, },
  rw [finset.set_bInter_insert],
  refine balanced.inter (h i (by simp)) (hi (λ i' hi', h i' _)),
  rw [finset.mem_insert],
  exact or.intro_right _ hi',
end

variables [module ℂ E]

lemma gauge_balanced (hs : balanced ℂ s) (r : ℂ) (x : E) : gauge s (r • x) =
  gauge s (∥r∥ • x) :=
begin
  have h'' : ∥r∥ • x = (∥r∥ : ℂ) • x := complex.coe_smul _ _,
  rw h'',
  simp_rw [gauge_def'],
  by_cases h : r = 0,
  { rw h, simp only [complex.norm_eq_abs, complex.abs_zero, complex.of_real_zero]},
  apply congr_arg _,
  ext r',
  simp only [mem_sep_eq, mem_Ioi, and.congr_right_iff],
  intros hr',
  simp_rw [←smul_assoc, ←complex.coe_smul, smul_eq_mul],
  rw balanced_iff at hs,
  split,
  { intros h',
    specialize hs _ h' (∥r∥/r) _,
    { simp only [complex.norm_eq_abs, complex.abs_div, complex.abs_of_real, complex.abs_abs],
      exact div_self_le_one (complex.abs r) },
    rw ←smul_assoc at hs,
    rw smul_eq_mul at hs,
    have hr : (↑∥r∥ / r * (↑r'⁻¹ * r)) = ↑r'⁻¹ * ↑∥r∥ :=
    begin
      ring_nf,
      simp only [complex.of_real_inv, complex.norm_eq_abs, mul_eq_mul_right_iff,
        complex.of_real_eq_zero, complex.abs_eq_zero],
      left,
      rw [mul_comm, ←mul_assoc],
      simp only [h, inv_mul_cancel, ne.def, not_false_iff, one_mul],
    end,
    rw hr at hs,
    exact hs,
  },
  intros h',
  specialize hs _ h' (r/∥r∥) _,
  { simp only [complex.norm_eq_abs, complex.abs_div, complex.abs_of_real, complex.abs_abs],
    exact div_self_le_one (complex.abs r) },
  rw ←smul_assoc at hs,
  rw smul_eq_mul at hs,
  have hr : r / ↑∥r∥ * (↑r'⁻¹ * ↑∥r∥) = ↑r'⁻¹ * r :=
  begin
    ring_nf,
    simp only [complex.norm_eq_abs, complex.of_real_inv, mul_eq_mul_right_iff],
    left,
    rw [mul_comm, ←mul_assoc],
    simp[h],
  end,
  rw hr at hs,
  exact hs,
end


/-- In textbooks, this is the homogeneity of the Minkowksi functional. -/
lemma gauge_smul' {s : set E} (hs : balanced ℂ s) (r : ℂ) (x : E) :
  gauge s (r • x) = ∥r∥ • gauge s x :=
begin
  rw ←gauge_smul_of_nonneg (norm_nonneg r),
  exact gauge_balanced hs _ _,
  apply_instance,
end

/--/
lemma absorbs_Union_finset {s : set E} {t : finset ι} {f : ι → set E} :
  absorbs 𝕜 s (⋃ (i ∈ t), f i) ↔ ∀ i ∈ t, absorbs 𝕜 s (f i) :=
begin
  classical,
  induction t using finset.induction_on with i t ht hi,
  { simp only [finset.not_mem_empty, set.Union_false, set.Union_empty, absorbs_empty,
    forall_false_left, implies_true_iff] },
  rw [finset.set_bUnion_insert, absorbs_union, hi],
  split; intro h,
  { refine λ _ hi', (finset.mem_insert.mp hi').elim _ (h.2 _),
    exact (λ hi'', by { rw hi'', exact h.1 }) },
  exact ⟨h i (finset.mem_insert_self i t), λ i' hi', h i' (finset.mem_insert_of_mem hi')⟩,
end
-/

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
  rw balanced_iff,
  intros x hx a ha,
  rw convex_hull_eq at hx,
  simp only [exists_prop, exists_and_distrib_left, mem_set_of_eq] at hx,
  rcases hx with ⟨ι, t, f, f', h, hsum, hpos, hx⟩,
  rw convex_hull_eq,
  simp only [exists_prop, exists_and_distrib_left, mem_set_of_eq],
  use [ι, t, f, λ y, a • f' y],
  refine ⟨λ i hi, balanced_mem hs (h i hi) ha, hsum, hpos, _⟩,
  rw ←hx,
  simp_rw finset.center_mass,
  simp_rw finset.smul_sum,
  simp_rw (mul_smul _ _ _).symm,
  simp_rw smul_comm,
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

variables [topological_add_group E]

noncomputable
def maximal_seminorm_family : seminorm_family 𝕜 E (abs_convex_nhds_sets 𝕜 E) :=
λ s, gauge_seminorm (balanced.symmetric s.2.2.1) s.2.2.2 (absorbent_nhds_zero s.2.1)


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
  refine ⟨_, _, convex_Inter₂ (λ _ _, seminorm.convex_ball _ _ _)⟩,
  { rw [filter.bInter_finset_mem],
    intros i hi,
    rw ←mul_one r,
    rw ←real.norm_of_nonneg (le_of_lt hr),
    have hr' : 0 < ∥r∥ := by {rw real.norm_of_nonneg (le_of_lt hr), exact hr},
    rw ←seminorm.smul_ball_zero hr',
    rw ←smul_zero r,
    refine set_smul_mem_nhds_smul _ (ne_of_gt hr),
    simp only [smul_zero],
    rw maximal_seminorm_family_ball,
    simp only [subtype.val_eq_coe, interior_mem_nhds],
    exact abs_convex_nhds_sets.coe_nhds 𝕜 E i },
  refine balanced.Inter_finset (λ _ _, _),
  refine seminorm.balanced_ball_zero _ _,
  sorry,
end


-- Need to show that
-- scaling is preserved


end module
