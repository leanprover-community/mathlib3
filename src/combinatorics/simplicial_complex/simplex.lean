/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.convex.topology
import combinatorics.simplicial_complex.extreme
import combinatorics.simplicial_complex.to_move
import order.filter.archimedean

/-!
# Definitions and lemmas about individual simplices

These are phrased in terms of finite sets of points, and the assumption of affine independence
(ie non-degeneracy) is added to theorems.
-/

open set
open_locale big_operators classical

variables {𝕜 E ι : Type*}

section ordered_ring
variables (𝕜) [ordered_ring 𝕜] [add_comm_group E] [module 𝕜 E] {s t : finset E} {x : E}

/-- The combinatorial frontier of a simplex as a subspace. -/
def combi_frontier (s : finset E) : set E := ⋃ t ⊂ s, convex_hull 𝕜 ↑t

/-- The interior of a simplex as a subspace. Note this is *not* the same thing as the topological
interior of the underlying space. -/
def combi_interior (s : finset E) : set E := convex_hull 𝕜 ↑s \ combi_frontier 𝕜 s

variables {𝕜}

lemma mem_combi_frontier_iff :
  x ∈ combi_frontier 𝕜 s ↔ ∃ t, t ⊂ s ∧ x ∈ convex_hull 𝕜 (t : set E) :=
by simp [combi_frontier]

lemma combi_frontier_subset_convex_hull : combi_frontier 𝕜 s ⊆ convex_hull 𝕜 ↑s :=
Union₂_subset $ λ t ht, convex_hull_mono ht.1

lemma combi_interior_subset_convex_hull : combi_interior 𝕜 s ⊆ convex_hull 𝕜 ↑s := diff_subset _ _

lemma combi_frontier_empty : combi_frontier 𝕜 (∅ : finset E) = ∅ :=
begin
  apply set.eq_empty_of_subset_empty,
  convert combi_frontier_subset_convex_hull,
  rw [finset.coe_empty, convex_hull_empty],
end

lemma combi_interior_empty : combi_interior 𝕜 (∅ : finset E) = ∅ :=
begin
  apply set.eq_empty_of_subset_empty,
  convert combi_interior_subset_convex_hull,
  rw [finset.coe_empty, convex_hull_empty],
end

lemma combi_frontier_singleton : combi_frontier 𝕜 ({x} : finset E) = ∅ :=
begin
  apply set.eq_empty_of_subset_empty,
  rintro y hy,
  rw mem_combi_frontier_iff at hy,
  obtain ⟨s, hs, hys⟩ := hy,
  rw finset.eq_empty_of_ssubset_singleton hs at hys,
  simp at hys,
  exact hys,
end

lemma combi_interior_singleton : combi_interior 𝕜 ({x} : finset E) = {x} :=
begin
  unfold combi_interior,
  rw combi_frontier_singleton,
  simp,
end

lemma convex_hull_eq_interior_union_combi_frontier :
  convex_hull 𝕜 ↑s = combi_interior 𝕜 s ∪ combi_frontier 𝕜 s :=
(diff_union_of_subset combi_frontier_subset_convex_hull).symm

lemma simplex_combi_interiors_cover : convex_hull 𝕜 ↑s = ⋃ (t ⊆ s), combi_interior 𝕜 t :=
begin
  apply subset.antisymm _ _,
  { apply s.strong_induction_on,
    rintro s ih x hx,
    by_cases x ∈ combi_frontier 𝕜 s,
    { rw [combi_frontier] at h,
      simp only [exists_prop, set.mem_Union] at h,
      obtain ⟨t, st, ht⟩ := h,
      specialize ih _ st ht,
      simp only [exists_prop, set.mem_Union] at ⊢ ih,
      obtain ⟨Z, Zt, hZ⟩ := ih,
      exact ⟨_, subset.trans Zt st.1, hZ⟩ },
    { exact subset_bUnion_of_mem (λ _ t, t) ⟨hx, h⟩ } },
  { exact Union₂_subset (λ t ht, subset.trans (diff_subset _ _) (convex_hull_mono ht)) },
end

end ordered_ring

section linear_ordered_field
variables [linear_ordered_field 𝕜] [add_comm_group E] [module 𝕜 E] {s t : finset E} {x : E}

lemma combi_frontier_eq :
  combi_frontier 𝕜 s =
    {x : E | ∃ (w : E → 𝕜) (hw₀ : ∀ y ∈ s, 0 ≤ w y) (hw₁ : ∑ y in s, w y = 1)
        (hw₂ : ∃ y ∈ s, w y = 0), s.center_mass w id = x} :=
begin
  ext x,
  simp_rw [combi_frontier, set.mem_Union, set.mem_set_of_eq],
  split,
  { simp only [and_imp, exists_prop, exists_imp_distrib],
    intros t ts hx,
    rw [finset.convex_hull_eq, set.mem_set_of_eq] at hx,
    rcases hx with ⟨w, hw₀, hw₁, hx⟩,
    rcases finset.exists_of_ssubset ts with ⟨y, hys, hyt⟩,
    let w' := λ z, if z ∈ t then w z else 0,
    have hw'₁ : s.sum w' = 1,
    { rwa [←finset.sum_subset ts.1, finset.sum_extend_by_zero],
      simp only [ite_eq_right_iff],
      tauto },
    refine ⟨w', _, hw'₁, ⟨_, ‹y ∈ s›, _⟩, _⟩,
    { intros y hy,
      change 0 ≤ ite (y ∈ t) (w y) 0,
      split_ifs,
      { apply hw₀ y ‹_› },
      { refl } },
    { apply if_neg ‹y ∉ t› },
    rw ← finset.center_mass_subset id ts.1,
    { rw [finset.center_mass_eq_of_sum_1],
      { rw finset.center_mass_eq_of_sum_1 _ _ hw₁ at hx,
        rw ← hx,
        apply finset.sum_congr rfl,
        intros x hx,
        change ite _ _ _ • _ = _,
        rw if_pos hx },
      rwa finset.sum_extend_by_zero },
    exact λ i _ hi, if_neg hi },
  { simp only [and_imp, exists_prop, exists_imp_distrib],
    intros w hw₁ hw₂ y hy₁ hy₂ hy₃,
    refine ⟨s.erase y, finset.erase_ssubset hy₁, _⟩,
    rw [finset.convex_hull_eq, set.mem_set_of_eq],
    refine ⟨w, λ z hz, hw₁ z (s.erase_subset _ hz), _, _⟩,
    rw finset.sum_erase _ hy₂,
    apply hw₂,
    rwa finset.center_mass_subset _ (s.erase_subset _),
    intros i hi₁ hi₂,
    simp only [hi₁, and_true, not_not, finset.mem_erase] at hi₂,
    subst hi₂,
    apply hy₂ }
end

lemma combi_interior_subset_positive_weighings :
  combi_interior 𝕜 s ⊆
    {x : E | ∃ (w : E → 𝕜) (hw₀ : ∀ y ∈ s, 0 < w y) (hw₁ : ∑ y in s, w y = 1),
      s.center_mass w id = x} :=
begin
  rw [combi_interior, finset.convex_hull_eq, combi_frontier_eq],
  rintro x,
  simp only [not_exists, and_imp, not_and, mem_set_of_eq, mem_diff, exists_imp_distrib],
  rintro w hw₁ hw₂ hw₃ q,
  refine ⟨w, λ y hy, _, hw₂, hw₃⟩,
  exact lt_of_le_of_ne (hw₁ _ hy) (ne.symm (λ t, q w hw₁ hw₂ y hy t hw₃))
end

lemma combi_interior_eq (hs : affine_independent 𝕜 (coe : (s : set E) → E)) :
  combi_interior 𝕜 s =
    {x : E | ∃ (w : E → 𝕜) (hw₀ : ∀ y ∈ s, 0 < w y) (hw₁ : ∑ y in s, w y = 1),
      s.center_mass w id = x} :=
begin
  apply subset.antisymm combi_interior_subset_positive_weighings,
  rintro x,
  rw [combi_interior, finset.convex_hull_eq, combi_frontier_eq],
  simp only [not_exists, and_imp, not_and, mem_set_of_eq, mem_diff, exists_imp_distrib],
  intros w hw₁ hw₂ hw₃,
  refine ⟨⟨w, λ y hy, le_of_lt (hw₁ y hy), hw₂, hw₃⟩, _⟩,
  intros w' hw'₁ hw'₂ y hy₁ hy₂ hw'₃,
  rw ← hw₃ at hw'₃,
  rw (unique_combination hs w' w hw'₂ hw₂ hw'₃) y hy₁ at hy₂,
  exact (hw₁ y hy₁).ne' hy₂
end

lemma centroid_mem_combi_interior (hs : affine_independent 𝕜 (coe : (s : set E) → E))
  (hsnonempty : s.nonempty) :
  s.centroid 𝕜 id ∈ combi_interior 𝕜 s :=
begin
  rw finset.centroid_def,
  have hsweights := s.sum_centroid_weights_eq_one_of_nonempty 𝕜 hsnonempty,
  rw affine_combination_eq_center_mass hsweights,
  rw combi_interior_eq hs,
  refine ⟨_, _, hsweights, rfl⟩,
  intros y hy,
  simpa [finset.card_pos] using hsnonempty,
end

protected lemma _root_.finset.nonempty.combi_interior
  (hs : affine_independent 𝕜 (coe : (s : set E) → E)) (hsnonempty : s.nonempty) :
  (combi_interior 𝕜 s).nonempty :=
⟨s.centroid 𝕜 id, centroid_mem_combi_interior hs hsnonempty⟩

lemma combi_interior.inj (hs : affine_independent 𝕜 (coe : (s : set E) → E))
  (ht : affine_independent 𝕜 (coe : (t : set E) → E))
  (h : combi_interior 𝕜 s = combi_interior 𝕜 t) :
  s = t := sorry

lemma convex_combi_interior (hs : affine_independent 𝕜 (coe : (s : set E) → E)) :
  convex 𝕜 (combi_interior 𝕜 s) :=
begin
  rw convex_iff_forall_pos,
  intros x y hx hy t₁ t₂ ht₁ ht₂ h,
  rw combi_interior_eq hs at hx hy ⊢,
  rcases hx with ⟨h₁, h₂, h₃, rfl⟩,
  rcases hy with ⟨h₄, h₅, h₆, rfl⟩,
  refine ⟨λ x, t₁ * h₁ x + t₂ * h₄ x, λ x hx, _, _, _⟩,
  { exact add_pos (mul_pos ht₁ (h₂ x hx)) (mul_pos ht₂ (h₅ x hx)) },
  { rw [finset.sum_add_distrib, ←finset.mul_sum, ←finset.mul_sum, h₃, h₆],
    simp [h] },
  rw finset.center_mass_segment _ _ _ _ h₃ h₆ _ _ h,
end

end linear_ordered_field

section real
section topological_space
variables [topological_space E] [add_comm_group E] [module ℝ E] [topological_add_group E]
  [has_continuous_smul ℝ E] [t2_space E] {s t : finset E}

lemma finset.is_closed_convex_hull (s : finset E) : is_closed (convex_hull ℝ (s : set E)) :=
s.finite_to_set.is_closed_convex_hull

lemma is_closed_combi_frontier : is_closed (combi_frontier ℝ s) :=
begin
  refine is_closed_bUnion _ (λ t _, t.is_closed_convex_hull),
  suffices : set.finite {t | t ⊆ s},
  { exact this.subset (λ i h, h.1) },
  convert s.powerset.finite_to_set using 1,
  ext,
  simp,
end

/-- `combi_interior 𝕜 s` is the topological interior iff `s` is of dimension `m`. -/
lemma interiors_agree_of_full_dimensional [finite_dimensional ℝ E]
  (hs : affine_independent ℝ (coe : (s : set E) → E))
  (hscard : s.card = finite_dimensional.finrank ℝ E + 1) :
  combi_interior ℝ s = interior (convex_hull ℝ ↑s) :=
begin
  unfold combi_interior,
  sorry
end

lemma frontiers_agree_of_full_dimensional [finite_dimensional ℝ E]
  (hscard : s.card = finite_dimensional.finrank ℝ E + 1) :
  combi_frontier ℝ s = frontier (convex_hull ℝ ↑s) :=
begin
  ext x,
  split,
  { unfold combi_frontier,
    simp_rw set.mem_Union,
    rintro ⟨t, hts, hx⟩,
    split,
    { exact subset_closure (convex_hull_mono hts.1 hx) },
    { rintro h,
      sorry,
      --have :=  finset.convex_hull_eq,
     } },
  { rintro ⟨h, g⟩,
    sorry
  }
end

end topological_space

section semi_normed_group
variables [semi_normed_group E] [normed_space ℝ E] {s t : finset E}

lemma subset_closure_combi_interior (hs : affine_independent ℝ (coe : (s : set E) → E)) :
  (s : set E) ⊆ closure (combi_interior ℝ s) :=
begin
  rintro x (hx : x ∈ s),
  apply seq_closure_subset_closure,
  have hsnonempty : s.nonempty := ⟨x, hx⟩,
  have centroid_weights : ∑ (i : E) in s, finset.centroid_weights ℝ s i = 1,
  { apply finset.sum_centroid_weights_eq_one_of_nonempty ℝ _ hsnonempty },
  refine ⟨λ n, _, λ n, _, _⟩,
  { apply ((n:ℝ)+2)⁻¹ • s.centroid ℝ id + (1-((n:ℝ)+2)⁻¹) • x },
  { rw finset.centroid_def,
    rw affine_combination_eq_center_mass _,
    { rw ←id.def x,
      rw ←finset.center_mass_ite_eq _ _ id hx,
      rw finset.center_mass_segment,
      { rw combi_interior_eq hs,
        refine ⟨_, _, _, rfl⟩,
        { simp only [mul_boole, finset.centroid_weights_apply],
          intros y hy,
          apply add_pos_of_pos_of_nonneg,
          { apply mul_pos,
            { rw inv_pos,
              norm_cast,
              simp, },
            { rw inv_pos,
              norm_cast,
              rwa finset.card_pos } },
          { split_ifs,
            { rw sub_nonneg,
              apply inv_le_one,
              norm_cast,
              apply nat.succ_pos },
            { refl } } },
        rw [finset.sum_add_distrib, ←finset.mul_sum, centroid_weights, ←finset.mul_sum,
          finset.sum_boole, finset.filter_eq],
        simp [hx] },
      { apply centroid_weights },
      { simp [finset.sum_boole, finset.filter_eq, hx] },
      { simp only [add_sub_cancel'_right] } },
    apply finset.sum_centroid_weights_eq_one_of_nonempty ℝ _ hsnonempty },
  { rw tendsto_iff_norm_tendsto_zero,
    convert_to filter.tendsto (λ (e:ℕ), ((e:ℝ)+2)⁻¹ * ∥s.centroid ℝ id - x∥) filter.at_top _,
    { ext n,
      rw [add_sub_assoc, sub_smul, sub_right_comm, one_smul, sub_self, zero_sub, ←smul_neg,
        ←smul_add, norm_smul_of_nonneg, ←sub_eq_add_neg],
      rw inv_nonneg,
      norm_cast,
      apply nat.zero_le },
    suffices : filter.tendsto (λ (e : ℕ), ((↑(e + 2):ℝ))⁻¹) filter.at_top (nhds 0),
    { simpa using this.mul_const _ },
    refine tendsto_inv_at_top_zero.comp _,
    rw tendsto_coe_nat_at_top_iff,
    apply filter.tendsto_add_at_top_nat }
end

variables [t2_space E]

-- Affine indep is necessary, since if not combi_interior can be empty
lemma closure_combi_interior_eq_convex_hull (hs : affine_independent ℝ (coe : (s : set E) → E)) :
  closure (combi_interior ℝ s) = convex_hull ℝ (s : set E) :=
begin
  refine set.subset.antisymm _
    (convex_hull_min (subset_closure_combi_interior hs) (convex_combi_interior hs).closure),
  rw s.is_closed_convex_hull.closure_subset_iff,
  exact combi_interior_subset_convex_hull,
end

lemma convex_hull_subset_convex_hull_of_combi_interior_subset_combi_interior
  (hs : affine_independent ℝ (coe : (s : set E) → E))
  (ht : affine_independent ℝ (coe : (t : set E) → E)) :
  combi_interior ℝ s ⊆ combi_interior ℝ t → convex_hull ℝ (s : set E) ⊆ convex_hull ℝ (t : set E) :=
begin
  rw ← closure_combi_interior_eq_convex_hull hs,
  rw ← closure_combi_interior_eq_convex_hull ht,
  intro h,
  apply closure_mono h,
end

end semi_normed_group
end real
