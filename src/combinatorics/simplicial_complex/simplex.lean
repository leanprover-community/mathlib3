/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.convex.topology
import combinatorics.simplicial_complex.extreme
import order.filter.archimedean

/-!
# Definitions and lemmas about individual simplices

These are phrased in terms of finite sets of points, and the assumption of affine independence
(ie non-degeneracy) is added to theorems.
-/

open_locale big_operators classical
open set

variables {E : Type*} [normed_group E] [normed_space ℝ E] {x : E} {X Y : finset E}
-- variables {m : ℕ}
-- local notation `E'` := fin m → ℝ

/--
The combinatorial frontier of a simplex as a subspace.
-/
def combi_frontier (X : finset E) :
  set E :=
⋃ Y ⊂ X, convex_hull 𝕜 ↑Y

lemma mem_combi_frontier_iff :
  x ∈ combi_frontier X ↔ ∃ Y, Y ⊂ X ∧ x ∈ convex_hull 𝕜 (Y : set E) :=
by simp [combi_frontier]

lemma combi_frontier_singleton :
  combi_frontier ({x} : finset E) = ∅ :=
begin
  apply set.eq_empty_of_subset_empty,
  rintro y hy,
  rw mem_combi_frontier_iff at hy,
  obtain ⟨X, hX, hyX⟩ := hy,
  rw finset.eq_empty_of_ssubset_singleton hX at hyX,
  simp at hyX,
  exact hyX,
end

lemma combi_frontier_eq :
  combi_frontier X =
    {x : E | ∃ (w : E → ℝ) (hw₀ : ∀ y ∈ X, 0 ≤ w y) (hw₁ : ∑ y in X, w y = 1)
        (hw₂ : ∃ y ∈ X, w y = 0), X.center_mass w id = x} :=
begin
  ext x,
  simp_rw [combi_frontier, set.mem_Union, set.mem_set_of_eq],
  split,
  { simp only [and_imp, exists_prop, exists_imp_distrib],
    intros Y YX hx,
    rw [finset.convex_hull_eq, set.mem_set_of_eq] at hx,
    rcases hx with ⟨w, hw₀, hw₁, hx⟩,
    rcases finset.exists_of_ssubset YX with ⟨y, hyX, hyY⟩,
    let w' := λ z, if z ∈ Y then w z else 0,
    have hw'₁ : X.sum w' = 1,
    { rwa [←finset.sum_subset YX.1, finset.sum_extend_by_zero],
      simp only [ite_eq_right_iff],
      tauto },
    refine ⟨w', _, hw'₁, ⟨_, ‹y ∈ X›, _⟩, _⟩,
    { intros y hy,
      change 0 ≤ ite (y ∈ Y) (w y) 0,
      split_ifs,
      { apply hw₀ y ‹_› },
      { refl } },
    { apply if_neg ‹y ∉ Y› },
    rw ← finset.center_mass_subset id YX.1,
    { rw [finset.center_mass_eq_of_sum_1],
      { rw finset.center_mass_eq_of_sum_1 _ _ hw₁ at hx,
        rw ← hx,
        apply finset.sum_congr rfl,
        intros x hx,
        change ite _ _ _ • _ = _,
        rw if_pos hx },
      rwa finset.sum_extend_by_zero },
    intros i _ hi,
    apply if_neg hi },
  { simp only [and_imp, exists_prop, exists_imp_distrib],
    intros w hw₁ hw₂ y hy₁ hy₂ hy₃,
    refine ⟨X.erase y, finset.erase_ssubset hy₁, _⟩,
    rw [finset.convex_hull_eq, set.mem_set_of_eq],
    refine ⟨w, λ z hz, hw₁ z (X.erase_subset _ hz), _, _⟩,
    rw finset.sum_erase _ hy₂,
    apply hw₂,
    rwa finset.center_mass_subset _ (X.erase_subset _),
    intros i hi₁ hi₂,
    simp only [hi₁, and_true, not_not, finset.mem_erase] at hi₂,
    subst hi₂,
    apply hy₂ }
end


/--
The interior of a simplex as a subspace. Note this is *not* the same thing as the topological
interior of the underlying space.
-/
def combi_interior (X : finset E) :
  set E :=
convex_hull 𝕜 ↑X \ combi_frontier X

lemma combi_interior_singleton :
  combi_interior ({x} : finset E) = {x} :=
begin
  unfold combi_interior,
  rw combi_frontier_singleton,
  simp,
end

lemma combi_interior_subset_positive_weighings :
  combi_interior X ⊆
    {x : E | ∃ (w : E → ℝ) (hw₀ : ∀ y ∈ X, 0 < w y) (hw₁ : ∑ y in X, w y = 1),
      X.center_mass w id = x} :=
begin
  rw [combi_interior, finset.convex_hull_eq, combi_frontier_eq],
  rintro x,
  simp only [not_exists, and_imp, not_and, mem_set_of_eq, mem_diff, exists_imp_distrib],
  rintro w hw₁ hw₂ hw₃ q,
  refine ⟨w, λ y hy, _, hw₂, hw₃⟩,
  exact lt_of_le_of_ne (hw₁ _ hy) (ne.symm (λ t, q w hw₁ hw₂ y hy t hw₃))
end

lemma combi_interior_eq (hX : affine_independent 𝕜 (λ p, p : (X : set E) → E)) :
  combi_interior X =
    {x : E | ∃ (w : E → ℝ) (hw₀ : ∀ y ∈ X, 0 < w y) (hw₁ : ∑ y in X, w y = 1),
      X.center_mass w id = x} :=
begin
  apply subset.antisymm combi_interior_subset_positive_weighings,
  rintro x,
  rw [combi_interior, finset.convex_hull_eq, combi_frontier_eq],
  simp only [not_exists, and_imp, not_and, mem_set_of_eq, mem_diff, exists_imp_distrib],
  intros w hw₁ hw₂ hw₃,
  refine ⟨⟨w, λ y hy, le_of_lt (hw₁ y hy), hw₂, hw₃⟩, _⟩,
  intros w' hw'₁ hw'₂ y hy₁ hy₂ hw'₃,
  rw ← hw₃ at hw'₃,
  rw (unique_combination hX w' w hw'₂ hw₂ hw'₃) y hy₁ at hy₂,
  exact ne_of_gt (hw₁ y hy₁) hy₂
end

lemma centroid_mem_combi_interior (hX : affine_independent 𝕜 (λ p, p : (X : set E) → E))
  (hXnonempty : X.nonempty) :
  X.centroid ℝ id ∈ combi_interior X :=
begin
  rw finset.centroid_def,
  have hXweights := X.sum_centroid_weights_eq_one_of_nonempty ℝ hXnonempty,
  rw affine_combination_eq_center_mass hXweights,
  rw combi_interior_eq hX,
  refine ⟨_, _, hXweights, rfl⟩,
  intros y hy,
  simpa [finset.card_pos] using hXnonempty,
end

lemma nonempty_combi_interior_of_nonempty (hX : affine_independent 𝕜 (λ p, p : (X : set E) → E))
  (hXnonempty : X.nonempty) :
  (combi_interior X).nonempty :=
⟨X.centroid ℝ id, centroid_mem_combi_interior hX hXnonempty⟩

lemma combi_interior_subset_convex_hull :
  combi_interior X ⊆ convex_hull 𝕜 ↑X :=
diff_subset _ _

lemma combi_interior.inj (hX : affine_independent 𝕜 (λ p, p : (X : set E) → E))
  (hY : affine_independent 𝕜 (λ p, p : (Y : set E) → E)) (h : combi_interior X = combi_interior Y) :
  X = Y := sorry

lemma is_closed_convex_hull :
  is_closed (convex_hull 𝕜 (X : set E)) :=
X.finite_to_set.is_closed_convex_hull

lemma is_closed_combi_frontier :
  is_closed (combi_frontier X) :=
begin
  apply is_closed_bUnion,
  { suffices : set.finite {Y | Y ⊆ X},
    { exact this.subset (λ i h, h.1) },
    convert X.powerset.finite_to_set using 1,
    ext,
    simp },
  { intros i hi,
    apply is_closed_convex_hull }
end

lemma subset_closure_combi_interior (hX : affine_independent 𝕜 (λ p, p : (X : set E) → E)) :
  (X : set E) ⊆ closure (combi_interior X) :=
begin
  rintro x (hx : x ∈ X),
  apply sequential_closure_subset_closure,
  have hXnonempty : X.nonempty := ⟨x, hx⟩,
  have centroid_weights : ∑ (i : E) in X, finset.centroid_weights ℝ X i = 1,
  { apply finset.sum_centroid_weights_eq_one_of_nonempty ℝ _ hXnonempty },
  refine ⟨_, _, _⟩,
  { intro n,
    apply ((n:ℝ)+2)⁻¹ • X.centroid ℝ id + (1-((n:ℝ)+2)⁻¹) • x },
  { intro n,
    rw finset.centroid_def,
    rw affine_combination_eq_center_mass _,
    { rw ←id.def x,
      rw ←finset.center_mass_ite_eq _ _ id hx,
      rw finset.center_mass_segment,
      { rw combi_interior_eq hX,
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
    apply finset.sum_centroid_weights_eq_one_of_nonempty ℝ _ hXnonempty },
  { rw tendsto_iff_norm_tendsto_zero,
    convert_to filter.tendsto (λ (e:ℕ), ((e:ℝ)+2)⁻¹ * ∥X.centroid ℝ id - x∥) filter.at_top _,
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

lemma convex_combi_interior (hX : affine_independent 𝕜 (λ p, p : (X : set E) → E)) :
  convex 𝕜 (combi_interior X) :=
begin
  rw convex_iff_forall_pos,
  intros x y hx hy t₁ t₂ ht₁ ht₂ h,
  rw combi_interior_eq hX at hx hy ⊢,
  rcases hx with ⟨h₁, h₂, h₃, rfl⟩,
  rcases hy with ⟨h₄, h₅, h₆, rfl⟩,
  refine ⟨λ x, t₁ * h₁ x + t₂ * h₄ x, λ x hx, _, _, _⟩,
  { exact add_pos (mul_pos ht₁ (h₂ x hx)) (mul_pos ht₂ (h₅ x hx)) },
  { rw [finset.sum_add_distrib, ←finset.mul_sum, ←finset.mul_sum, h₃, h₆],
    simp [h] },
  rw finset.center_mass_segment _ _ _ _ h₃ h₆ _ _ h,
end

-- Affine indep is necessary, since if not combi_interior can be empty
lemma closure_combi_interior_eq_convex_hull (hX : affine_independent 𝕜 (λ p, p : (X : set E) → E)) :
  closure (combi_interior X) = convex_hull 𝕜 (X : set E) :=
begin
  apply set.subset.antisymm,
  { rw is_closed.closure_subset_iff is_closed_convex_hull,
    apply combi_interior_subset_convex_hull },
  refine convex_hull_min (subset_closure_combi_interior hX) _,
  apply convex.closure,
  apply convex_combi_interior hX,
end

lemma combi_frontier_subset_convex_hull :
  combi_frontier X ⊆ convex_hull 𝕜 ↑X :=
bUnion_subset (λ Y hY, convex_hull_mono hY.1)

lemma convex_hull_eq_interior_union_combi_frontier :
  convex_hull 𝕜 ↑X = combi_interior X ∪ combi_frontier X :=
(diff_union_of_subset combi_frontier_subset_convex_hull).symm

lemma convex_hull_subset_convex_hull_of_combi_interior_subset_combi_interior
  (hX : affine_independent 𝕜 (λ p, p : (X : set E) → E))
  (hY : affine_independent 𝕜 (λ p, p : (Y : set E) → E)) :
  combi_interior X ⊆ combi_interior Y → convex_hull 𝕜 (X : set E) ⊆ convex_hull 𝕜 (Y : set E) :=
begin
  rw ← closure_combi_interior_eq_convex_hull hX,
  rw ← closure_combi_interior_eq_convex_hull hY,
  intro h,
  apply closure_mono h,
end

lemma simplex_combi_interiors_cover :
  convex_hull 𝕜 ↑X = ⋃ (Y ⊆ X), combi_interior Y :=
begin
  apply subset.antisymm _ _,
  { apply X.strong_induction_on,
    rintro s ih x hx,
    by_cases x ∈ combi_frontier s,
    { rw [combi_frontier] at h,
      simp only [exists_prop, set.mem_Union] at h,
      obtain ⟨t, st, ht⟩ := h,
      specialize ih _ st ht,
      simp only [exists_prop, set.mem_Union] at ⊢ ih,
      obtain ⟨Z, Zt, hZ⟩ := ih,
      exact ⟨_, subset.trans Zt st.1, hZ⟩ },
    { exact subset_bUnion_of_mem (λ _ t, t) ⟨hx, h⟩ } },
  { exact bUnion_subset (λ Y hY, subset.trans (diff_subset _ _) (convex_hull_mono hY)) },
end

/- combi_interior X is the topological interior iff X is of dimension m -/
lemma interiors_agree_of_full_dimensional [finite_dimensional ℝ E]
  (hX : affine_independent 𝕜 (λ p, p : (X : set E) → E))
  (hXcard : X.card = finite_dimensional.finrank ℝ E + 1) :
  combi_interior X = interior (convex_hull 𝕜 ↑X) :=
begin
  --rw ← closure_combi_interior_eq_convex_hull,
  unfold combi_interior,
  sorry
end

lemma frontiers_agree_of_full_dimensional [finite_dimensional ℝ E]
  (hXcard : X.card = finite_dimensional.finrank ℝ E + 1) :
  combi_frontier X = frontier (convex_hull 𝕜 ↑X) :=
begin
  ext x,
  split,
  { unfold combi_frontier,
    simp_rw set.mem_Union,
    rintro ⟨Y, hYX, hx⟩,
    split,
    { exact subset_closure (convex_hull_mono hYX.1 hx) },
    {   rintro h,
      sorry,
      --have :=  finset.convex_hull_eq,
     }
  },
  { rintro ⟨h, g⟩,
    sorry
  }
end
