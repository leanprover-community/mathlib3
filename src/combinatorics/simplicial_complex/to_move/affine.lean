/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.convex.combination
import linear_algebra.affine_space.finite_dimensional

/-!
# To move
-/

variables {𝕜 E ι : Type*} [linear_ordered_field 𝕜] [add_comm_group E] [module 𝕜 E] {m n : ℕ}

open_locale big_operators
open finset

lemma convex_subspace (s : affine_subspace 𝕜 E) :
  convex 𝕜 (s : set E) :=
λ x y hxs hys a b ha hb hab,
calc a • x + b • y = b • (y - x) + x : convex.combo_eq_vadd hab
               ... ∈ s : s.2 _ hys hxs hxs

lemma convex_hull_subset_span_points (X : set E) :
  convex_hull 𝕜 X ⊆ affine_span 𝕜 X :=
convex_hull_min (subset_affine_span 𝕜 X) (convex_subspace _)

-- TODO (Bhavik): move these two, and use them to prove the old versions
lemma nontrivial_sum_of_affine_independent' {p : ι → E} {X : finset ι}
  (hX : affine_independent 𝕜 p) (w : ι → 𝕜)
  (hw₀ : ∑ i in X, w i = 0) (hw₁ : ∑ i in X, w i • p i = 0) :
∀ i ∈ X, w i = 0 :=
begin
  specialize hX _ _ hw₀ _,
  { rw finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ _ _ hw₀ (0 : E),
    rw finset.weighted_vsub_of_point_apply,
    simpa only [vsub_eq_sub, sub_zero, sum_finset_coe (λ i, w i • p i)] },
  intros i hi,
  apply hX _ hi
end

lemma unique_combination' {p : ι → E} (X : finset ι)
  (hX : affine_independent 𝕜 p)
  (w₁ w₂ : ι → 𝕜) (hw₁ : ∑ i in X, w₁ i = 1) (hw₂ : ∑ i in X, w₂ i = 1)
  (same : ∑ i in X, w₁ i • p i = ∑ i in X, w₂ i • p i) :
  ∀ i ∈ X, w₁ i = w₂ i :=
begin
  let w := w₁ - w₂,
  suffices : ∀ i ∈ X, w i = 0,
  { intros i hi,
    apply eq_of_sub_eq_zero (this i hi) },
  apply nontrivial_sum_of_affine_independent' hX,
  { change ∑ i in X, (w₁ i - w₂ i) = _,
    rw [finset.sum_sub_distrib, hw₁, hw₂, sub_self] },
  { change ∑ i in X, (w₁ i - w₂ i) • p i = _,
    simp_rw [sub_smul, finset.sum_sub_distrib, same, sub_self] }
end

lemma nontrivial_sum_of_affine_independent {X : finset E}
  (hX : affine_independent 𝕜 (coe : (X : set E) → E))
  (w : E → 𝕜) (hw₀ : ∑ i in X, w i = 0) (hw₁ : ∑ i in X, w i • i = 0) :
  ∀ i ∈ X, w i = 0 :=
begin
  have hw₀' : ∑ (i : (X : set E)), w i = 0,
  { rwa [sum_finset_coe] },
  specialize hX _ _ hw₀' _,
  { rw finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ _ _ hw₀' (0 : E),
    rw finset.weighted_vsub_of_point_apply,
    simpa only [vsub_eq_sub, sub_zero, sum_finset_coe (λ i, w i • i)] },
  intros i hi,
  apply hX ⟨i, hi⟩ (mem_univ _)
end

lemma unique_combination {X : finset E} (hX : affine_independent 𝕜 (coe : (X : set E) → E))
  (w₁ w₂ : E → 𝕜) (hw₁ : ∑ i in X, w₁ i = 1) (hw₂ : ∑ i in X, w₂ i = 1)
  (same : X.center_mass w₁ id = X.center_mass w₂ id) :
  ∀ i ∈ X, w₁ i = w₂ i :=
begin
  let w := w₁ - w₂,
  suffices : ∀ i ∈ X, w i = 0,
  { intros i hi,
    apply eq_of_sub_eq_zero (this i hi) },
  apply nontrivial_sum_of_affine_independent hX w,
  { change ∑ i in X, (w₁ i - w₂ i) = _,
    rw [finset.sum_sub_distrib, hw₁, hw₂, sub_self] },
  { change ∑ i in X, (w₁ i - w₂ i) • i = _,
    simp_rw [sub_smul, finset.sum_sub_distrib, ←finset.center_mass_eq_of_sum_1 _ _ hw₁,
      ←finset.center_mass_eq_of_sum_1 _ _ hw₂],
    apply sub_eq_zero_of_eq same }
end

lemma affine_span_convex_hull_eq {X : set E} : affine_span 𝕜 (convex_hull 𝕜 X) = affine_span 𝕜 X :=
le_antisymm
  (((affine_subspace.gi _ _ _).gc _ _).2 (convex_hull_subset_span_points X))
  (affine_span_mono 𝕜 (subset_convex_hull 𝕜 X))

lemma disjoint_convex_hull_of_subsets {X : finset E}
  (hX : affine_independent 𝕜 (coe : (X : set E) → E)) {Y₁ Y₂ : finset E}
  (hY₁ : Y₁ ⊆ X) (hY₂ : Y₂ ⊆ X) :
  convex_hull 𝕜 (Y₁ : set E) ∩ convex_hull 𝕜 (Y₂ : set E) ⊆ convex_hull 𝕜 (Y₁ ∩ Y₂ : set E) :=
begin
  classical,
  rintro x ⟨hx₁, hx₂⟩,
  rw ←coe_inter,
  rw finset.convex_hull_eq at hx₁ hx₂,
  rcases hx₁ with ⟨w₁, h₁w₁, h₂w₁, h₃w₁⟩,
  rcases hx₂ with ⟨w₂, h₁w₂, h₂w₂, h₃w₂⟩,
  rw center_mass_eq_of_sum_1 _ _ h₂w₁ at h₃w₁,
  rw center_mass_eq_of_sum_1 _ _ h₂w₂ at h₃w₂,
  dsimp at h₃w₁ h₃w₂,
  let w : E → 𝕜,
  { intro x,
    apply (if x ∈ Y₁ then w₁ x else 0) - (if x ∈ Y₂ then w₂ x else 0) },
  have h₁w : ∑ i in X, w i = 0,
  { rw [finset.sum_sub_distrib, ←sum_filter, filter_mem_eq_inter, ←sum_filter,
      filter_mem_eq_inter, (finset.inter_eq_right_iff_subset _ _).2 hY₁,
      (finset.inter_eq_right_iff_subset _ _).2 hY₂, h₂w₁, h₂w₂],
    simp only [sub_self] },
  have : ∑ (i : E) in X, w i • i = 0,
  { simp only [sub_smul, zero_smul, ite_smul, finset.sum_sub_distrib, ←finset.sum_filter, h₃w₁,
      finset.filter_mem_eq_inter, (finset.inter_eq_right_iff_subset _ _).2 hY₁,
      (finset.inter_eq_right_iff_subset _ _).2 hY₂, h₃w₂, sub_self] },
  have hX' := nontrivial_sum_of_affine_independent hX w h₁w this,
  have t₁ : ∀ x, x ∈ Y₁ → x ∉ Y₂ → w₁ x = 0,
  { intros x hx₁ hx₂,
    have : ite (x ∈ Y₁) (w₁ x) 0 - ite (x ∈ Y₂) (w₂ x) 0 = 0 := hX' _ (hY₁ hx₁),
    simpa [hx₁, hx₂] using this },
  have h₄w₁ : ∑ (y : E) in Y₁ ∩ Y₂, w₁ y = 1,
  { rw [finset.sum_subset (finset.inter_subset_left Y₁ Y₂), h₂w₁],
    simp_intros x hx₁ hx₂,
    exact t₁ x hx₁ (hx₂ hx₁)},
  rw finset.convex_hull_eq,
  refine ⟨w₁, _, h₄w₁, _⟩,
  { simp only [and_imp, finset.mem_inter],
    intros y hy₁ hy₂,
    exact h₁w₁ y hy₁},
  { rw finset.center_mass_eq_of_sum_1 _ _ h₄w₁,
    dsimp only [id.def],
    rw [finset.sum_subset (finset.inter_subset_left Y₁ Y₂), h₃w₁],
    simp_intros x hx₁ hx₂,
    left,
    exact t₁ x hx₁ (hx₂ hx₁) }
end

lemma finrank_le_finrank_of_le {x y : submodule 𝕜 E} (h : x ≤ y) [finite_dimensional 𝕜 y] :
  finite_dimensional.finrank 𝕜 x ≤ finite_dimensional.finrank 𝕜 y :=
begin
  let f : x →ₗ[𝕜] y := submodule.of_le h,
  have hf : function.injective f,
  { intros x₁ x₂ h',
    apply subtype.ext,
    apply subtype.ext_iff.1 h' },
  haveI : finite_dimensional 𝕜 x := submodule.finite_dimensional_of_le h,
  apply linear_map.finrank_le_finrank_of_injective hf,
end

-- convex_hull 𝕜 ↑X ⊆ convex_hull 𝕜 ↑Y implies that X.card <= Y.card if X is independent
theorem card_le_of_convex_hull_subset {X Y : finset E}
  (hX : affine_independent 𝕜 (coe : (X : set E) → E))
  (hXY : convex_hull 𝕜 ↑X ⊆ convex_hull 𝕜 (Y : set E)) :
  X.card ≤ Y.card :=
begin
  cases X.eq_empty_or_nonempty with h₁ h₁,
  { subst h₁,
    simp },
  cases Y.eq_empty_or_nonempty with h₂ h₂,
  { subst h₂,
    simp only [finset.coe_empty, convex_hull_empty, set.subset_empty_iff, convex_hull_empty_iff,
      finset.coe_eq_empty] at hXY,
    subst hXY },
  have X_card_pos : 0 < X.card := finset.card_pos.2 h₁,
  have X_eq_succ : fintype.card (X : set E) = (X.card - 1) + 1,
  { simp [nat.sub_add_cancel ‹1 ≤ X.card›] },
  have Y_card_pos : 0 < Y.card := finset.card_pos.2 h₂,
  have Y_eq_succ : fintype.card (Y : set E) = (Y.card - 1) + 1,
  { simp [nat.sub_add_cancel ‹1 ≤ Y.card›] },
  have affine_span_le := affine_span_mono 𝕜 hXY,
  rw [affine_span_convex_hull_eq, affine_span_convex_hull_eq] at affine_span_le,
  have direction_le := affine_subspace.direction_le affine_span_le,
  letI : finite_dimensional 𝕜 (vector_span 𝕜 (Y : set E)),
  { apply finite_dimensional_vector_span_of_finite,
    exact Y.finite_to_set },
  rw direction_affine_span at direction_le,
  rw direction_affine_span at direction_le,
  have finrank_le := finrank_le_finrank_of_le direction_le,
  have dumb : set.range (λ (p : (X : set E)), ↑p) = (X : set E),
  { simp only [subtype.range_coe_subtype, finset.set_of_mem, finset.mem_coe] },
  rw ← dumb at finrank_le,
  rw hX.finrank_vector_span X_eq_succ at finrank_le,
  have := finrank_vector_span_range_le 𝕜 (coe : (Y : set E) → E) Y_eq_succ,
  have dumb₂ : set.range (λ (p : (Y : set E)), ↑p) = (Y : set E),
  { simp only [subtype.range_coe_subtype, finset.set_of_mem, finset.mem_coe] },
  rw dumb₂ at this,
  have := le_trans finrank_le this,
  rwa nat.sub_le_sub_right_iff at this,
  exact Y_card_pos,
end

lemma affine_independent.card_le_finrank_succ [finite_dimensional 𝕜 E] {s : finset E}
  (ha : affine_independent 𝕜 (coe : (s : set E) → E)) :
  s.card ≤ finite_dimensional.finrank 𝕜 E + 1 :=
begin
  classical,
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty,
  { rw finset.card_empty, exact zero_le _ },
  rw [@affine_independent_set_iff_linear_independent_vsub 𝕜 _ _ _ _ _ _ ↑s x hx,
    ←coe_erase, ←coe_image] at ha,
  letI : fintype ↥((λ (p : E), p -ᵥ x) '' (↑s \ {x})),
  { apply set.fintype_image _ _,
    { apply_instance },
    rw ←coe_erase,
    exact finset_coe.fintype _ },
  have hs := finite_dimensional.fintype_card_le_finrank_of_linear_independent ha,
  simp_rw coe_sort_coe at hs,
  rwa [fintype.card_coe, finset.card_image_of_injective, finset.card_erase_of_mem hx,
    tsub_le_iff_right] at hs,
  { simp_rw vsub_eq_sub,
    exact λ _ _, sub_left_inj.1 }
end
