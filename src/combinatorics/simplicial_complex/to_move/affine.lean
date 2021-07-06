/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simplicial_complex.to_move.convex
import linear_algebra.affine_space.finite_dimensional

variables {m n : ℕ} {E : Type*} [normed_group E] [normed_space ℝ E]
open_locale big_operators
open finset

lemma convex_subspace (M : Type*) [add_comm_group M] [module ℝ M] (s : affine_subspace ℝ M) :
  convex (s : set M) :=
λ x y hxs hys a b ha hb hab,
calc a • x + b • y = b • (y - x) + x : convex.combo_to_vadd hab
               ... ∈ s : s.2 _ hys hxs hxs

lemma convex_hull_subset_span_points (X : set E) :
  convex_hull X ⊆ affine_span ℝ X :=
convex_hull_min (subset_affine_span ℝ X) (convex_subspace E _)

lemma affine_combination_eq_center_mass {ι : Type*} {t : finset ι} {p : ι → E} {w : ι → ℝ}
  (hw₂ : ∑ i in t, w i = 1) :
  affine_combination t p w = center_mass t w p :=
begin
  rw affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one _ w _ hw₂ (0 : E),
  simp only [vsub_eq_sub, add_zero, finset.weighted_vsub_of_point_apply, vadd_eq_add, sub_zero],
  rw center_mass_eq_of_sum_1 _ _ hw₂,
end

lemma nontrivial_sum_of_affine_independent {X : finset E}
  (hX : affine_independent ℝ (λ p, p : (X : set E) → E))
  (w : E → ℝ) (hw₀ : ∑ i in X, w i = 0) (hw₁ : ∑ i in X, w i • i = 0) :
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

lemma unique_combination {X : finset E} (hX : affine_independent ℝ (λ p, p : (X : set E) → E))
  (w₁ w₂ : E → ℝ) (hw₁ : ∑ i in X, w₁ i = 1) (hw₂ : ∑ i in X, w₂ i = 1)
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

lemma affine_span_convex_hull_eq {X : set E} :
  affine_span ℝ (convex_hull X) = affine_span ℝ X :=
le_antisymm
  (((affine_subspace.gi _ _ _).gc _ _).2 (convex_hull_subset_span_points X))
  (affine_span_mono ℝ (subset_convex_hull X))

lemma disjoint_convex_hull_of_subsets {X : finset E}
  (hX : affine_independent ℝ (λ p, p : (X : set E) → E)) {Y₁ Y₂ : finset E}
  (hY₁ : Y₁ ⊆ X) (hY₂ : Y₂ ⊆ X) :
  convex_hull (Y₁ : set E) ∩ convex_hull (Y₂ : set E) ⊆ convex_hull (Y₁ ∩ Y₂ : set E) :=
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
  let w : E → ℝ,
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
    have : ite (x ∈ Y₁) (w₁ x) 0 - ite (x ∈ Y₂) (w₂ x) 0 = 0 := hX' x (hY₁ hx₁),
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
    exact t₁ x hx₁ (hx₂ hx₁) },
end

lemma finrank_le_finrank_of_le {x y : submodule ℝ E} (h : x ≤ y) [finite_dimensional ℝ y] :
  finite_dimensional.finrank ℝ x ≤ finite_dimensional.finrank ℝ y :=
begin
  let f : x →ₗ[ℝ] y := submodule.of_le h,
  have hf : function.injective f,
  { intros x₁ x₂ h',
    apply subtype.ext,
    apply subtype.ext_iff.1 h' },
  haveI : finite_dimensional ℝ x := submodule.finite_dimensional_of_le h,
  apply linear_map.finrank_le_finrank_of_injective hf,
end

-- convex_hull ↑X ⊆ convex_hull ↑Y implies that X.card <= Y.card if X is independent
theorem card_le_of_convex_hull_subset {X Y : finset E}
  (hX : affine_independent ℝ (λ p, p : (X : set E) → E))
  (hXY : convex_hull ↑X ⊆ convex_hull (Y : set E)) :
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
  have affine_span_le := affine_span_mono ℝ hXY,
  rw [affine_span_convex_hull_eq, affine_span_convex_hull_eq] at affine_span_le,
  have direction_le := affine_subspace.direction_le affine_span_le,
  letI : finite_dimensional ℝ (vector_span ℝ (Y : set E)),
  { apply finite_dimensional_vector_span_of_finite,
    exact Y.finite_to_set },
  rw direction_affine_span at direction_le,
  rw direction_affine_span at direction_le,
  have finrank_le := finrank_le_finrank_of_le direction_le,
  have dumb : set.range (λ (p : (X : set E)), ↑p) = (X : set E),
  { simp only [subtype.range_coe_subtype, finset.set_of_mem, finset.mem_coe] },
  rw ← dumb at finrank_le,
  rw finrank_vector_span_of_affine_independent hX X_eq_succ at finrank_le,
  have := finrank_vector_span_range_le ℝ (λ p, p : (Y : set E) → E) Y_eq_succ,
  have dumb₂ : set.range (λ (p : (Y : set E)), ↑p) = (Y : set E),
  { simp only [subtype.range_coe_subtype, finset.set_of_mem, finset.mem_coe] },
  rw dumb₂ at this,
  have := le_trans finrank_le this,
  rwa nat.sub_le_sub_right_iff at this,
  exact Y_card_pos,
end

lemma size_bound [finite_dimensional ℝ E] {X : finset E}
  (hX : affine_independent ℝ (λ p, p : (X : set E) → E)) :
  X.card ≤ finite_dimensional.finrank ℝ E + 1 :=
begin
  classical,
  cases X.eq_empty_or_nonempty,
  { simp [h] },
  rcases h with ⟨y, hy⟩,
  have y_mem : y ∈ (X : set E) := hy,
  have Xy : (↑X \ {y}) = (↑(X.erase y) : set E),
  { simp },
  have := hX,
  rw @affine_independent_set_iff_linear_independent_vsub ℝ _ _ _ _ _ _ ↑X y y_mem at this,
  letI q : fintype ↥((λ (p : E), p -ᵥ y) '' (↑X \ {y})),
  { apply set.fintype_image _ _,
    { apply_instance },
    rw Xy,
    exact finset_coe.fintype _ },
  have hX := finite_dimensional.fintype_card_le_finrank_of_linear_independent this,
  simp only [vsub_eq_sub, finite_dimensional.finrank_fin_fun, fintype.card_of_finset] at hX,
  rw finset.card_image_of_injective at hX,
  { simp only [set.to_finset_card] at hX,
    rw fintype.card_of_finset' (X.erase y) at hX,
    { rwa [finset.card_erase_of_mem hy, nat.pred_le_iff] at hX },
    { simp [and_comm] } },
  rintro p q h,
  simpa using h,
end.
