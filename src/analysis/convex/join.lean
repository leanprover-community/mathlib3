/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import analysis.convex.combination

/-!
# Convex join

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the convex join of two sets. The convex join of `s` and `t` is the union of the
segments with one end in `s` and the other in `t`. This is notably a useful gadget to deal with
convex hulls of finite sets.
-/

open set
open_locale big_operators

variables {ι : Sort*} {𝕜 E : Type*}

section ordered_semiring
variables (𝕜) [ordered_semiring 𝕜] [add_comm_monoid E] [module 𝕜 E] {s t s₁ s₂ t₁ t₂ u : set E}
  {x y : E}

/-- The join of two sets is the union of the segments joining them. This can be interpreted as the
topological join, but within the original space. -/
def convex_join (s t : set E) : set E := ⋃ (x ∈ s) (y ∈ t), segment 𝕜 x y

variables {𝕜}

lemma mem_convex_join : x ∈ convex_join 𝕜 s t ↔ ∃ (a ∈ s) (b ∈ t), x ∈ segment 𝕜 a b :=
by simp [convex_join]

lemma convex_join_comm (s t : set E) : convex_join 𝕜 s t = convex_join 𝕜 t s :=
(Union₂_comm _).trans $ by simp_rw [convex_join, segment_symm]

lemma convex_join_mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : convex_join 𝕜 s₁ t₁ ⊆ convex_join 𝕜 s₂ t₂ :=
bUnion_mono hs $ λ x hx, bUnion_mono ht $ λ y hy, subset.rfl

lemma convex_join_mono_left (hs : s₁ ⊆ s₂) : convex_join 𝕜 s₁ t ⊆ convex_join 𝕜 s₂ t :=
convex_join_mono hs subset.rfl

lemma convex_join_mono_right (ht : t₁ ⊆ t₂) : convex_join 𝕜 s t₁ ⊆ convex_join 𝕜 s t₂ :=
convex_join_mono subset.rfl ht

@[simp] lemma convex_join_empty_left (t : set E) : convex_join 𝕜 ∅ t = ∅ := by simp [convex_join]
@[simp] lemma convex_join_empty_right (s : set E) : convex_join 𝕜 s ∅ = ∅ := by simp [convex_join]

@[simp] lemma convex_join_singleton_left (t : set E) (x : E) :
  convex_join 𝕜 {x} t = ⋃ (y ∈ t), segment 𝕜 x y := by simp [convex_join]

@[simp] lemma convex_join_singleton_right (s : set E) (y : E) :
  convex_join 𝕜 s {y} = ⋃ (x ∈ s), segment 𝕜 x y := by simp [convex_join]

@[simp] lemma convex_join_singletons (x : E) : convex_join 𝕜 {x} {y} = segment 𝕜 x y :=
by simp [convex_join]

@[simp] lemma convex_join_union_left (s₁ s₂ t : set E) :
  convex_join 𝕜 (s₁ ∪ s₂) t = convex_join 𝕜 s₁ t ∪ convex_join 𝕜 s₂ t :=
by simp_rw [convex_join, mem_union, Union_or, Union_union_distrib]

@[simp] lemma convex_join_union_right (s t₁ t₂ : set E) :
  convex_join 𝕜 s (t₁ ∪ t₂) = convex_join 𝕜 s t₁ ∪ convex_join 𝕜 s t₂ :=
by simp_rw [convex_join, mem_union, Union_or, Union_union_distrib]

@[simp] lemma convex_join_Union_left (s : ι → set E) (t : set E) :
  convex_join 𝕜 (⋃ i, s i) t = ⋃ i, convex_join 𝕜 (s i) t :=
by { simp_rw [convex_join, mem_Union, Union_exists], exact Union_comm _ }

@[simp] lemma convex_join_Union_right (s : set E) (t : ι → set E) :
  convex_join 𝕜 s (⋃ i, t i) = ⋃ i, convex_join 𝕜 s (t i) :=
by simp_rw [convex_join_comm s, convex_join_Union_left]

lemma segment_subset_convex_join (hx : x ∈ s) (hy : y ∈ t) : segment 𝕜 x y ⊆ convex_join 𝕜 s t :=
(subset_Union₂ y hy).trans (subset_Union₂ x hx)

lemma subset_convex_join_left (h : t.nonempty) : s ⊆ convex_join 𝕜 s t :=
λ x hx, let ⟨y, hy⟩ := h in segment_subset_convex_join hx hy $ left_mem_segment _ _ _

lemma subset_convex_join_right (h : s.nonempty) : t ⊆ convex_join 𝕜 s t :=
λ y hy, let ⟨x, hx⟩ := h in segment_subset_convex_join hx hy $ right_mem_segment _ _ _

lemma convex_join_subset (hs : s ⊆ u) (ht : t ⊆ u) (hu : convex 𝕜 u) : convex_join 𝕜 s t ⊆ u :=
Union₂_subset $ λ x hx, Union₂_subset $ λ y hy, hu.segment_subset (hs hx) (ht hy)

lemma convex_join_subset_convex_hull (s t : set E) : convex_join 𝕜 s t ⊆ convex_hull 𝕜 (s ∪ t) :=
convex_join_subset ((subset_union_left _ _).trans $ subset_convex_hull _ _)
  ((subset_union_right _ _).trans $ subset_convex_hull _ _) $ convex_convex_hull _ _

end ordered_semiring

section linear_ordered_field
variables [linear_ordered_field 𝕜] [add_comm_group E] [module 𝕜 E] {s t u : set E} {x y : E}

lemma convex_join_assoc_aux (s t u : set E) :
  convex_join 𝕜 (convex_join 𝕜 s t) u ⊆ convex_join 𝕜 s (convex_join 𝕜 t u) :=
begin
  simp_rw [subset_def, mem_convex_join],
  rintro _ ⟨z, ⟨x, hx, y, hy, a₁, b₁, ha₁, hb₁, hab₁, rfl⟩, z, hz, a₂, b₂, ha₂, hb₂, hab₂, rfl⟩,
  obtain rfl | hb₂ := hb₂.eq_or_lt,
  { refine ⟨x, hx, y, ⟨y, hy, z, hz, left_mem_segment _ _ _⟩, a₁, b₁, ha₁, hb₁, hab₁, _⟩,
    rw add_zero at hab₂,
    rw [hab₂, one_smul, zero_smul, add_zero] },
  have ha₂b₁ : 0 ≤ a₂ * b₁ := mul_nonneg ha₂ hb₁,
  have hab : 0 < a₂ * b₁ + b₂ := add_pos_of_nonneg_of_pos ha₂b₁ hb₂,
  refine ⟨x, hx, ((a₂ * b₁) / (a₂ * b₁ + b₂)) • y + (b₂ / (a₂ * b₁ + b₂)) • z,
    ⟨y, hy, z, hz, _, _, _, _, _, rfl⟩, a₂ * a₁, a₂ * b₁ + b₂, mul_nonneg ha₂ ha₁, hab.le, _, _⟩,
  { exact div_nonneg ha₂b₁ hab.le },
  { exact div_nonneg hb₂.le hab.le },
  { rw [←add_div, div_self hab.ne'] },
  { rw [←add_assoc, ←mul_add, hab₁, mul_one, hab₂] },
  { simp_rw [smul_add, ←mul_smul, mul_div_cancel' _ hab.ne', add_assoc] }
end

lemma convex_join_assoc (s t u : set E) :
  convex_join 𝕜 (convex_join 𝕜 s t) u = convex_join 𝕜 s (convex_join 𝕜 t u) :=
begin
  refine (convex_join_assoc_aux _ _ _).antisymm _,
  simp_rw [convex_join_comm s, convex_join_comm _ u],
  exact convex_join_assoc_aux _ _ _,
end

lemma convex_join_left_comm (s t u : set E) :
  convex_join 𝕜 s (convex_join 𝕜 t u) = convex_join 𝕜 t (convex_join 𝕜 s u) :=
by simp_rw [←convex_join_assoc, convex_join_comm]

lemma convex_join_right_comm (s t u : set E) :
  convex_join 𝕜 (convex_join 𝕜 s t) u = convex_join 𝕜 (convex_join 𝕜 s u) t :=
by simp_rw [convex_join_assoc, convex_join_comm]

lemma convex_join_convex_join_convex_join_comm (s t u v : set E) :
  convex_join 𝕜 (convex_join 𝕜 s t) (convex_join 𝕜 u v) =
    convex_join 𝕜 (convex_join 𝕜 s u) (convex_join 𝕜 t v) :=
by simp_rw [←convex_join_assoc, convex_join_right_comm]

lemma convex_hull_insert (hs : s.nonempty) :
  convex_hull 𝕜 (insert x s) = convex_join 𝕜 {x} (convex_hull 𝕜 s) :=
begin
  classical,
  refine (convex_join_subset ((singleton_subset_iff.2 $ mem_insert _ _).trans $ subset_convex_hull
    _ _) (convex_hull_mono $ subset_insert _ _) $ convex_convex_hull _ _).antisymm' (λ x hx, _),
  rw convex_hull_eq at hx,
  obtain ⟨ι, t, w, z, hw₀, hw₁, hz, rfl⟩ := hx,
  have : (∑ i in t.filter (λ i, z i = x), w i) • x + ∑ i in t.filter (λ i, z i ≠ x), w i • z i =
    t.center_mass w z,
  { rw [finset.center_mass_eq_of_sum_1 _ _ hw₁, finset.sum_smul],
    convert finset.sum_filter_add_sum_filter_not _ _ (w • z) using 2,
    refine finset.sum_congr rfl (λ i hi, _),
    rw [pi.smul_apply', (finset.mem_filter.1 hi).2] },
  rw ←this,
  have hw₀' : ∀ i ∈ t.filter (λ i, z i ≠ x), 0 ≤ w i := λ i hi, hw₀ _ $ finset.filter_subset _ _ hi,
  obtain hw | hw := (finset.sum_nonneg hw₀').eq_or_gt,
  { rw [←finset.sum_filter_add_sum_filter_not _ (λ i, z i = x), hw, add_zero] at hw₁,
    rw [hw₁, one_smul, finset.sum_eq_zero, add_zero],
    { exact subset_convex_join_left hs.convex_hull (mem_singleton _) },
    simp_rw finset.sum_eq_zero_iff_of_nonneg hw₀' at hw,
    rintro i hi,
    rw [hw _ hi, zero_smul] },
  refine mem_convex_join.2 ⟨x, mem_singleton _, (t.filter $ λ i, z i ≠ x).center_mass w z,
    finset.center_mass_mem_convex_hull _ hw₀' hw (λ i hi, _),
    ∑ i in t.filter (λ i, z i = x), w i, ∑ i in t.filter (λ i, z i ≠ x), w i,
    finset.sum_nonneg (λ i hi, hw₀ _ $ finset.filter_subset _ _ hi), finset.sum_nonneg hw₀', _, _⟩,
  { rw finset.mem_filter at hi,
    exact mem_of_mem_insert_of_ne (hz _ hi.1) hi.2 },
  { rw [finset.sum_filter_add_sum_filter_not, hw₁] },
  { rw [finset.center_mass, smul_inv_smul₀ hw.ne', finset.sum_smul] }
end

lemma convex_join_segments (a b c d : E) :
  convex_join 𝕜 (segment 𝕜 a b) (segment 𝕜 c d) = convex_hull 𝕜 {a, b, c, d} :=
by simp only [convex_hull_insert, insert_nonempty, singleton_nonempty, convex_hull_pair,
    ←convex_join_assoc, convex_join_singletons]

lemma convex_join_segment_singleton (a b c : E) :
  convex_join 𝕜 (segment 𝕜 a b) {c} = convex_hull 𝕜 {a, b, c} :=
by rw [←pair_eq_singleton, ←convex_join_segments, segment_same, pair_eq_singleton]

lemma convex_join_singleton_segment (a b c : E) :
  convex_join 𝕜 {a} (segment 𝕜 b c) = convex_hull 𝕜 {a, b, c} :=
by rw [←segment_same 𝕜, convex_join_segments, insert_idem]

protected lemma convex.convex_join (hs : convex 𝕜 s) (ht : convex 𝕜 t) :
  convex 𝕜 (convex_join 𝕜 s t) :=
begin
  rw convex_iff_segment_subset at ⊢ ht hs,
  simp_rw mem_convex_join,
  rintro x ⟨xa, hxa, xb, hxb, hx⟩ y ⟨ya, hya, yb, hyb, hy⟩,
  refine (segment_subset_convex_join hx hy).trans _,
  have triv : ({xa, xb, ya, yb} : set E) = {xa, ya, xb, yb} := by simp only [set.insert_comm],
  rw [convex_join_segments, triv, ←convex_join_segments],
  exact convex_join_mono (hs hxa hya) (ht hxb hyb),
end

protected lemma convex.convex_hull_union (hs : convex 𝕜 s) (ht : convex 𝕜 t) (hs₀ : s.nonempty)
  (ht₀ : t.nonempty) :
  convex_hull 𝕜 (s ∪ t) = convex_join 𝕜 s t :=
(convex_hull_min (union_subset (subset_convex_join_left ht₀) $ subset_convex_join_right hs₀) $
  hs.convex_join ht).antisymm $ convex_join_subset_convex_hull _ _

lemma convex_hull_union (hs : s.nonempty) (ht : t.nonempty) :
  convex_hull 𝕜 (s ∪ t) = convex_join 𝕜 (convex_hull 𝕜 s) (convex_hull 𝕜 t) :=
begin
  rw [←convex_hull_convex_hull_union_left, ←convex_hull_convex_hull_union_right],
  exact (convex_convex_hull 𝕜 s).convex_hull_union (convex_convex_hull 𝕜 t)
    hs.convex_hull ht.convex_hull,
end

end linear_ordered_field
