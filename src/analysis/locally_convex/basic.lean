/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo, Bhavik Mehta, Yaël Dillies
-/
import analysis.convex.basic
import analysis.convex.hull
import analysis.normed_space.basic

/-!
# Local convexity

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines absorbent and balanced sets.

An absorbent set is one that "surrounds" the origin. The idea is made precise by requiring that any
point belongs to all large enough scalings of the set. This is the vector world analog of a
topological neighborhood of the origin.

A balanced set is one that is everywhere around the origin. This means that `a • s ⊆ s` for all `a`
of norm less than `1`.

## Main declarations

For a module over a normed ring:
* `absorbs`: A set `s` absorbs a set `t` if all large scalings of `s` contain `t`.
* `absorbent`: A set `s` is absorbent if every point eventually belongs to all large scalings of
  `s`.
* `balanced`: A set `s` is balanced if `a • s ⊆ s` for all `a` of norm less than `1`.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

absorbent, balanced, locally convex, LCTVS
-/

open set
open_locale pointwise topology

variables {𝕜 𝕝 E  : Type*} {ι : Sort*} {κ : ι → Sort*}

section semi_normed_ring
variables [semi_normed_ring 𝕜]

section has_smul
variables (𝕜) [has_smul 𝕜 E]

/-- A set `A` absorbs another set `B` if `B` is contained in all scalings of `A` by elements of
sufficiently large norm. -/
def absorbs (A B : set E) := ∃ r, 0 < r ∧ ∀ a : 𝕜, r ≤ ‖a‖ → B ⊆ a • A

variables {𝕜} {s t u v A B : set E}

@[simp] lemma absorbs_empty {s : set E}: absorbs 𝕜 s (∅ : set E) :=
⟨1, one_pos, λ a ha, set.empty_subset _⟩

lemma absorbs.mono (hs : absorbs 𝕜 s u) (hst : s ⊆ t) (hvu : v ⊆ u) : absorbs 𝕜 t v :=
let ⟨r, hr, h⟩ := hs in ⟨r, hr, λ a ha, hvu.trans $ (h _ ha).trans $ smul_set_mono hst⟩

lemma absorbs.mono_left (hs : absorbs 𝕜 s u) (h : s ⊆ t) : absorbs 𝕜 t u := hs.mono h subset.rfl
lemma absorbs.mono_right (hs : absorbs 𝕜 s u) (h : v ⊆ u) : absorbs 𝕜 s v := hs.mono subset.rfl h

lemma absorbs.union (hu : absorbs 𝕜 s u) (hv : absorbs 𝕜 s v) : absorbs 𝕜 s (u ∪ v) :=
begin
  obtain ⟨a, ha, hu⟩ := hu,
  obtain ⟨b, hb, hv⟩ := hv,
  exact ⟨max a b, lt_max_of_lt_left ha,
    λ c hc, union_subset (hu _ $ le_of_max_le_left hc) (hv _ $ le_of_max_le_right hc)⟩,
end

@[simp] lemma absorbs_union : absorbs 𝕜 s (u ∪ v) ↔ absorbs 𝕜 s u ∧ absorbs 𝕜 s v :=
⟨λ h, ⟨h.mono_right $ subset_union_left _ _, h.mono_right $ subset_union_right _ _⟩,
  λ h, h.1.union h.2⟩

lemma absorbs_Union_finset {ι : Type*} {t : finset ι} {f : ι → set E} :
  absorbs 𝕜 s (⋃ i ∈ t, f i) ↔ ∀ i ∈ t, absorbs 𝕜 s (f i) :=
begin
  classical,
  induction t using finset.induction_on with i t ht hi,
  { simp only [finset.not_mem_empty, set.Union_false, set.Union_empty, absorbs_empty,
      is_empty.forall_iff, implies_true_iff] },
  rw [finset.set_bUnion_insert, absorbs_union, hi],
  split; intro h,
  { refine λ _ hi', (finset.mem_insert.mp hi').elim _ (h.2 _),
    exact (λ hi'', by { rw hi'', exact h.1 }) },
  exact ⟨h i (finset.mem_insert_self i t), λ i' hi', h i' (finset.mem_insert_of_mem hi')⟩,
end

lemma set.finite.absorbs_Union {ι : Type*} {s : set E} {t : set ι} {f : ι → set E} (hi : t.finite) :
  absorbs 𝕜 s (⋃ i ∈ t, f i) ↔ ∀ i ∈ t, absorbs 𝕜 s (f i) :=
begin
  lift t to finset ι using hi,
  simp only [finset.mem_coe],
  exact absorbs_Union_finset,
end

variables (𝕜)

/-- A set is absorbent if it absorbs every singleton. -/
def absorbent (A : set E) := ∀ x, ∃ r, 0 < r ∧ ∀ a : 𝕜, r ≤ ‖a‖ → x ∈ a • A

variables {𝕜}

lemma absorbent.subset (hA : absorbent 𝕜 A) (hAB : A ⊆ B) : absorbent 𝕜 B :=
begin
  refine forall_imp (λ x, _) hA,
  exact Exists.imp (λ r, and.imp_right $ forall₂_imp $ λ a ha hx, set.smul_set_mono hAB hx),
end

lemma absorbent_iff_forall_absorbs_singleton : absorbent 𝕜 A ↔ ∀ x, absorbs 𝕜 A {x} :=
by simp_rw [absorbs, absorbent, singleton_subset_iff]

lemma absorbent.absorbs (hs : absorbent 𝕜 s) {x : E} : absorbs 𝕜 s {x} :=
absorbent_iff_forall_absorbs_singleton.1 hs _

lemma absorbent_iff_nonneg_lt : absorbent 𝕜 A ↔ ∀ x, ∃ r, 0 ≤ r ∧ ∀ ⦃a : 𝕜⦄, r < ‖a‖ → x ∈ a • A :=
forall_congr $ λ x, ⟨λ ⟨r, hr, hx⟩, ⟨r, hr.le, λ a ha, hx a ha.le⟩, λ ⟨r, hr, hx⟩,
  ⟨r + 1, add_pos_of_nonneg_of_pos hr zero_lt_one,
    λ a ha, hx ((lt_add_of_pos_right r zero_lt_one).trans_le ha)⟩⟩

lemma absorbent.absorbs_finite {s : set E} (hs : absorbent 𝕜 s) {v : set E} (hv : v.finite) :
  absorbs 𝕜 s v :=
begin
  rw ←set.bUnion_of_singleton v,
  exact hv.absorbs_Union.mpr (λ _ _, hs.absorbs),
end

variables (𝕜)

/-- A set `A` is balanced if `a • A` is contained in `A` whenever `a` has norm at most `1`. -/
def balanced (A : set E) := ∀ a : 𝕜, ‖a‖ ≤ 1 → a • A ⊆ A

variables {𝕜}

lemma balanced_iff_smul_mem : balanced 𝕜 s ↔ ∀ ⦃a : 𝕜⦄, ‖a‖ ≤ 1 → ∀ ⦃x : E⦄, x ∈ s → a • x ∈ s :=
forall₂_congr $ λ a ha, smul_set_subset_iff

alias balanced_iff_smul_mem ↔ balanced.smul_mem _

@[simp] lemma balanced_empty : balanced 𝕜 (∅ : set E) :=
λ _ _, by { rw smul_set_empty }

@[simp] lemma balanced_univ : balanced 𝕜 (univ : set E) := λ a ha, subset_univ _

lemma balanced.union (hA : balanced 𝕜 A) (hB : balanced 𝕜 B) : balanced 𝕜 (A ∪ B) :=
λ a ha, smul_set_union.subset.trans $ union_subset_union (hA _ ha) $ hB _ ha

lemma balanced.inter (hA : balanced 𝕜 A) (hB : balanced 𝕜 B) : balanced 𝕜 (A ∩ B) :=
λ a ha, smul_set_inter_subset.trans $ inter_subset_inter (hA _ ha) $ hB _ ha

lemma balanced_Union {f : ι → set E} (h : ∀ i, balanced 𝕜 (f i)) : balanced 𝕜 (⋃ i, f i) :=
λ a ha, (smul_set_Union _ _).subset.trans $ Union_mono $ λ _, h _ _ ha

lemma balanced_Union₂ {f : Π i, κ i → set E} (h : ∀ i j, balanced 𝕜 (f i j)) :
  balanced 𝕜 (⋃ i j, f i j) :=
balanced_Union $ λ _, balanced_Union $ h _

lemma balanced_Inter {f : ι → set E} (h : ∀ i, balanced 𝕜 (f i)) : balanced 𝕜 (⋂ i, f i) :=
λ a ha, (smul_set_Inter_subset _ _).trans $ Inter_mono $ λ _, h _ _ ha

lemma balanced_Inter₂ {f : Π i, κ i → set E} (h : ∀ i j, balanced 𝕜 (f i j)) :
  balanced 𝕜 (⋂ i j, f i j) :=
balanced_Inter $ λ _, balanced_Inter $ h _

variables [has_smul 𝕝 E] [smul_comm_class 𝕜 𝕝 E]

lemma balanced.smul (a : 𝕝) (hs : balanced 𝕜 s) : balanced 𝕜 (a • s) :=
λ b hb, (smul_comm _ _ _).subset.trans $ smul_set_mono $ hs _ hb

end has_smul

section module
variables [add_comm_group E] [module 𝕜 E] {s s₁ s₂ t t₁ t₂ : set E}

lemma absorbs.neg : absorbs 𝕜 s t → absorbs 𝕜 (-s) (-t) :=
Exists.imp $ λ r, and.imp_right $ forall₂_imp $ λ _ _ h,
  (neg_subset_neg.2 h).trans (smul_set_neg _ _).superset

lemma balanced.neg : balanced 𝕜 s → balanced 𝕜 (-s) :=
forall₂_imp $ λ _ _ h, (smul_set_neg _ _).subset.trans $ neg_subset_neg.2 h

lemma absorbs.add : absorbs 𝕜 s₁ t₁ → absorbs 𝕜 s₂ t₂ → absorbs 𝕜 (s₁ + s₂) (t₁ + t₂) :=
λ ⟨r₁, hr₁, h₁⟩ ⟨r₂, hr₂, h₂⟩, ⟨max r₁ r₂, lt_max_of_lt_left hr₁, λ a ha, (add_subset_add
  (h₁ _ $ le_of_max_le_left ha) $ h₂ _ $ le_of_max_le_right ha).trans (smul_add _ _ _).superset⟩

lemma balanced.add (hs : balanced 𝕜 s) (ht : balanced 𝕜 t) : balanced 𝕜 (s + t) :=
λ a ha, (smul_add _ _ _).subset.trans $ add_subset_add (hs _ ha) $ ht _ ha

lemma absorbs.sub (h₁ : absorbs 𝕜 s₁ t₁) (h₂ : absorbs 𝕜 s₂ t₂) : absorbs 𝕜 (s₁ - s₂) (t₁ - t₂) :=
by { simp_rw sub_eq_add_neg, exact h₁.add h₂.neg }

lemma balanced.sub (hs : balanced 𝕜 s) (ht : balanced 𝕜 t) : balanced 𝕜 (s - t) :=
by { simp_rw sub_eq_add_neg, exact hs.add ht.neg }

lemma balanced_zero : balanced 𝕜 (0 : set E) := λ a ha, (smul_zero _).subset

end module
end semi_normed_ring

section normed_field
variables [normed_field 𝕜] [normed_ring 𝕝] [normed_space 𝕜 𝕝] [add_comm_group E] [module 𝕜 E]
  [smul_with_zero 𝕝 E] [is_scalar_tower 𝕜 𝕝 E] {s t u v A B : set E} {x : E} {a b : 𝕜}

/-- Scalar multiplication (by possibly different types) of a balanced set is monotone. -/
lemma balanced.smul_mono (hs : balanced 𝕝 s) {a : 𝕝} {b : 𝕜} (h : ‖a‖ ≤ ‖b‖) : a • s ⊆ b • s :=
begin
  obtain rfl | hb := eq_or_ne b 0,
  { rw norm_zero at h,
    rw norm_eq_zero.1 (h.antisymm $ norm_nonneg _),
    obtain rfl | h := s.eq_empty_or_nonempty,
    { simp_rw [smul_set_empty] },
    { simp_rw [zero_smul_set h] } },
  rintro _ ⟨x, hx, rfl⟩,
  refine ⟨b⁻¹ • a • x, _, smul_inv_smul₀ hb _⟩,
  rw ←smul_assoc,
  refine hs _ _ (smul_mem_smul_set hx),
  rw [norm_smul, norm_inv, ←div_eq_inv_mul],
  exact div_le_one_of_le h (norm_nonneg _),
end

/-- A balanced set absorbs itself. -/
lemma balanced.absorbs_self (hA : balanced 𝕜 A) : absorbs 𝕜 A A :=
begin
  refine ⟨1, zero_lt_one, λ a ha x hx, _⟩,
  rw mem_smul_set_iff_inv_smul_mem₀ (norm_pos_iff.1 $ zero_lt_one.trans_le ha),
  refine hA a⁻¹ _ (smul_mem_smul_set hx),
  rw norm_inv,
  exact inv_le_one ha,
end

lemma balanced.subset_smul (hA : balanced 𝕜 A) (ha : 1 ≤ ‖a‖) : A ⊆ a • A :=
begin
  refine (subset_set_smul_iff₀ _).2 (hA (a⁻¹) _),
  { rintro rfl,
    rw norm_zero at ha,
    exact zero_lt_one.not_le ha },
  { rw norm_inv,
    exact inv_le_one ha }
end

lemma balanced.smul_eq (hA : balanced 𝕜 A) (ha : ‖a‖ = 1) : a • A = A :=
(hA _ ha.le).antisymm $ hA.subset_smul ha.ge

lemma balanced.mem_smul_iff (hs : balanced 𝕜 s) (h : ‖a‖ = ‖b‖) : a • x ∈ s ↔ b • x ∈ s :=
begin
  obtain rfl | hb := eq_or_ne b 0,
  { rw [norm_zero, norm_eq_zero] at h,
    rw h },
  have ha : a ≠ 0 := norm_ne_zero_iff.1 (ne_of_eq_of_ne h $ norm_ne_zero_iff.2 hb),
  split; intro h'; [rw ←inv_mul_cancel_right₀ ha b, rw ←inv_mul_cancel_right₀ hb a];
  { rw [←smul_eq_mul, smul_assoc],
    refine hs.smul_mem _ h',
    simp [←h, ha] }
end

lemma balanced.neg_mem_iff (hs : balanced 𝕜 s) : -x ∈ s ↔ x ∈ s :=
by convert hs.mem_smul_iff (norm_neg 1); simp only [neg_smul, one_smul]

lemma absorbs.inter (hs : absorbs 𝕜 s u) (ht : absorbs 𝕜 t u) : absorbs 𝕜 (s ∩ t) u :=
begin
  obtain ⟨a, ha, hs⟩ := hs,
  obtain ⟨b, hb, ht⟩ := ht,
  have h : 0 < max a b := lt_max_of_lt_left ha,
  refine ⟨max a b, lt_max_of_lt_left ha, λ c hc, _⟩,
  rw smul_set_inter₀ (norm_pos_iff.1 $ h.trans_le hc),
  exact subset_inter (hs _ $ le_of_max_le_left hc) (ht _ $ le_of_max_le_right hc),
end

@[simp] lemma absorbs_inter : absorbs 𝕜 (s ∩ t) u ↔ absorbs 𝕜 s u ∧ absorbs 𝕜 t u :=
⟨λ h, ⟨h.mono_left $ inter_subset_left _ _, h.mono_left $ inter_subset_right _ _⟩,
  λ h, h.1.inter h.2⟩

lemma absorbent_univ : absorbent 𝕜 (univ : set E) :=
begin
  refine λ x, ⟨1, zero_lt_one, λ a ha, _⟩,
  rw smul_set_univ₀ (norm_pos_iff.1 $ zero_lt_one.trans_le ha),
  exact trivial,
end

variables [topological_space E] [has_continuous_smul 𝕜 E]

/-- Every neighbourhood of the origin is absorbent. -/
lemma absorbent_nhds_zero (hA : A ∈ 𝓝 (0 : E)) : absorbent 𝕜 A :=
begin
  intro x,
  obtain ⟨w, hw₁, hw₂, hw₃⟩ := mem_nhds_iff.mp hA,
  have hc : continuous (λ t : 𝕜, t • x) := continuous_id.smul continuous_const,
  obtain ⟨r, hr₁, hr₂⟩ := metric.is_open_iff.mp (hw₂.preimage hc) 0
    (by rwa [mem_preimage, zero_smul]),
  have hr₃ := inv_pos.mpr (half_pos hr₁),
  refine ⟨(r / 2)⁻¹, hr₃, λ a ha₁, _⟩,
  have ha₂ : 0 < ‖a‖ := hr₃.trans_le ha₁,
  refine (mem_smul_set_iff_inv_smul_mem₀ (norm_pos_iff.mp ha₂) _ _).2 (hw₁ $ hr₂ _),
  rw [metric.mem_ball, dist_zero_right, norm_inv],
  calc ‖a‖⁻¹ ≤ r/2 : (inv_le (half_pos hr₁) ha₂).mp ha₁
  ...       < r : half_lt_self hr₁,
end

/-- The union of `{0}` with the interior of a balanced set is balanced. -/
lemma balanced_zero_union_interior (hA : balanced 𝕜 A) : balanced 𝕜 ((0 : set E) ∪ interior A) :=
begin
  intros a ha,
  obtain rfl | h := eq_or_ne a 0,
  { rw zero_smul_set,
    exacts [subset_union_left _ _, ⟨0, or.inl rfl⟩] },
  { rw [←image_smul, image_union],
    apply union_subset_union,
    { rw [image_zero, smul_zero],
      refl },
    { calc a • interior A ⊆ interior (a • A) : (is_open_map_smul₀ h).image_interior_subset A
                      ... ⊆ interior A       : interior_mono (hA _ ha) } }
end

/-- The interior of a balanced set is balanced if it contains the origin. -/
lemma balanced.interior (hA : balanced 𝕜 A) (h : (0 : E) ∈ interior A) : balanced 𝕜 (interior A) :=
begin
  rw ←union_eq_self_of_subset_left (singleton_subset_iff.2 h),
  exact balanced_zero_union_interior hA,
end

lemma balanced.closure (hA : balanced 𝕜 A) : balanced 𝕜 (closure A) :=
λ a ha,
  (image_closure_subset_closure_image $ continuous_id.const_smul _).trans $ closure_mono $ hA _ ha

end normed_field

section nontrivially_normed_field
variables [nontrivially_normed_field 𝕜] [add_comm_group E] [module 𝕜 E] {s : set E}

lemma absorbs_zero_iff : absorbs 𝕜 s 0 ↔ (0 : E) ∈ s :=
begin
  refine ⟨_, λ h, ⟨1, zero_lt_one, λ a _, zero_subset.2 $ zero_mem_smul_set h⟩⟩,
  rintro ⟨r, hr, h⟩,
  obtain ⟨a, ha⟩ := normed_space.exists_lt_norm 𝕜 𝕜 r,
  have := h _ ha.le,
  rwa [zero_subset, zero_mem_smul_set_iff] at this,
  exact norm_ne_zero_iff.1 (hr.trans ha).ne',
end

lemma absorbent.zero_mem (hs : absorbent 𝕜 s) : (0 : E) ∈ s :=
absorbs_zero_iff.1 $ absorbent_iff_forall_absorbs_singleton.1 hs _

variables [module ℝ E] [smul_comm_class ℝ 𝕜 E]

lemma balanced_convex_hull_of_balanced (hs : balanced 𝕜 s) : balanced 𝕜 (convex_hull ℝ s) :=
begin
  suffices : convex ℝ {x | ∀ a : 𝕜, ‖a‖ ≤ 1 → a • x ∈ convex_hull ℝ s},
  { rw balanced_iff_smul_mem at hs ⊢,
    refine λ a ha x hx, convex_hull_min _ this hx a ha,
    exact λ y hy a ha, subset_convex_hull ℝ s (hs ha hy) },
  intros x hx y hy u v hu hv huv a ha,
  simp only [smul_add, ← smul_comm],
  exact convex_convex_hull ℝ s (hx a ha) (hy a ha) hu hv huv
end

end nontrivially_normed_field

section real
variables [add_comm_group E] [module ℝ E] {s : set E}

lemma balanced_iff_neg_mem (hs : convex ℝ s) : balanced ℝ s ↔ ∀ ⦃x⦄, x ∈ s → -x ∈ s :=
begin
  refine ⟨λ h x, h.neg_mem_iff.2, λ h a ha, smul_set_subset_iff.2 $ λ x hx, _⟩,
  rw [real.norm_eq_abs, abs_le] at ha,
  rw [show a = -((1 - a) / 2) + (a - -1)/2, by ring, add_smul, neg_smul, ←smul_neg],
  exact hs (h hx) hx (div_nonneg (sub_nonneg_of_le ha.2) zero_le_two)
    (div_nonneg (sub_nonneg_of_le ha.1) zero_le_two) (by ring),
end

end real
