/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.convex.extreme

/-!
# Exposed sets

This file defines exposed sets and exposed points for sets in a real vector space.

An exposed set of `A` is a subset of `A` that maximizes a functional (a continuous linear map
`E → ℝ`) over `A`. By convention, `∅` is exposed to all sets.
This is an analytic notion of "being on the side of". It is stronger than being extreme (see
`is_exposed.is_extreme`), but weaker (for exposed points) than being a vertex.

An exposed set of `A` is sometimes called a "face of `A`", but we decided to reserve this
terminology to the more specific notion of a face of a polytope (sometimes hopefully soon out
on mathlib!).

## Main declarations

* `is_exposed A B`: States that `B` is exposed with respect to `A`.
* `is_exposed.is_extreme`: An exposed set is also extreme.

## References

See chapter 8 of [*Barry Simon*, Convexity][simon2011]

TODO:
- define convex independence, intrinsic frontier and prove lemmas related to exposed sets and
  points.
- generalise to Locally Convex Topological Vector Spaces.
More not-yet-PRed stuff is available on the branch `sperner_again`.
-/

open_locale classical affine big_operators
open set

variables {E : Type*} [normed_group E] [normed_space ℝ E] {x : E} {A B C : set E}
  {X : finset E} {l : E →L[ℝ] ℝ}

/-- A set is exposed with respect to `A` iff it maximizes some functional over `A`. -/
def is_exposed (A B : set E) : Prop :=
B.nonempty → ∃ l : E →L[ℝ] ℝ, B = {x ∈ A | ∀ y ∈ A, l y ≤ l x}


/-- A useful way to build exposed sets from intersecting `A` with halfspaces. -/
def continuous_linear_map.to_exposed (l : E →L[ℝ] ℝ) (A : set E) : set E :=
{x ∈ A | ∀ y ∈ A, l y ≤ l x}

lemma continuous_linear_map.to_exposed.is_exposed : is_exposed A (l.to_exposed A) := λ h, ⟨l, rfl⟩

lemma is_exposed_empty : is_exposed A ∅ :=
λ ⟨x, hx⟩, by { exfalso, exact hx }

namespace is_exposed

protected lemma subset (hAB : is_exposed A B) : B ⊆ A :=
begin
  rintro x hx,
  obtain ⟨_, rfl⟩ := hAB ⟨x, hx⟩,
  exact hx.1,
end

@[refl] lemma refl (A : set E) : is_exposed A A :=
λ ⟨w, hw⟩, ⟨0, subset.antisymm (λ x hx, ⟨hx, λ y hy, by exact le_refl 0⟩) (λ x hx, hx.1)⟩

lemma antisymm (hB : is_exposed A B) (hA : is_exposed B A) :
  A = B :=
hA.subset.antisymm hB.subset

-- `is_exposed` is *not* transitive

protected lemma mono (hC : is_exposed A C) (hBA : B ⊆ A) (hCB : C ⊆ B) :
  is_exposed B C :=
begin
  rintro ⟨w, hw⟩,
  obtain ⟨l, rfl⟩ := hC ⟨w, hw⟩,
  exact ⟨l, subset.antisymm (λ x hx, ⟨hCB hx, λ y hy, hx.2 y (hBA hy)⟩)
    (λ x hx, ⟨hBA hx.1, λ y hy, (hw.2 y hy).trans (hx.2 w (hCB hw))⟩)⟩,
end

lemma inter (hB : is_exposed A B) (hC : is_exposed A C) :
  is_exposed A (B ∩ C) :=
begin
  rintro ⟨x, hxB, hxC⟩,
  obtain ⟨l₁, rfl⟩ := hB ⟨x, hxB⟩,
  obtain ⟨l₂, rfl⟩ := hC ⟨x, hxC⟩,
  refine ⟨l₁ + l₂, subset.antisymm _ _⟩,
  { rintro y ⟨⟨hyA, hyB⟩, ⟨_, hyC⟩⟩,
    exact ⟨hyA, λ z hz, add_le_add (hyB z hz) (hyC z hz)⟩ },
  rintro y ⟨hyA, hy⟩,
  refine ⟨⟨hyA, λ z hz, _⟩, hyA, λ z hz, _⟩,
  { exact (add_le_add_iff_right (l₂ y)).1 (le_trans (add_le_add (hxB.2 z hz) (hxC.2 y hyA))
      (hy x hxB.1)) },
  exact (add_le_add_iff_left (l₁ y)).1 (le_trans (add_le_add (hxB.2 y hyA) (hxC.2 z hz))
    (hy x hxB.1)),
end

lemma sInter {F : finset (set E)} (hF : F.nonempty)
  (hAF : ∀ B ∈ F, is_exposed A B) :
  is_exposed A (⋂₀ F) :=
begin
  revert hF F,
  refine finset.induction _ _,
  { rintro h,
    exfalso,
    exact empty_not_nonempty h },
  rintro C F _ hF _ hCF,
  rw [finset.coe_insert, sInter_insert],
  obtain rfl | hFnemp := F.eq_empty_or_nonempty,
  { rw [finset.coe_empty, sInter_empty, inter_univ],
    exact hCF C (finset.mem_singleton_self C) },
  exact (hCF C (finset.mem_insert_self C F)).inter (hF hFnemp (λ B hB,
    hCF B(finset.mem_insert_of_mem hB))),
end

lemma inter_left (hC : is_exposed A C) (hCB : C ⊆ B) :
  is_exposed (A ∩ B) C :=
begin
  rintro ⟨w, hw⟩,
  obtain ⟨l, rfl⟩ := hC ⟨w, hw⟩,
  exact ⟨l, subset.antisymm (λ x hx, ⟨⟨hx.1, hCB hx⟩, λ y hy, hx.2 y hy.1⟩)
    (λ x ⟨⟨hxC, _⟩, hx⟩, ⟨hxC, λ y hy, (hw.2 y hy).trans (hx w ⟨hC.subset hw, hCB hw⟩)⟩)⟩,
end

lemma inter_right (hC : is_exposed B C) (hCA : C ⊆ A) :
  is_exposed (A ∩ B) C :=
begin
  rw inter_comm,
  exact hC.inter_left hCA,
end

lemma eq_inter_halfspace (hAB : is_exposed A B) :
  ∃ l : E →L[ℝ] ℝ, ∃ a, B = {x ∈ A | a ≤ l x} :=
begin
  obtain hB | hB := B.eq_empty_or_nonempty,
  { refine ⟨0, 1, _⟩,
    rw [hB, eq_comm, eq_empty_iff_forall_not_mem],
    rintro x ⟨-, h⟩,
    rw continuous_linear_map.zero_apply at h,
    linarith },
  obtain ⟨l, rfl⟩ := hAB hB,
  obtain ⟨w, hw⟩ := hB,
  exact ⟨l, l w, subset.antisymm (λ x hx, ⟨hx.1, hx.2 w hw.1⟩)
    (λ x hx, ⟨hx.1, λ y hy, (hw.2 y hy).trans hx.2⟩)⟩,
end

protected lemma is_extreme (hAB : is_exposed A B) :
  is_extreme A B :=
begin
  use hAB.subset,
  rintro x₁ x₂ hx₁A hx₂A x hxB ⟨a, b, ha, hb, hab, hx⟩,
  obtain ⟨l, rfl⟩ := hAB ⟨x, hxB⟩,
  have hl : convex_on univ l := sorry,
  have hlx₁ : l x₁ = l x,
  { apply (hxB.2 x₁ hx₁A).antisymm,
    rw [←@smul_le_smul_iff_of_pos ℝ ℝ _ _ _ _ _ _ _ ha, ←add_le_add_iff_right (b • l x), ←add_smul,
      hab, one_smul],
    nth_rewrite 0 ←hx,
    rw [l.map_add, l.map_smul, l.map_smul, add_le_add_iff_left,
      @smul_le_smul_iff_of_pos ℝ ℝ _ _ _ _ _ _ _ hb],
    exact hxB.2 x₂ hx₂A },
  have hlx₂ : l x₂ = l x,
  { apply (hxB.2 x₂ hx₂A).antisymm,
    rw [←@smul_le_smul_iff_of_pos ℝ ℝ _ _ _ _ _ _ _ hb, ←add_le_add_iff_left (a • l x), ←add_smul,
      hab, one_smul],
    nth_rewrite 0 ←hx,
    rw [l.map_add, l.map_smul, l.map_smul, add_le_add_iff_right,
    @smul_le_smul_iff_of_pos ℝ ℝ _ _ _ _ _ _ _ ha],
    exact hxB.2 x₁ hx₁A },
  refine ⟨⟨hx₁A, λ y hy, _⟩, ⟨hx₂A, λ y hy, _⟩⟩,
  { rw hlx₁,
    exact hxB.2 y hy },
  rw hlx₂,
  exact hxB.2 y hy,
end

protected lemma is_convex (hAB : is_exposed A B) (hA : convex A) :
  convex B :=
begin
  cases B.eq_empty_or_nonempty,
  { rw h,
    exact convex_empty },
  have hBA := hAB.subset,
  obtain ⟨l, rfl⟩ := hAB h,
  rw convex_iff_segment_subset at ⊢ hA,
  rintro x₁ x₂ ⟨hx₁A, hx₁⟩ ⟨hx₂A, hx₂⟩ x hx,
  use hA hx₁A hx₂A hx,
  obtain ⟨a, b, ha, hb, hab, hx⟩ := hx,
  rintro y hyA,
  calc
    l y = a • l y + b • l y : by rw [←add_smul, hab, one_smul]
    ... ≤ a • l x₁ + b • l x₂ : add_le_add (mul_le_mul_of_nonneg_left (hx₁ y hyA) ha)
                                           (mul_le_mul_of_nonneg_left (hx₂ y hyA) hb)
    ... = l x : by rw [←hx, l.map_add, l.map_smul, l.map_smul],
end

lemma is_closed (hAB : is_exposed A B) (hA : is_closed A) :
  is_closed B :=
begin
  obtain ⟨l, a, rfl⟩ := hAB.eq_inter_halfspace,
  exact hA.is_closed_le continuous_on_const l.continuous.continuous_on,
end

lemma is_compact (hAB : is_exposed A B) (hA : is_compact A) :
  is_compact B :=
compact_of_is_closed_subset hA (hAB.is_closed hA.is_closed) hAB.subset

end is_exposed

/-- A point is exposed with respect to `A` iff there exists an hyperplane whose intersection with
`A` is exactly that point. -/
def set.exposed_points (A : set E) :
  set E :=
{x ∈ A | ∃ l : E →L[ℝ] ℝ, ∀ y ∈ A, l y ≤ l x ∧ (l x ≤ l y → y = x)}

lemma exposed_point_def :
  x ∈ A.exposed_points ↔ x ∈ A ∧ ∃ l : E →L[ℝ] ℝ, ∀ y ∈ A, l y ≤ l x ∧ (l x ≤ l y → y = x) :=
iff.rfl

/-- Exposed points exactly correspond to exposed singletons. -/
lemma mem_exposed_points_iff_exposed_singleton :
  x ∈ A.exposed_points ↔ is_exposed A {x} :=
begin
  use λ ⟨hxA, l, hl⟩ h, ⟨l, eq.symm $ eq_singleton_iff_unique_mem.2 ⟨⟨hxA, λ y hy, (hl y hy).1⟩,
    λ z hz, (hl z hz.1).2 (hz.2 x hxA)⟩⟩,
  rintro h,
  obtain ⟨l, hl⟩ := h ⟨x, mem_singleton _⟩,
  rw [eq_comm, eq_singleton_iff_unique_mem] at hl,
  exact ⟨hl.1.1, l, λ y hy, ⟨hl.1.2 y hy, λ hxy, hl.2 y ⟨hy, λ z hz, (hl.1.2 z hz).trans hxy⟩⟩⟩,
end

lemma exposed_points_subset :
  A.exposed_points ⊆ A :=
λ x hx, hx.1

lemma exposed_points_subset_extreme_points :
  A.exposed_points ⊆ A.extreme_points :=
λ x hx, mem_extreme_points_iff_extreme_singleton.2
  (mem_exposed_points_iff_exposed_singleton.1 hx).is_extreme

@[simp]
lemma exposed_points_empty :
  (∅ : set E).exposed_points = ∅ :=
subset_empty_iff.1 exposed_points_subset
