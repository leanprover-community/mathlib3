/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import linear_algebra.affine_space.independent
import algebra.big_operators.basic
import analysis.convex.topology

/-!
# Extreme sets

This file defines extreme sets and extreme points for set in a real normed space.

## References

See chapter 8 of [Convexity][simon2011]

TODO:
- add exposed sets to this file.
- define convex independence and prove lemmas related to extreme points.
-/

open_locale classical affine
open set

variables {E : Type*} [add_comm_group E] [vector_space ℝ E] {x : E} {A B C : set E}

/--
A set B is extreme to a set A if B ⊆ A and all points of B only belong to (intrinsic) interiors of
segments whose ends are in B.
-/
def is_extreme (A B : set E) :
  Prop :=
B ⊆ A ∧ ∀ x₁ x₂ ∈ A, ∀ x ∈ B, x ∈ segment x₁ x₂ → x₁ ≠ x → x₂ ≠ x → x₁ ∈ B ∧ x₂ ∈ B

lemma is_extreme.refl :
  reflexive (is_extreme : set E → set E → Prop) :=
λ A, ⟨subset.refl _, λ x₁ x₂ hx₁A hx₂A x hxA hx hxx₁ hxx₂, ⟨hx₁A, hx₂A⟩⟩

lemma is_extreme.trans :
  transitive (is_extreme : set E → set E → Prop) :=
begin
  rintro A B C ⟨hBA, hAB⟩ ⟨hCB, hBC⟩,
  use subset.trans hCB hBA,
  rintro x₁ x₂ hx₁A hx₂A x hxC hx hxx₁ hxx₂,
  obtain ⟨hx₁B, hx₂B⟩ := hAB x₁ x₂ hx₁A hx₂A x (hCB hxC) hx hxx₁ hxx₂,
  exact hBC x₁ x₂ hx₁B hx₂B x hxC hx hxx₁ hxx₂,
end

lemma is_extreme.antisymm :
  anti_symmetric (is_extreme : set E → set E → Prop) :=
λ A B hAB hBA, subset.antisymm hBA.1 hAB.1

instance : is_partial_order (set E) is_extreme :=
{ refl := is_extreme.refl,
  trans := is_extreme.trans,
  antisymm := is_extreme.antisymm }

lemma convex_diff_of_extreme (hA : convex A) (hAB : is_extreme A B) :
  convex (A \ B) :=
begin
  rw convex_iff_segment_subset,
  rintro x₁ x₂ ⟨hx₁A, hx₁B⟩ ⟨hx₂A, hx₂B⟩ x hx,
  refine ⟨hA.segment_subset hx₁A hx₂A hx, λ hxB, hx₁B (hAB.2 x₁ x₂ hx₁A hx₂A x hxB hx _ _).1⟩,
  { rintro rfl,
    exact hx₁B hxB },
  { rintro rfl,
    exact hx₂B hxB }
end

/--
A point x is an extreme point of a set A if x belongs to no (intrinsic) interior of a segment with
ends in A.
-/
def set.extreme_points (A : set E) :
  set E :=
{x ∈ A | ∀ (x₁ x₂ ∈ A), x ∈ segment x₁ x₂ → x₁ = x ∨ x₂ = x}

lemma extreme_point_def :
  x ∈ A.extreme_points ↔ x ∈ A ∧ ∀ (x₁ x₂ ∈ A), x ∈ segment x₁ x₂ → x₁ = x ∨ x₂ = x :=
by refl

/--x is an extreme point to A iff {x} is an extreme set of A.-/
lemma extreme_point_iff_extreme_singleton :
  x ∈ A.extreme_points ↔ is_extreme A {x} :=
begin
  split,
  { rintro ⟨hxA, hx⟩,
    use singleton_subset_iff.2 hxA,
    rintro x₁ x₂ hx₁A hx₂A y (rfl : y = x) hxs hx₁ hx₂,
    exfalso,
    cases hx x₁ x₂ hx₁A hx₂A hxs,
    exacts [hx₁ h, hx₂ h] },
  { rintro hx,
    use singleton_subset_iff.1 hx.1,
    rintro x₁ x₂ hx₁ hx₂ hxs,
    by_contra,
    push_neg at h,
    exact h.1 (hx.2 x₁ x₂ hx₁ hx₂ x rfl hxs h.1 h.2).1 }
end

lemma extreme_points_subset :
  A.extreme_points ⊆ A :=
λ x hx, hx.1

@[simp]
lemma extreme_points_empty :
  (∅ : set E).extreme_points = ∅ :=
subset_empty_iff.1 extreme_points_subset

@[simp]
lemma extreme_points_singleton :
  ({x} : set E).extreme_points = {x} :=
begin
  refine subset.antisymm extreme_points_subset (singleton_subset_iff.2 ⟨mem_singleton x,
  λ x₁ _ hx₁ _ _, _⟩),
  left,
  exact hx₁,
end

lemma inter_extreme_of_extreme (hAB : is_extreme A B) (hAC : is_extreme A C) :
  is_extreme A (B ∩ C) :=
begin
  use subset.trans (inter_subset_left _ _) hAB.1,
  rintro x₁ x₂ hx₁A hx₂A x ⟨hxB, hxC⟩ hx hxx₁ hxx₂,
  obtain ⟨hx₁B, hx₂B⟩ := hAB.2 x₁ x₂ hx₁A hx₂A x hxB hx hxx₁ hxx₂,
  obtain ⟨hx₁C, hx₂C⟩ := hAC.2 x₁ x₂ hx₁A hx₂A x hxC hx hxx₁ hxx₂,
  exact ⟨⟨hx₁B, hx₁C⟩, hx₂B, hx₂C⟩,
end

lemma bInter_extreme_of_extreme {F : set (set E)} (hF : F.nonempty)
  (hAF : ∀ B ∈ F, is_extreme A B) :
  is_extreme A (⋂ B ∈ F, B) :=
begin
  obtain ⟨B, hB⟩ := hF,
  use subset.trans (bInter_subset_of_mem hB) (hAF B hB).1,
  rintro x₁ x₂ hx₁A hx₂A x hxF hx hxx₁ hxx₂,
  rw mem_bInter_iff at ⊢ hxF,
  rw mem_bInter_iff,
  have h := λ B hB, (hAF B hB).2 x₁ x₂ hx₁A hx₂A x (hxF B hB) hx hxx₁ hxx₂,
  exact ⟨λ B hB, (h B hB).1, λ B hB, (h B hB).2⟩,
end

lemma sInter_extreme_of_extreme {F : set (set E)} (hF : F.nonempty)
  (hAF : ∀ B ∈ F, is_extreme A B) :
  is_extreme A (⋂₀ F) :=
begin
  obtain ⟨B, hB⟩ := hF,
  use subset.trans (sInter_subset_of_mem hB) (hAF B hB).1,
  rintro x₁ x₂ hx₁A hx₂A x hxF hx hxx₁ hxx₂,
  rw mem_sInter at ⊢ hxF,
  rw mem_sInter,
  have h := λ B hB, (hAF B hB).2 x₁ x₂ hx₁A hx₂A x (hxF B hB) hx hxx₁ hxx₂,
  exact ⟨λ B hB, (h B hB).1, λ B hB, (h B hB).2⟩,
end

lemma Inter_extreme_of_extreme {ι : Type*} [nonempty ι] {F : ι → set E}
  (hAF : ∀ i : ι, is_extreme A (F i)) :
  is_extreme A (⋂ i : ι, F i) :=
begin
  obtain i := classical.arbitrary ι,
  use Inter_subset_of_subset i (hAF i).1,
  rintro x₁ x₂ hx₁A hx₂A x hxF hx hxx₁ hxx₂,
  rw mem_Inter at ⊢ hxF,
  rw mem_Inter,
  have h := λ i, (hAF i).2 x₁ x₂ hx₁A hx₂A x (hxF i) hx hxx₁ hxx₂,
  exact ⟨λ i, (h i).1, λ i, (h i).2⟩,
end

lemma extreme_mono (hAC : is_extreme A C) (hBA : B ⊆ A) (hCB : C ⊆ B) :
  is_extreme B C :=
⟨hCB, λ x₁ x₂ hx₁B hx₂B x hxC hx hxx₁ hxx₂, hAC.2 x₁ x₂ (hBA hx₁B) (hBA hx₂B) x hxC hx hxx₁ hxx₂⟩

lemma extreme_points_eq_inter_extreme_points_of_extreme (hAB : is_extreme A B) :
  B.extreme_points = B ∩ A.extreme_points :=
begin
  ext x,
  exact ⟨λ hxB, ⟨hxB.1, extreme_point_iff_extreme_singleton.2 (is_extreme.trans hAB
  (extreme_point_iff_extreme_singleton.1 hxB))⟩, λ ⟨hxB, hxA⟩, ⟨hxB, λ x₁ x₂ hx₁B hx₂B hx,
    hxA.2 x₁ x₂ (hAB.1 hx₁B) (hAB.1 hx₂B) hx⟩⟩,
end

lemma extreme_points_subset_extreme_points_of_extreme (hAB : is_extreme A B) :
  B.extreme_points ⊆ A.extreme_points :=
begin
  rw extreme_points_eq_inter_extreme_points_of_extreme hAB,
  exact inter_subset_right _ _,
end

lemma convex_remove_iff_extreme_point (hA : convex A) :
  x ∈ A ∧ convex (A \ {x}) ↔ x ∈ A.extreme_points :=
begin
  split,
  { rintro ⟨hxA, hAx⟩,
    use hxA,
    rintro x₁ x₂ hx₁A hx₂A hx,
    by_contra,
    push_neg at h,
    rw convex_iff_segment_subset at hAx,
    exact (hAx ⟨hx₁A, λ hx₁, h.1 (mem_singleton_iff.2 hx₁)⟩
      ⟨hx₂A, λ hx₂, h.2 (mem_singleton_iff.2 hx₂)⟩ hx).2 rfl },
  exact λ hx, ⟨hx.1, convex_diff_of_extreme hA (extreme_point_iff_extreme_singleton.1 hx)⟩,
end

lemma convex_hull_extreme_points_subset :
  (convex_hull A).extreme_points ⊆ A :=
begin
  rintro x hx,
  by_contra,
  rw ←convex_remove_iff_extreme_point (convex_convex_hull _) at hx,
  exact (convex_hull_min (subset_diff.2 ⟨subset_convex_hull _, disjoint_singleton_right.2 h⟩) hx.2
    hx.1).2 rfl,
end
