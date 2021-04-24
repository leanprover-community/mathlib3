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
def is_extreme_set (A B : set E) :
  Prop :=
B ⊆ A ∧ ∀ x₁ x₂ ∈ A, ∀ x ∈ B, x ∈ segment x₁ x₂ → x₁ ≠ x → x₂ ≠ x → x₁ ∈ B ∧ x₂ ∈ B

lemma is_extreme_set.refl :
  reflexive (is_extreme_set : set E → set E → Prop) :=
λ A, ⟨subset.refl _, λ x₁ x₂ hx₁A hx₂A x hxA hx hxx₁ hxx₂, ⟨hx₁A, hx₂A⟩⟩

lemma is_extreme_set.trans :
  transitive (is_extreme_set : set E → set E → Prop) :=
begin
  rintro A B C ⟨hBA, hAB⟩ ⟨hCB, hBC⟩,
  use subset.trans hCB hBA,
  rintro x₁ x₂ hx₁A hx₂A x hxC hx hxx₁ hxx₂,
  obtain ⟨hx₁B, hx₂B⟩ := hAB x₁ x₂ hx₁A hx₂A x (hCB hxC) hx hxx₁ hxx₂,
  exact hBC x₁ x₂ hx₁B hx₂B x hxC hx hxx₁ hxx₂,
end

lemma is_extreme_set.antisymm :
  anti_symmetric (is_extreme_set : set E → set E → Prop) :=
λ A B hAB hBA, subset.antisymm hBA.1 hAB.1

instance : is_partial_order (set E) is_extreme_set :=
{ refl := is_extreme_set.refl,
  trans := is_extreme_set.trans,
  antisymm := is_extreme_set.antisymm }

lemma convex_diff_of_extreme (hA : convex A) (hAB : is_extreme_set A B) :
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

/--
x is an extreme point to A iff {x} is an extreme set of A.
-/
lemma extreme_point_iff_extreme_singleton :
  x ∈ A.extreme_points ↔ is_extreme_set A {x} :=
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

lemma inter_extreme_of_extreme (hAB : is_extreme_set A B) (hAC : is_extreme_set A C) :
  is_extreme_set A (B ∩ C) :=
begin
  use subset.trans (inter_subset_left _ _) hAB.1,
  rintro x₁ x₂ hx₁A hx₂A x ⟨hxB, hxC⟩ hx hxx₁ hxx₂,
  obtain ⟨hx₁B, hx₂B⟩ := hAB.2 x₁ x₂ hx₁A hx₂A x hxB hx hxx₁ hxx₂,
  obtain ⟨hx₁C, hx₂C⟩ := hAC.2 x₁ x₂ hx₁A hx₂A x hxC hx hxx₁ hxx₂,
  exact ⟨⟨hx₁B, hx₁C⟩, hx₂B, hx₂C⟩,
end

lemma bInter_extreme_of_extreme {F : set (set E)} (hF : F.nonempty)
  (hAF : ∀ B ∈ F, is_extreme_set A B) :
  is_extreme_set A (⋂ B ∈ F, B) :=
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
  (hAF : ∀ B ∈ F, is_extreme_set A B) :
  is_extreme_set A (⋂₀ F) :=
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
  (hAF : ∀ i : ι, is_extreme_set A (F i)) :
  is_extreme_set A (⋂ i : ι, F i) :=
begin
  obtain i := classical.arbitrary ι,
  use Inter_subset_of_subset i (hAF i).1,
  rintro x₁ x₂ hx₁A hx₂A x hxF hx hxx₁ hxx₂,
  rw mem_Inter at ⊢ hxF,
  rw mem_Inter,
  have h := λ i, (hAF i).2 x₁ x₂ hx₁A hx₂A x (hxF i) hx hxx₁ hxx₂,
  exact ⟨λ i, (h i).1, λ i, (h i).2⟩,
end

lemma extreme_mono (hAC : is_extreme_set A C) (hBA : B ⊆ A) (hCB : C ⊆ B) :
  is_extreme_set B C :=
⟨hCB, λ x₁ x₂ hx₁B hx₂B x hxC hx hxx₁ hxx₂, hAC.2 x₁ x₂ (hBA hx₁B) (hBA hx₂B) x hxC hx hxx₁ hxx₂⟩

lemma extreme_points_eq_inter_extreme_points_of_extreme (hAB : is_extreme_set A B) :
  B.extreme_points = B ∩ A.extreme_points :=
begin
  ext x,
  exact ⟨λ hxB, ⟨hxB.1, extreme_point_iff_extreme_singleton.2 (is_extreme_set.trans hAB
  (extreme_point_iff_extreme_singleton.1 hxB))⟩, λ ⟨hxB, hxA⟩, ⟨hxB, λ x₁ x₂ hx₁B hx₂B hx,
    hxA.2 x₁ x₂ (hAB.1 hx₁B) (hAB.1 hx₂B) hx⟩⟩,
end

lemma extreme_points_subset_extreme_points_of_extreme (hAB : is_extreme_set A B) :
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

/-- TODO: generalise to convex independence and make it an iff.-/
lemma extreme_to_convex_hull_of_affine_independent {s : finset E} (hx : x ∈ s)
  (hs : affine_independent ℝ (λ p, p : (s : set E) → E)) :
  x ∈ (convex_hull ↑s : set E).extreme_points :=
begin
  refine ⟨subset_convex_hull _ hx, _⟩,
  rintro y y' hy hy' t,
  rw finset.convex_hull_eq at hy hy',
  obtain ⟨w, hw₀, hw₁, hy⟩ := hy,
  obtain ⟨w', hw'₀, hw'₁, hy'⟩ := hy',
  rw segment_eq_image at t,
  obtain ⟨θ, hθ₁, hθ₂ : _ + _ = _⟩ := t,
  rw finset.center_mass_eq_of_sum_1 _ _ hw₁ at hy,
  rw finset.center_mass_eq_of_sum_1 _ _ hw'₁ at hy',
  change s.sum (λ i, w i • i) = y at hy,
  change s.sum (λ i, w' i • i) = y' at hy',
  let w'' : E → ℝ := λ t, (1 - θ) * w t + θ * w' t - if t = x then 1 else 0,
  have hw''₁ : s.sum w'' = 0,
  { rw [finset.sum_sub_distrib, finset.sum_add_distrib, ← finset.mul_sum, ← finset.mul_sum, hw₁,
      hw'₁, finset.sum_ite_eq' s, if_pos hx],
    simp },
  have hw''₂ : s.sum (λ i, w'' i • i) = 0,
  { simp only [sub_smul, add_smul, finset.sum_add_distrib, finset.sum_sub_distrib],
    simp only [mul_smul, ←finset.smul_sum, hy, hy'],
    simp only [ite_smul, zero_smul, one_smul, finset.sum_ite_eq', if_pos hx, hθ₂, sub_self] },
  by_contra t,
  push_neg at t,
  suffices hw''₃ : ∀ q ∈ s, w'' q = 0,
  { have : θ = 0 ∨ θ = 1,
    { by_contra hθ,
      push_neg at hθ,
      have : 0 < θ ∧ 0 < 1 - θ,
      { split,
        { apply lt_of_le_of_ne hθ₁.1 hθ.1.symm },
        { rw sub_pos,
          apply lt_of_le_of_ne hθ₁.2 hθ.2 } },
      have both_zero : ∀ q ∈ s, q ≠ x → w q = 0,
      { intros q hq₁ hq₂,
        specialize hw''₃ q hq₁,
        change _ + _ = _ at hw''₃,
        rw if_neg hq₂ at hw''₃,
        simp only [add_zero, neg_zero] at hw''₃,
        rw add_eq_zero_iff'
            (mul_nonneg (le_of_lt this.2) (hw₀ q hq₁))
            (mul_nonneg (le_of_lt this.1) (hw'₀ q hq₁)) at hw''₃,
        rw mul_eq_zero at hw''₃,
        apply or.resolve_left hw''₃.1 (ne_of_gt this.2) },
      have : (1 - θ) * w x + θ * w' x = 1,
      { specialize hw''₃ _ hx,
        change (1 - θ) * w x + θ * w' x - ite _ _ _ = 0 at hw''₃,
        rwa [if_pos rfl, sub_eq_zero] at hw''₃ },
      rw finset.sum_eq_single x at hw₁,
      { rw finset.sum_eq_single x at hy,
        { rw hw₁ at hy,
          apply t.1,
          rw ←hy,
          simp },
        { rintro q hq₁ hq₂,
          rw both_zero q hq₁ hq₂,
          simp },
        { exact λ t, (t hx).elim } },
      { intros q hq₁ hq₂,
        apply both_zero q hq₁ hq₂ },
      { exact λ t, (t hx).elim } },
    rcases this with (rfl | rfl),
    { simp only [add_zero, one_smul, sub_zero, zero_smul] at hθ₂,
      apply t.1 hθ₂ },
    { simp only [one_smul, zero_smul, zero_add, sub_self] at hθ₂,
      apply t.2 hθ₂ } },
  rw affine_independent_iff_of_fintype at hs,
  let w''' : (s : set E) → ℝ := λ t, w'' (t : E),
  have hw''' : finset.univ.sum w''' = 0,
  { rw finset.sum_finset_coe,
    apply hw''₁ },
  specialize hs w''' hw''' _,
  { rw finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ _ _ hw''' (0 : E),
    rw finset.weighted_vsub_of_point_apply,
    simp only [vsub_eq_sub, sub_zero],
    rw finset.sum_finset_coe (λ i, w'' i • i),
    apply hw''₂ },
  rintro q hq,
  exact hs ⟨q, hq⟩,
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
