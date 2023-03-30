/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.convex.hull

/-!
# Extreme sets

This file defines extreme sets and extreme points for sets in a module.

An extreme set of `A` is a subset of `A` that is as far as it can get in any outward direction: If
point `x` is in it and point `y ∈ A`, then the line passing through `x` and `y` leaves `A` at `x`.
This is an analytic notion of "being on the side of". It is weaker than being exposed (see
`is_exposed.is_extreme`).

## Main declarations

* `is_extreme 𝕜 A B`: States that `B` is an extreme set of `A` (in the literature, `A` is often
  implicit).
* `set.extreme_points 𝕜 A`: Set of extreme points of `A` (corresponding to extreme singletons).
* `convex.mem_extreme_points_iff_convex_diff`: A useful equivalent condition to being an extreme
  point: `x` is an extreme point iff `A \ {x}` is convex.

## Implementation notes

The exact definition of extremeness has been carefully chosen so as to make as many lemmas
unconditional (in particular, the Krein-Milman theorem doesn't need the set to be convex!).
In practice, `A` is often assumed to be a convex set.

## References

See chapter 8 of [Barry Simon, *Convexity*][simon2011]

## TODO

Prove lemmas relating extreme sets and points to the intrinsic frontier.

More not-yet-PRed stuff is available on the branch `sperner_again`.
-/

open function set
open_locale affine classical

variables {𝕜 E F ι : Type*} {π : ι → Type*}

section has_smul
variables (𝕜) [ordered_semiring 𝕜] [add_comm_monoid E] [has_smul 𝕜 E]

/-- A set `B` is an extreme subset of `A` if `B ⊆ A` and all points of `B` only belong to open
segments whose ends are in `B`. -/
def is_extreme (A B : set E) : Prop :=
B ⊆ A ∧ ∀ ⦃x₁⦄, x₁ ∈ A → ∀ ⦃x₂⦄, x₂ ∈ A → ∀ ⦃x⦄, x ∈ B → x ∈ open_segment 𝕜 x₁ x₂ → x₁ ∈ B ∧ x₂ ∈ B

/-- A point `x` is an extreme point of a set `A` if `x` belongs to no open segment with ends in
`A`, except for the obvious `open_segment x x`. -/
def set.extreme_points (A : set E) : set E :=
{x ∈ A | ∀ ⦃x₁⦄, x₁ ∈ A → ∀ ⦃x₂⦄, x₂ ∈ A → x ∈ open_segment 𝕜 x₁ x₂ → x₁ = x ∧ x₂ = x}

@[refl] protected lemma is_extreme.refl (A : set E) :
  is_extreme 𝕜 A A :=
⟨subset.rfl, λ x₁ hx₁A x₂ hx₂A x hxA hx, ⟨hx₁A, hx₂A⟩⟩

variables {𝕜} {A B C : set E} {x : E}

protected lemma is_extreme.rfl :
  is_extreme 𝕜 A A :=
is_extreme.refl 𝕜 A

@[trans] protected lemma is_extreme.trans (hAB : is_extreme 𝕜 A B) (hBC : is_extreme 𝕜 B C) :
  is_extreme 𝕜 A C :=
begin
  refine ⟨subset.trans hBC.1 hAB.1, λ x₁ hx₁A x₂ hx₂A x hxC hx, _⟩,
  obtain ⟨hx₁B, hx₂B⟩ := hAB.2 hx₁A hx₂A (hBC.1 hxC) hx,
  exact hBC.2 hx₁B hx₂B hxC hx,
end

protected lemma is_extreme.antisymm :
  anti_symmetric (is_extreme 𝕜 : set E → set E → Prop) :=
λ A B hAB hBA, subset.antisymm hBA.1 hAB.1

instance : is_partial_order (set E) (is_extreme 𝕜) :=
{ refl := is_extreme.refl 𝕜,
  trans := λ A B C, is_extreme.trans,
  antisymm := is_extreme.antisymm }

lemma is_extreme.inter (hAB : is_extreme 𝕜 A B) (hAC : is_extreme 𝕜 A C) :
  is_extreme 𝕜 A (B ∩ C) :=
begin
  use subset.trans (inter_subset_left _ _) hAB.1,
  rintro x₁ hx₁A x₂ hx₂A x ⟨hxB, hxC⟩ hx,
  obtain ⟨hx₁B, hx₂B⟩ := hAB.2 hx₁A hx₂A hxB hx,
  obtain ⟨hx₁C, hx₂C⟩ := hAC.2 hx₁A hx₂A hxC hx,
  exact ⟨⟨hx₁B, hx₁C⟩, hx₂B, hx₂C⟩,
end

protected lemma is_extreme.mono (hAC : is_extreme 𝕜 A C) (hBA : B ⊆ A) (hCB : C ⊆ B) :
  is_extreme 𝕜 B C :=
⟨hCB, λ x₁ hx₁B x₂ hx₂B x hxC hx, hAC.2 (hBA hx₁B) (hBA hx₂B) hxC hx⟩

lemma is_extreme_Inter {ι : Sort*} [nonempty ι] {F : ι → set E}
  (hAF : ∀ i : ι, is_extreme 𝕜 A (F i)) :
  is_extreme 𝕜 A (⋂ i : ι, F i) :=
begin
  obtain i := classical.arbitrary ι,
  refine ⟨Inter_subset_of_subset i (hAF i).1, λ x₁ hx₁A x₂ hx₂A x hxF hx, _⟩,
  simp_rw mem_Inter at ⊢ hxF,
  have h := λ i, (hAF i).2 hx₁A hx₂A (hxF i) hx,
  exact ⟨λ i, (h i).1, λ i, (h i).2⟩,
end

lemma is_extreme_bInter {F : set (set E)} (hF : F.nonempty) (hA : ∀ B ∈ F, is_extreme 𝕜 A B) :
  is_extreme 𝕜 A (⋂ B ∈ F, B) :=
by { haveI := hF.to_subtype, simpa only [Inter_subtype] using is_extreme_Inter (λ i : F, hA _ i.2) }

lemma is_extreme_sInter {F : set (set E)} (hF : F.nonempty)
  (hAF : ∀ B ∈ F, is_extreme 𝕜 A B) :
  is_extreme 𝕜 A (⋂₀ F) :=
begin
  obtain ⟨B, hB⟩ := hF,
  refine ⟨(sInter_subset_of_mem hB).trans (hAF B hB).1, λ x₁ hx₁A x₂ hx₂A x hxF hx, _⟩,
  simp_rw mem_sInter at ⊢ hxF,
  have h := λ B hB, (hAF B hB).2 hx₁A hx₂A (hxF B hB) hx,
  exact ⟨λ B hB, (h B hB).1, λ B hB, (h B hB).2⟩,
end

lemma mem_extreme_points :
  x ∈ A.extreme_points 𝕜 ↔ x ∈ A ∧ ∀ (x₁ x₂ ∈ A), x ∈ open_segment 𝕜 x₁ x₂ → x₁ = x ∧ x₂ = x :=
iff.rfl

/-- x is an extreme point to A iff {x} is an extreme set of A. -/
lemma mem_extreme_points_iff_extreme_singleton :
  x ∈ A.extreme_points 𝕜 ↔ is_extreme 𝕜 A {x} :=
begin
  refine ⟨_, λ hx, ⟨singleton_subset_iff.1 hx.1, λ x₁ hx₁ x₂ hx₂, hx.2 hx₁ hx₂ rfl⟩⟩,
  rintro ⟨hxA, hAx⟩,
  use singleton_subset_iff.2 hxA,
  rintro x₁ hx₁A x₂ hx₂A y (rfl : y = x),
  exact hAx hx₁A hx₂A,
end

lemma extreme_points_subset : A.extreme_points 𝕜 ⊆ A := λ x hx, hx.1

@[simp] lemma extreme_points_empty :
  (∅ : set E).extreme_points 𝕜 = ∅ :=
subset_empty_iff.1 extreme_points_subset

@[simp] lemma extreme_points_singleton :
  ({x} : set E).extreme_points 𝕜 = {x} :=
extreme_points_subset.antisymm $ singleton_subset_iff.2
  ⟨mem_singleton x, λ x₁ hx₁ x₂ hx₂ _, ⟨hx₁, hx₂⟩⟩

lemma inter_extreme_points_subset_extreme_points_of_subset (hBA : B ⊆ A) :
  B ∩ A.extreme_points 𝕜 ⊆ B.extreme_points 𝕜 :=
λ x ⟨hxB, hxA⟩, ⟨hxB, λ x₁ hx₁ x₂ hx₂ hx, hxA.2 (hBA hx₁) (hBA hx₂) hx⟩

lemma is_extreme.extreme_points_subset_extreme_points (hAB : is_extreme 𝕜 A B) :
  B.extreme_points 𝕜 ⊆ A.extreme_points 𝕜 :=
λ x hx, mem_extreme_points_iff_extreme_singleton.2 (hAB.trans
  (mem_extreme_points_iff_extreme_singleton.1 hx))

lemma is_extreme.extreme_points_eq (hAB : is_extreme 𝕜 A B) :
  B.extreme_points 𝕜 = B ∩ A.extreme_points 𝕜 :=
subset.antisymm (λ x hx, ⟨hx.1, hAB.extreme_points_subset_extreme_points hx⟩)
  (inter_extreme_points_subset_extreme_points_of_subset hAB.1)

end has_smul

section ordered_semiring
variables [ordered_semiring 𝕜] [add_comm_group E] [add_comm_group F] [Π i, add_comm_group (π i)]
  [module 𝕜 E] [module 𝕜 F] [Π i, module 𝕜 (π i)] {A B : set E} {x : E}

lemma is_extreme.convex_diff (hA : convex 𝕜 A) (hAB : is_extreme 𝕜 A B) :
  convex 𝕜 (A \ B) :=
convex_iff_open_segment_subset.2 (λ x₁ ⟨hx₁A, hx₁B⟩ x₂ ⟨hx₂A, hx₂B⟩ x hx,
    ⟨hA.open_segment_subset hx₁A hx₂A hx, λ hxB, hx₁B (hAB.2 hx₁A hx₂A hxB hx).1⟩)

@[simp] lemma extreme_points_prod (s : set E) (t : set F) :
  (s ×ˢ t).extreme_points 𝕜 = s.extreme_points 𝕜 ×ˢ t.extreme_points 𝕜 :=
begin
  ext,
  refine (and_congr_right $ λ hx, ⟨λ h, _, λ h, _⟩).trans (and_and_and_comm _ _ _ _),
  split,
  { rintro x₁ hx₁ x₂ hx₂ hx_fst,
    refine (h (mk_mem_prod hx₁ hx.2) (mk_mem_prod hx₂ hx.2) _).imp
      (congr_arg prod.fst) (congr_arg prod.fst),
    rw ←prod.image_mk_open_segment_left,
    exact ⟨_, hx_fst, prod.mk.eta⟩ },
  { rintro x₁ hx₁ x₂ hx₂ hx_snd,
    refine (h (mk_mem_prod hx.1 hx₁) (mk_mem_prod hx.1 hx₂) _).imp
      (congr_arg prod.snd) (congr_arg prod.snd),
    rw ←prod.image_mk_open_segment_right,
    exact ⟨_, hx_snd, prod.mk.eta⟩ },
  { rintro x₁ hx₁ x₂ hx₂ ⟨a, b, ha, hb, hab, hx'⟩,
    simp_rw prod.ext_iff,
    exact (and_and_and_comm _ _ _ _).1
     ⟨h.1 hx₁.1 hx₂.1 ⟨a, b, ha, hb, hab, congr_arg prod.fst hx'⟩,
      h.2 hx₁.2 hx₂.2 ⟨a, b, ha, hb, hab, congr_arg prod.snd hx'⟩⟩ }
end

@[simp] lemma extreme_points_pi (s : Π i, set (π i)) :
  (univ.pi s).extreme_points 𝕜 = univ.pi (λ i, (s i).extreme_points 𝕜) :=
begin
  ext,
  simp only [mem_extreme_points, mem_pi, mem_univ, true_implies_iff, @forall_and_distrib ι],
  refine and_congr_right (λ hx, ⟨λ h i, _, λ h, _⟩),
  { rintro x₁ hx₁ x₂ hx₂ hi,
    refine (h (update x i x₁) _ (update x i x₂) _ _).imp (λ h₁, by rw [←h₁, update_same])
      (λ h₂, by rw [←h₂, update_same]),
    iterate 2
    { rintro j,
      obtain rfl | hji := eq_or_ne j i,
      { rwa update_same },
      { rw update_noteq hji,
        exact hx _ } },
    rw ←pi.image_update_open_segment,
    exact ⟨_, hi, update_eq_self _ _⟩ },
  { rintro x₁ hx₁ x₂ hx₂ ⟨a, b, ha, hb, hab, hx'⟩,
    simp_rw [funext_iff, ←forall_and_distrib],
    exact λ i, h _ _ (hx₁ _) _ (hx₂ _) ⟨a, b, ha, hb, hab, congr_fun hx' _⟩ }
end

end ordered_semiring

section linear_ordered_ring
variables {𝕜} [linear_ordered_ring 𝕜] [add_comm_group E] [module 𝕜 E]
variables [densely_ordered 𝕜] [no_zero_smul_divisors 𝕜 E] {A B : set E} {x : E}

/-- A useful restatement using `segment`: `x` is an extreme point iff the only (closed) segments
that contain it are those with `x` as one of their endpoints. -/
lemma mem_extreme_points_iff_forall_segment :
  x ∈ A.extreme_points 𝕜 ↔ x ∈ A ∧ ∀ (x₁ x₂ ∈ A), x ∈ segment 𝕜 x₁ x₂ → x₁ = x ∨ x₂ = x :=
begin
  refine and_congr_right (λ hxA, forall₄_congr $ λ x₁ h₁ x₂ h₂, _),
  split,
  { rw ← insert_endpoints_open_segment,
    rintro H (rfl|rfl|hx),
    exacts [or.inl rfl, or.inr rfl, or.inl $ (H hx).1] },
  { intros H hx,
    rcases H (open_segment_subset_segment _ _ _ hx) with rfl | rfl,
    exacts [⟨rfl, (left_mem_open_segment_iff.1 hx).symm⟩, ⟨right_mem_open_segment_iff.1 hx, rfl⟩] }
end

lemma convex.mem_extreme_points_iff_convex_diff (hA : convex 𝕜 A) :
  x ∈ A.extreme_points 𝕜 ↔ x ∈ A ∧ convex 𝕜 (A \ {x}) :=
begin
  use λ hx, ⟨hx.1, (mem_extreme_points_iff_extreme_singleton.1 hx).convex_diff hA⟩,
  rintro ⟨hxA, hAx⟩,
  refine mem_extreme_points_iff_forall_segment.2 ⟨hxA, λ x₁ hx₁ x₂ hx₂ hx, _⟩,
  rw convex_iff_segment_subset at hAx,
  by_contra' h,
  exact (hAx ⟨hx₁, λ hx₁, h.1 (mem_singleton_iff.2 hx₁)⟩
    ⟨hx₂, λ hx₂, h.2 (mem_singleton_iff.2 hx₂)⟩ hx).2 rfl,
end

lemma convex.mem_extreme_points_iff_mem_diff_convex_hull_diff (hA : convex 𝕜 A) :
  x ∈ A.extreme_points 𝕜 ↔ x ∈ A \ convex_hull 𝕜 (A \ {x}) :=
by rw [hA.mem_extreme_points_iff_convex_diff, hA.convex_remove_iff_not_mem_convex_hull_remove,
  mem_diff]

lemma extreme_points_convex_hull_subset :
  (convex_hull 𝕜 A).extreme_points 𝕜 ⊆ A :=
begin
  rintro x hx,
  rw (convex_convex_hull 𝕜 _).mem_extreme_points_iff_convex_diff at hx,
  by_contra,
  exact (convex_hull_min (subset_diff.2 ⟨subset_convex_hull 𝕜 _, disjoint_singleton_right.2 h⟩) hx.2
    hx.1).2 rfl,
  apply_instance
end

end linear_ordered_ring
