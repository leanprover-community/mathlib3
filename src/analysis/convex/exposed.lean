/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.convex.extreme
import analysis.convex.function
import analysis.normed_space.ordered

/-!
# Exposed sets

This file defines exposed sets and exposed points for sets in a real vector space.

An exposed subset of `A` is a subset of `A` that is the set of all maximal points of a functional
(a continuous linear map `E → 𝕜`) over `A`. By convention, `∅` is an exposed subset of all sets.
This allows for better functioriality of the definition (the intersection of two exposed subsets is
exposed, faces of a polytope form a bounded lattice).
This is an analytic notion of "being on the side of". It is stronger than being extreme (see
`is_exposed.is_extreme`), but weaker (for exposed points) than being a vertex.

An exposed set of `A` is sometimes called a "face of `A`", but we decided to reserve this
terminology to the more specific notion of a face of a polytope (sometimes hopefully soon out
on mathlib!).

## Main declarations

* `is_exposed 𝕜 A B`: States that `B` is an exposed set of `A` (in the literature, `A` is often
  implicit).
* `is_exposed.is_extreme`: An exposed set is also extreme.

## References

See chapter 8 of [Barry Simon, *Convexity*][simon2011]

## TODO

Define intrinsic frontier/interior and prove the lemmas related to exposed sets and points.

Generalise to Locally Convex Topological Vector Spaces™

More not-yet-PRed stuff is available on the branch `sperner_again`.
-/

open_locale classical affine big_operators
open set

variables (𝕜 : Type*) {E : Type*} [normed_linear_ordered_field 𝕜] [normed_group E]
  [normed_space 𝕜 E] {l : E →L[𝕜] 𝕜} {A B C : set E} {X : finset E} {x : E}

/-- A set `B` is exposed with respect to `A` iff it maximizes some functional over `A` (and contains
all points maximizing it). Written `is_exposed 𝕜 A B`. -/
def is_exposed (A B : set E) : Prop :=
B.nonempty → ∃ l : E →L[𝕜] 𝕜, B = {x ∈ A | ∀ y ∈ A, l y ≤ l x}

variables {𝕜}

/-- A useful way to build exposed sets from intersecting `A` with halfspaces (modelled by an
inequality with a functional). -/
def continuous_linear_map.to_exposed (l : E →L[𝕜] 𝕜) (A : set E) : set E :=
{x ∈ A | ∀ y ∈ A, l y ≤ l x}

lemma continuous_linear_map.to_exposed.is_exposed : is_exposed 𝕜 A (l.to_exposed A) := λ h, ⟨l, rfl⟩

lemma is_exposed_empty : is_exposed 𝕜 A ∅ :=
λ ⟨x, hx⟩, by { exfalso, exact hx }

namespace is_exposed

protected lemma subset (hAB : is_exposed 𝕜 A B) : B ⊆ A :=
begin
  rintro x hx,
  obtain ⟨_, rfl⟩ := hAB ⟨x, hx⟩,
  exact hx.1,
end

@[refl] lemma refl (A : set E) : is_exposed 𝕜 A A :=
λ ⟨w, hw⟩, ⟨0, subset.antisymm (λ x hx, ⟨hx, λ y hy, by exact le_refl 0⟩) (λ x hx, hx.1)⟩

lemma antisymm (hB : is_exposed 𝕜 A B) (hA : is_exposed 𝕜 B A) :
  A = B :=
hA.subset.antisymm hB.subset

/- `is_exposed` is *not* transitive: Consider a (topologically) open cube with vertices
`A₀₀₀, ..., A₁₁₁` and add to it the triangle `A₀₀₀A₀₀₁A₀₁₀`. Then `A₀₀₁A₀₁₀` is an exposed subset
of `A₀₀₀A₀₀₁A₀₁₀` which is an exposed subset of the cube, but `A₀₀₁A₀₁₀` is not itself an exposed
subset of the cube. -/

protected lemma mono (hC : is_exposed 𝕜 A C) (hBA : B ⊆ A) (hCB : C ⊆ B) :
  is_exposed 𝕜 B C :=
begin
  rintro ⟨w, hw⟩,
  obtain ⟨l, rfl⟩ := hC ⟨w, hw⟩,
  exact ⟨l, subset.antisymm (λ x hx, ⟨hCB hx, λ y hy, hx.2 y (hBA hy)⟩)
    (λ x hx, ⟨hBA hx.1, λ y hy, (hw.2 y hy).trans (hx.2 w (hCB hw))⟩)⟩,
end

/-- If `B` is an exposed subset of `A`, then `B` is the intersection of `A` with some closed
halfspace. The converse is *not* true. It would require that the corresponding open halfspace
doesn't intersect `A`. -/
lemma eq_inter_halfspace (hAB : is_exposed 𝕜 A B) :
  ∃ l : E →L[𝕜] 𝕜, ∃ a, B = {x ∈ A | a ≤ l x} :=
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

lemma inter (hB : is_exposed 𝕜 A B) (hC : is_exposed 𝕜 A C) :
  is_exposed 𝕜 A (B ∩ C) :=
begin
  rintro ⟨w, hwB, hwC⟩,
  obtain ⟨l₁, rfl⟩ := hB ⟨w, hwB⟩,
  obtain ⟨l₂, rfl⟩ := hC ⟨w, hwC⟩,
  refine ⟨l₁ + l₂, subset.antisymm _ _⟩,
  { rintro x ⟨⟨hxA, hxB⟩, ⟨-, hxC⟩⟩,
    exact ⟨hxA, λ z hz, add_le_add (hxB z hz) (hxC z hz)⟩ },
  rintro x ⟨hxA, hx⟩,
  refine ⟨⟨hxA, λ y hy, _⟩, hxA, λ y hy, _⟩,
  { exact (add_le_add_iff_right (l₂ x)).1 ((add_le_add (hwB.2 y hy) (hwC.2 x hxA)).trans
      (hx w hwB.1)) },
  { exact (add_le_add_iff_left (l₁ x)).1 (le_trans (add_le_add (hwB.2 x hxA) (hwC.2 y hy))
    (hx w hwB.1)) }
end

lemma sInter {F : finset (set E)} (hF : F.nonempty)
  (hAF : ∀ B ∈ F, is_exposed 𝕜 A B) :
  is_exposed 𝕜 A (⋂₀ F) :=
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

lemma inter_left (hC : is_exposed 𝕜 A C) (hCB : C ⊆ B) :
  is_exposed 𝕜 (A ∩ B) C :=
begin
  rintro ⟨w, hw⟩,
  obtain ⟨l, rfl⟩ := hC ⟨w, hw⟩,
  exact ⟨l, subset.antisymm (λ x hx, ⟨⟨hx.1, hCB hx⟩, λ y hy, hx.2 y hy.1⟩)
    (λ x ⟨⟨hxC, _⟩, hx⟩, ⟨hxC, λ y hy, (hw.2 y hy).trans (hx w ⟨hC.subset hw, hCB hw⟩)⟩)⟩,
end

lemma inter_right (hC : is_exposed 𝕜 B C) (hCA : C ⊆ A) :
  is_exposed 𝕜 (A ∩ B) C :=
begin
  rw inter_comm,
  exact hC.inter_left hCA,
end

protected lemma is_extreme [normed_space ℝ E]  (hAB : is_exposed ℝ A B) :
  is_extreme ℝ A B :=
begin
  refine ⟨hAB.subset, λ x₁ x₂ hx₁A hx₂A x hxB hx, _⟩,
  obtain ⟨l, rfl⟩ := hAB ⟨x, hxB⟩,
  have hl : convex_on univ l := l.to_linear_map.convex_on convex_univ,
  have hlx₁ := hxB.2 x₁ hx₁A,
  have hlx₂ := hxB.2 x₂ hx₂A,
  refine ⟨⟨hx₁A, λ y hy, _⟩, ⟨hx₂A, λ y hy, _⟩⟩,
  { rw hlx₁.antisymm (hl.le_left_of_right_le (mem_univ _) (mem_univ _) hx hlx₂),
    exact hxB.2 y hy },
  { rw hlx₂.antisymm (hl.le_right_of_left_le (mem_univ _) (mem_univ _) hx hlx₁),
    exact hxB.2 y hy }
end

protected lemma convex [normed_space ℝ E] (hAB : is_exposed ℝ A B) (hA : convex ℝ A) :
  convex ℝ B :=
begin
  obtain rfl | hB := B.eq_empty_or_nonempty,
  { exact convex_empty },
  obtain ⟨l, rfl⟩ := hAB hB,
  exact λ x₁ x₂ hx₁ hx₂ a b ha hb hab, ⟨hA hx₁.1 hx₂.1 ha hb hab, λ y hy,
    ((l.to_linear_map.concave_on convex_univ).concave_le _
    ⟨mem_univ _, hx₁.2 y hy⟩ ⟨mem_univ _, hx₂.2 y hy⟩ ha hb hab).2⟩,
end

lemma is_closed [normed_space ℝ E] (hAB : is_exposed ℝ A B) (hA : is_closed A) :
  is_closed B :=
begin
  obtain ⟨l, a, rfl⟩ := hAB.eq_inter_halfspace,
  exact hA.is_closed_le continuous_on_const l.continuous.continuous_on,
end

lemma is_compact [normed_space ℝ E] (hAB : is_exposed ℝ A B) (hA : is_compact A) :
  is_compact B :=
compact_of_is_closed_subset hA (hAB.is_closed hA.is_closed) hAB.subset

end is_exposed

variables (𝕜)

/-- A point is exposed with respect to `A` iff there exists an hyperplane whose intersection with
`A` is exactly that point. -/
def set.exposed_points (A : set E) :
  set E :=
{x ∈ A | ∃ l : E →L[𝕜] 𝕜, ∀ y ∈ A, l y ≤ l x ∧ (l x ≤ l y → y = x)}

variables {𝕜}

lemma exposed_point_def :
  x ∈ A.exposed_points 𝕜 ↔ x ∈ A ∧ ∃ l : E →L[𝕜] 𝕜, ∀ y ∈ A, l y ≤ l x ∧ (l x ≤ l y → y = x) :=
iff.rfl

lemma exposed_points_subset :
  A.exposed_points 𝕜 ⊆ A :=
λ x hx, hx.1

@[simp] lemma exposed_points_empty :
  (∅ : set E).exposed_points 𝕜 = ∅ :=
subset_empty_iff.1 exposed_points_subset

/-- Exposed points exactly correspond to exposed singletons. -/
lemma mem_exposed_points_iff_exposed_singleton :
  x ∈ A.exposed_points 𝕜 ↔ is_exposed 𝕜 A {x} :=
begin
  use λ ⟨hxA, l, hl⟩ h, ⟨l, eq.symm $ eq_singleton_iff_unique_mem.2 ⟨⟨hxA, λ y hy, (hl y hy).1⟩,
    λ z hz, (hl z hz.1).2 (hz.2 x hxA)⟩⟩,
  rintro h,
  obtain ⟨l, hl⟩ := h ⟨x, mem_singleton _⟩,
  rw [eq_comm, eq_singleton_iff_unique_mem] at hl,
  exact ⟨hl.1.1, l, λ y hy, ⟨hl.1.2 y hy, λ hxy, hl.2 y ⟨hy, λ z hz, (hl.1.2 z hz).trans hxy⟩⟩⟩,
end

lemma exposed_points_subset_extreme_points [normed_space ℝ E] :
  A.exposed_points ℝ ⊆ A.extreme_points ℝ :=
λ x hx, mem_extreme_points_iff_extreme_singleton.2
  (mem_exposed_points_iff_exposed_singleton.1 hx).is_extreme
