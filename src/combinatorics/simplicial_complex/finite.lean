/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simplicial_complex.basic

/-!
# Finite simplicial complexes
-/

open geometry set

variables {𝕜 E : Type*}

namespace geometry.simplicial_complex
variables [ordered_ring 𝕜] [add_comm_group E] [module 𝕜 E] [module 𝕜 E]
  {S : simplicial_complex 𝕜 E} {X Y : finset E}

/-- A simplicial complex is finite iff it has finitely many faces. -/
protected def finite (S : simplicial_complex 𝕜 E) : Prop := S.faces.finite

noncomputable def faces_finset (S : simplicial_complex 𝕜 E) (hS : S.finite) :
  finset (finset E) :=
hS.to_finset

@[simp] lemma mem_faces_finset (hS : S.finite) : X ∈ S.faces_finset hS ↔ X ∈ S.faces :=
set.finite.mem_to_finset _

/-- A simplicial complex `S` is locally finite at the face `X` iff `X` is a subface of finitely many
faces in `S`. -/
def locally_finite_at (S : simplicial_complex 𝕜 E) (X : finset E) : Prop :=
{Y ∈ S.faces | X ⊆ Y}.finite

/-- A simplicial complex `S` is locally finite at the face `X` iff `X` is a subface of infinitely
many faces in `S`. -/
def locally_infinite_at (S : simplicial_complex 𝕜 E) (X : finset E) : Prop :=
{Y ∈ S.faces | X ⊆ Y}.infinite

@[simp] lemma locally_finite_at_iff_not_locally_infinite_at :
  ¬ S.locally_infinite_at X ↔ S.locally_finite_at X :=
not_not

/-- A simplicial complex is locally finite iff each of its nonempty faces belongs to finitely many
faces. -/
def locally_finite (S : simplicial_complex 𝕜 E) : Prop :=
∀ {X : finset _}, X ∈ S.faces → X.nonempty → S.locally_finite_at X

lemma locally_finite_at_up_closed (hX : S.locally_finite_at X) (hXY : X ⊆ Y) :
  S.locally_finite_at Y :=
begin
  apply hX.subset,
  rintro Z ⟨_, _⟩,
  exact ⟨‹Z ∈ S.faces›, finset.subset.trans hXY ‹Y ⊆ Z›⟩,
end

lemma locally_infinite_at_down_closed (hY : S.locally_infinite_at Y) (hXY : X ⊆ Y) :
  S.locally_infinite_at X :=
λ t, hY (locally_finite_at_up_closed t hXY)

lemma locally_finite_of_finite (hS : S.finite) : S.locally_finite :=
λ X hX _, hS.subset (λ Y hY, hY.1)

/-- A simplicial complex is locally finite iff each point belongs to finitely many faces. -/
lemma locally_finite_iff_mem_finitely_many_faces [decidable_eq E] :
  S.locally_finite ↔ ∀ x : E, finite {X | X ∈ S.faces ∧ x ∈ convex_hull 𝕜 (X : set E)} :=
begin
  split,
  { unfold locally_finite,
    contrapose!,
    rintro ⟨x, hx⟩,
    by_cases hxspace : x ∈ S.space,
    { obtain ⟨X, ⟨hX, hXhull, hXbound⟩, hXunique⟩ := combi_interiors_partition hxspace,
      simp at hXunique,
      refine ⟨X, hX, finset.nonempty_of_ne_empty _, λ hXlocallyfinite, hx _⟩,
      { rintro rfl,
        simpa using hXhull },
      suffices h : {X : finset E | X ∈ S.faces ∧ x ∈ convex_hull 𝕜 ↑X} ⊆
        {Y : finset E | Y ∈ S.faces ∧ X ⊆ Y},
      { exact finite.subset hXlocallyfinite h },
      rintro Y ⟨hY, hYhull⟩,
      use hY,
      have hXYhull := S.inter_subset_convex_hull hX hY ⟨hXhull, hYhull⟩,
      rw ←finset.coe_inter at hXYhull,
      by_contra hXY,
      exact hXbound (mem_combi_frontier_iff.2 ⟨X ∩ Y,
        ⟨finset.inter_subset_left X Y, λ hXXY, hXY (finset.subset_inter_iff.1 hXXY).2⟩, hXYhull⟩) },
    { cases hx _,
      suffices h : {X : finset E | X ∈ S.faces ∧ x ∈ convex_hull 𝕜 ↑X} = ∅,
      { rw h,
        exact finite_empty },
      apply eq_empty_of_subset_empty,
      rintro X ⟨hX, h⟩,
      exact hxspace (mem_bUnion hX h) }},
  { rintro hS X hX ⟨x, hx⟩,
    suffices h : {Y : finset E | Y ∈ S.faces ∧ X ⊆ Y} ⊆
      {Y : finset E | Y ∈ S.faces ∧ x ∈ convex_hull 𝕜 ↑Y},
    { exact (hS x).subset h },
    rintro Y ⟨hY, hXY⟩,
    exact ⟨hY, subset_convex_hull 𝕜 Y (hXY hx)⟩ }
end

end geometry.simplicial_complex
