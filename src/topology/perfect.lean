/-
Copyright (c) 2022 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
-/
import topology.separation
import topology.bases

/-!
# Perfect Sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define perfect subsets of a topological space, and prove some basic properties,
including a version of the Cantor-Bendixson Theorem.

## Main Definitions

* `perfect C`: A set `C` is perfect, meaning it is closed and every point of it
  is an accumulation point of itself.

## Main Statements

* `perfect.splitting`: A perfect nonempty set contains two disjoint perfect nonempty subsets.
  The main inductive step in the construction of an embedding from the Cantor space to a
  perfect nonempty complete metric space.
* `exists_countable_union_perfect_of_is_closed`: One version of the **Cantor-Bendixson Theorem**:
  A closed set in a second countable space can be written as the union of a countable set and a
  perfect set.

## Implementation Notes

We do not require perfect sets to be nonempty.

We define a nonstandard predicate, `preperfect`, which drops the closed-ness requirement
from the definition of perfect. In T1 spaces, this is equivalent to having a perfect closure,
see `preperfect_iff_perfect_closure`.

## References

* [kechris1995] (Chapter 6)

## Tags

accumulation point, perfect set, Cantor-Bendixson.

-/

open_locale topology filter
open topological_space filter set

variables {α : Type*} [topological_space α] {C : set α}

/-- If `x` is an accumulation point of a set `C` and `U` is a neighborhood of `x`,
then `x` is an accumulation point of `U ∩ C`. -/
theorem acc_pt.nhds_inter {x : α} {U : set α} (h_acc : acc_pt x (𝓟 C)) (hU : U ∈ 𝓝 x) :
  acc_pt x (𝓟 (U ∩ C)) :=
begin
  have : 𝓝[≠] x ≤ 𝓟 U,
  { rw le_principal_iff,
    exact mem_nhds_within_of_mem_nhds hU, },
  rw [acc_pt, ← inf_principal, ← inf_assoc, inf_of_le_left this],
  exact h_acc,
end

/-- A set `C` is preperfect if all of its points are accumulation points of itself.
If `C` is nonempty and `α` is a T1 space, this is equivalent to the closure of `C` being perfect.
See `preperfect_iff_perfect_closure`.-/
def preperfect (C : set α) : Prop := ∀ x ∈ C, acc_pt x (𝓟 C)

/-- A set `C` is called perfect if it is closed and all of its
points are accumulation points of itself.
Note that we do not require `C` to be nonempty.-/
structure perfect (C : set α) : Prop :=
(closed : is_closed C)
(acc : preperfect C)

lemma preperfect_iff_nhds : preperfect C ↔ ∀ x ∈ C, ∀ U ∈ 𝓝 x, ∃ y ∈ U ∩ C, y ≠ x :=
by simp only [preperfect, acc_pt_iff_nhds]

/-- The intersection of a preperfect set and an open set is preperfect-/
theorem preperfect.open_inter {U : set α} (hC : preperfect C) (hU : is_open U) :
  preperfect (U ∩ C) :=
begin
  rintros x ⟨xU, xC⟩,
  apply (hC _ xC).nhds_inter,
  exact hU.mem_nhds xU,
end

/-- The closure of a preperfect set is perfect.
For a converse, see `preperfect_iff_perfect_closure`-/
theorem preperfect.perfect_closure (hC : preperfect C) : perfect (closure C) :=
begin
  split, { exact is_closed_closure },
  intros x hx,
  by_cases h : x ∈ C; apply acc_pt.mono _ (principal_mono.mpr subset_closure),
  { exact hC _ h },
  have : {x}ᶜ ∩ C = C := by simp [h],
  rw [acc_pt, nhds_within, inf_assoc, inf_principal, this],
  rw [closure_eq_cluster_pts] at hx,
  exact hx,
end

/-- In a T1 space, being preperfect is equivalent to having perfect closure.-/
theorem preperfect_iff_perfect_closure [t1_space α] :
  preperfect C ↔ perfect (closure C) :=
begin
  split; intro h, { exact h.perfect_closure },
  intros x xC,
  have H : acc_pt x (𝓟 (closure C)) := h.acc _ (subset_closure xC),
  rw acc_pt_iff_frequently at *,
  have : ∀ y , y ≠ x ∧ y ∈ closure C → ∃ᶠ z in 𝓝 y, z ≠ x ∧ z ∈ C,
  { rintros y ⟨hyx, yC⟩,
    simp only [← mem_compl_singleton_iff, @and_comm _ (_ ∈ C) , ← frequently_nhds_within_iff,
      hyx.nhds_within_compl_singleton, ← mem_closure_iff_frequently],
    exact yC, },
  rw ← frequently_frequently_nhds,
  exact H.mono this,
end

theorem perfect.closure_nhds_inter {U : set α} (hC : perfect C) (x : α) (xC : x ∈ C) (xU : x ∈ U)
  (Uop : is_open U) : perfect (closure (U ∩ C)) ∧ (closure (U ∩ C)).nonempty :=
begin
  split,
  { apply preperfect.perfect_closure,
    exact (hC.acc).open_inter Uop, },
  apply nonempty.closure,
  exact ⟨x, ⟨xU, xC⟩⟩,
end

/-- Given a perfect nonempty set in a T2.5 space, we can find two disjoint perfect subsets
This is the main inductive step in the proof of the Cantor-Bendixson Theorem-/
lemma perfect.splitting [t2_5_space α] (hC : perfect C) (hnonempty : C.nonempty) :
  ∃ C₀ C₁ : set α, (perfect C₀ ∧ C₀.nonempty ∧ C₀ ⊆ C) ∧
  (perfect C₁ ∧ C₁.nonempty ∧ C₁ ⊆ C) ∧ disjoint C₀ C₁ :=
begin
  cases hnonempty with y yC,
  obtain ⟨x, xC, hxy⟩ : ∃ x ∈ C, x ≠ y,
  { have := hC.acc _ yC,
    rw acc_pt_iff_nhds at this,
    rcases this univ (univ_mem) with ⟨x, xC, hxy⟩,
    exact ⟨x, xC.2, hxy⟩, },
  obtain ⟨U, xU, Uop, V, yV, Vop, hUV⟩ := exists_open_nhds_disjoint_closure hxy,
  use [closure (U ∩ C), closure (V ∩ C)],
  split; rw ← and_assoc,
  { refine ⟨hC.closure_nhds_inter x xC xU Uop, _⟩,
    rw hC.closed.closure_subset_iff,
    exact inter_subset_right _ _, },
  split,
  { refine ⟨hC.closure_nhds_inter y yC yV Vop, _⟩,
    rw hC.closed.closure_subset_iff,
    exact inter_subset_right _ _, },
  apply disjoint.mono _ _ hUV; apply closure_mono; exact inter_subset_left _ _,
end

section kernel

/-- The **Cantor-Bendixson Theorem**: Any closed subset of a second countable space
can be written as the union of a countable set and a perfect set.-/
theorem exists_countable_union_perfect_of_is_closed [second_countable_topology α]
  (hclosed : is_closed C) :
  ∃ V D : set α, (V.countable) ∧ (perfect D) ∧ (C = V ∪ D) :=
begin
  obtain ⟨b, bct, bnontrivial, bbasis⟩ := topological_space.exists_countable_basis α,
  let v := {U ∈ b | (U ∩ C).countable},
  let V := ⋃ U ∈ v, U,
  let D := C \ V,
  have Vct : (V ∩ C).countable,
  { simp only [Union_inter, mem_sep_iff],
    apply countable.bUnion,
    { exact countable.mono (inter_subset_left _ _) bct, },
    { exact inter_subset_right _ _, }, },
  refine ⟨V ∩ C, D, Vct, ⟨_, _⟩, _⟩,
  { refine hclosed.sdiff (is_open_bUnion (λ U, _)),
    exact λ ⟨Ub, _⟩, is_topological_basis.is_open bbasis Ub, },
  { rw preperfect_iff_nhds,
    intros x xD E xE,
    have : ¬ (E ∩ D).countable,
    { intro h,
      obtain ⟨U, hUb, xU, hU⟩ : ∃ U ∈ b, x ∈ U ∧ U ⊆ E,
      { exact (is_topological_basis.mem_nhds_iff bbasis).mp xE, },
      have hU_cnt : (U ∩ C).countable,
      { apply @countable.mono _ _ ((E ∩ D) ∪ (V ∩ C)),
        { rintros y ⟨yU, yC⟩,
          by_cases y ∈ V,
          { exact mem_union_right _ (mem_inter h yC), },
          { exact mem_union_left _ (mem_inter (hU yU) ⟨yC, h⟩), }, },
        exact countable.union h Vct, },
      have : U ∈ v := ⟨hUb, hU_cnt⟩,
      apply xD.2,
      exact mem_bUnion this xU, },
    by_contradiction h,
    push_neg at h,
    exact absurd (countable.mono h (set.countable_singleton _)) this, },
  { rw [inter_comm, inter_union_diff], },
end

/-- Any uncountable closed set in a second countable space contains a nonempty perfect subset.-/
theorem exists_perfect_nonempty_of_is_closed_of_not_countable [second_countable_topology α]
  (hclosed : is_closed C) (hunc : ¬ C.countable) :
  ∃ D : set α, perfect D ∧ D.nonempty ∧ D ⊆ C :=
begin
  rcases exists_countable_union_perfect_of_is_closed hclosed with ⟨V, D, Vct, Dperf, VD⟩,
  refine ⟨D, ⟨Dperf, _⟩⟩,
  split,
  { rw nonempty_iff_ne_empty,
    by_contradiction,
    rw [h, union_empty] at VD,
    rw VD at hunc,
    contradiction, },
  rw VD,
  exact subset_union_right _ _,
end

end kernel
