/-
Copyright (c) 2022 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
-/
import topology.separation
import topology.bases

/-!
# Perfect Sets

In this file we define perfect subsets of a topological space, and prove some basic properties,
including a version of the Cantor-Bendixson Theorem.

## Main Definitions

* `perfect C`: A set `C` is perfect, meaning it is closed and every point of it
  is an accumulation point of itself.

## Main Statements

* `perf_nonempty.splitting`: A perfect nonempty set contains two disjoint perfect nonempty subsets.
  The main inductive step in the construction of an embedding from the Cantor space to a
  perfect nonempty complete metric space.
* `ctble_union_perfect_of_closed`: One version of the Cantor-Bendixson Theorem: A closed
  set in a second countable space can be written as the union of a countable set and a perfect set.

## Implementation Notes

We do not require perfect sets to be nonempty, a condition which is often part of
the definition of perfect. We include an extra definition `perf_nonempty`, which bundles
these two conditions.

We define a nonstandard predicate, `preperfect`, which drops the closed-ness requirement
from the definition of perfect. In T1 spaces, this is equivalent to having a perfect closure,
see `preperfect_iff_perfect_closure`.

## References

* [kechris1995] (Chapter 6)

## Tags

accumulation point, perfect set, Cantor-Bendixson.

-/

section

open_locale topological_space filter
open topological_space filter set

variables {α : Type*} [topological_space α]

/-- If `x` is an accumulation point of a set `C` and `U` is a neighborhood of `x`,
then `x` is an accumulation point of `U ∩ C`. -/
theorem acc_pt.nhd_inter {x : α} {C U: set α} (h_acc : acc_pt x (𝓟 C)) (hU : U ∈ 𝓝 x) :
  acc_pt x (𝓟 (U ∩ C)) :=
begin
  have : 𝓝[≠] x ≤ 𝓟 U,
  { rw le_principal_iff,
    exact mem_nhds_within_of_mem_nhds hU, },
  rw [acc_pt, ← inf_principal, ← inf_assoc, inf_of_le_left this],
  exact h_acc,
end

/-- A set `C` is preperfect if all of its points are accumulation points of itself.
If `C` is nonempty, this is equivalent to the closure of `C` being perfect.
See `preperfect_iff_closure_perfect`.-/
--Note : This is my own term, feel free to suggest a better one :P
def preperfect (C : set α) : Prop := ∀ x ∈ C, acc_pt x (𝓟 C)

/-- A set `C` is called perfect if it is closed and all of its
points are accumulation points of itself.
Note that we do not require `C` to be nonempty as is common,
but see `perf_nonempty`.-/
structure perfect (C : set α) : Prop :=
  (closed : is_closed C)
  (acc : preperfect C)

/-- A set is called nonempty perfect if it is closed, nonempty, and
all of its points are accumulation points of itself.-/
structure perf_nonempty (C : set α) extends perfect C : Prop :=
  (nonempty : C.nonempty)

lemma preperfect_iff_nhds {C : set α} : preperfect C ↔ ∀ x ∈ C, ∀ U ∈ 𝓝 x, ∃ y ∈ U ∩ C, y ≠ x
  := by simp only[preperfect, acc_pt_iff_nhds]

/-- The intersection of a preperfect set and an open set is preperfect-/
theorem preperfect.open_inter {C U : set α} (hC : preperfect C) (hU : is_open U) :
  preperfect (U ∩ C) :=
begin
  rintros x ⟨xU, xC⟩,
  apply (hC _ xC).nhd_inter,
  exact hU.mem_nhds xU,
end

/-- The closure of a preperfect set is perfect.
For a converse, see `preperfect_iff_perfect_closure`-/
theorem preperfect.perfect_closure {C : set α} (hC : preperfect C) :
  perfect (closure C) :=
begin
  split, {apply is_closed_closure},
  intros x hx,
  by_cases h : x ∈ C; apply acc_pt.mono _ (principal_mono.mpr subset_closure),
  { exact hC _ h },
  have : {x}ᶜ ∩ C = C := by simp[h],
  rw [acc_pt, nhds_within, inf_assoc, inf_principal, this],
  rw [closure_eq_cluster_pts] at hx,
  exact hx,
end

/-- In a T1 space, being preperfect is equivalent to having perfect closure.-/
theorem preperfect_iff_perfect_closure [t1_space α] {C : set α} :
  preperfect C ↔ perfect (closure C) :=
begin
  split; intro h, {exact h.perfect_closure},
  intros x xC,
  have H := h.acc _ (subset_closure xC),
  rw acc_pt_iff_frequently at *,
  have : ∀ y , y ≠ x ∧ y ∈ closure C → ∃ᶠ z in 𝓝 y, z ≠ x ∧ z ∈ C,
  { rintros y ⟨hyx, yC⟩,
    simp only [← mem_compl_singleton_iff, @and_comm _ (_ ∈ C) , ← frequently_nhds_within_iff,
      hyx.nhds_within_compl_singleton, ← mem_closure_iff_frequently],
    exact yC, },
  rw ← frequently_frequently_nhds,
  exact H.mono this,
end

theorem perfect.closure_nhd_inter {C U: set α} (hC : perfect C) (x : α) (xC : x ∈ C) (xU : x ∈ U)
  (Uop : is_open U) : perf_nonempty (closure (U ∩ C)) :=
begin
  split,
  { apply preperfect.perfect_closure,
    exact (hC.acc).open_inter Uop, },
  apply nonempty.mono subset_closure,
  exact ⟨x,⟨xU,xC⟩⟩,
end

/-- Given a perfect nonempty set in a T2.5 space, we can find two disjoint perfect subsets
This is the main inductive step in the proof of the Cantor-Bendixson Theorem-/
lemma perf_nonempty.splitting [t2_5_space α] {C : set α} (hC : perf_nonempty C) :
  ∃ C₀ C₁ : set α, (perf_nonempty C₀ ∧ C₀ ⊆ C) ∧ (perf_nonempty C₁ ∧ C₁ ⊆ C) ∧ disjoint C₀ C₁ :=
begin
  cases hC.nonempty with y yC,
  obtain ⟨x, xC, hxy⟩ : ∃ x ∈ C, x ≠ y,
  { have := hC.acc _ yC,
    rw acc_pt_iff_nhds at this,
    rcases this univ (univ_mem) with ⟨x,xC,hxy⟩,
    exact ⟨x,xC.2,hxy⟩, },
  obtain ⟨U, xU, Uop, V, yV, Vop, hUV⟩ := exists_open_nhds_disjoint_closure hxy,
  use [closure (U ∩ C), closure (V ∩ C)],
  split,
  { split, { apply hC.closure_nhd_inter x xC xU Uop, },
    rw hC.closed.closure_subset_iff,
    apply inter_subset_right, },
  split,
  { split, { apply hC.closure_nhd_inter y yC yV Vop, },
    rw hC.closed.closure_subset_iff,
    apply inter_subset_right, },
  apply disjoint.mono _ _ hUV; apply closure_mono; apply inter_subset_left,
end

section kernel

/-- The Cantor-Bendixson Theorem: Any closed subset of a second countable space
can be written as the union of a countable set and a perfect set.-/
theorem ctble_union_perfect_of_closed [second_countable_topology α] {C : set α}
  (hclosed : is_closed C) : ∃ V D : set α, (V.countable) ∧ (perfect D) ∧ (C = V ∪ D) :=
begin
  have := topological_space.exists_countable_basis α,
  rcases this with ⟨b,bct,bnontrivial,bbasis⟩,
  let v := {U ∈ b | (U ∩ C).countable},
  let V := ⋃ U ∈ v, U,
  let D := C \ V,
  have Vct : (V ∩ C).countable,
  { simp[V,Union_inter],
    apply set.countable.bUnion,
    { apply @set.countable.mono _ _ b,
      { apply set.inter_subset_left, },
      exact bct, },
    apply set.inter_subset_right, },
  use [V ∩ C,D],
  refine ⟨Vct, ⟨_, _⟩, _⟩,
  { apply hclosed.sdiff,
    apply is_open_bUnion,
    rintros U ⟨Ub,-⟩,
    exact is_topological_basis.is_open bbasis Ub, },
  { rw preperfect_iff_nhds,
    intros x xD E xE,
    have : ¬ (E ∩ D).countable,
    { intro h,
      obtain ⟨U,hUb,xU,hU⟩ : ∃ U ∈ b, x ∈ U ∧ U ⊆ E,
      { exact (is_topological_basis.mem_nhds_iff bbasis).mp xE, },
      have : U ∈ v,
      { use hUb,
        dsimp,
        apply @countable.mono _ _ ((E ∩ D) ∪ (V ∩ C)),
        { rintros y ⟨yU,yC⟩,
          by_cases y ∈ V,
          { right,
            exact ⟨h,yC⟩, },
          left,
          split,
          { exact hU yU, },
          exact ⟨yC, h⟩, },
        apply countable.union h Vct, },
      apply xD.2,
      exact mem_bUnion this xU, },
    by_contradiction,
    push_neg at h,
    apply this,
    have : E ∩ D ⊆ {x}, {exact h},
    apply countable.mono this,
    apply set.countable_singleton, },
  dsimp[D],
  rw[inter_comm,inter_union_diff],
end

/-- Any uncountable closed set in a second countable space contains a nonempty perfect subset.-/
theorem perf_nonempty_of_closed_unctble [second_countable_topology α] {C : set α}
  (hclosed : is_closed C) (hunc : ¬ C.countable) : ∃ D : set α, (perf_nonempty D) ∧ (D ⊆ C) :=
begin
  rcases ctble_union_perfect_of_closed hclosed with ⟨V,D,Vct,Dperf,VD⟩,
  use D,
  split,
  { split, swap,
    { rw ← ne_empty_iff_nonempty,
      by_contradiction,
      rw [h, union_empty] at VD,
      rw VD at hunc,
      contradiction, },
    exact Dperf, },
  rw VD,
  apply subset_union_right,
end

end kernel

end
