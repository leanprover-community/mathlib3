/-
Copyright (c) 2022 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
-/
import topology.metric_space.polish
import topology.metric_space.cantor_scheme

/-!
# Perfect Sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define perfect subsets of a topological space, and prove some basic properties,
including a version of the Cantor-Bendixson Theorem.

## Main Definitions

* `perfect C`: A set `C` is perfect, meaning it is closed and every point of it
  is an accumulation point of itself.
* `set.scheme β α`: A `β`-scheme on `α`, a collection of subsets of `α` indexed by `list β`.
  Used to construct maps `(β → ℕ) → α` as limiting objects.

## Main Statements

* `perfect.splitting`: A perfect nonempty set contains two disjoint perfect nonempty subsets.
  The main inductive step in the construction of an embedding from the Cantor space to a
  perfect nonempty complete metric space.
* `exists_countable_union_perfect_of_is_closed`: One version of the **Cantor-Bendixson Theorem**:
  A closed set in a second countable space can be written as the union of a countable set and a
  perfect set.
* `perfect.exists_nat_bool_injection`: A perfect nonempty set in a complete metric space
  admits an embedding from the Cantor space.

## Implementation Notes

We do not require perfect sets to be nonempty.

We define a nonstandard predicate, `preperfect`, which drops the closed-ness requirement
from the definition of perfect. In T1 spaces, this is equivalent to having a perfect closure,
see `preperfect_iff_perfect_closure`.

## References

* [kechris1995] (Chapters 6-7)

## Tags

accumulation point, perfect set, cantor-bendixson.

-/

open_locale topology filter
open topological_space filter set

section basic

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
end basic

section cantor_inj_metric

open function
open_locale ennreal
variables {α : Type*} [metric_space α] {C : set α} (hC : perfect C) {ε : ℝ≥0∞}
include hC

private lemma perfect.small_diam_aux (ε_pos : 0 < ε) {x : α} (xC : x ∈ C) :
  let D := closure (emetric.ball x (ε / 2) ∩ C) in
  perfect D ∧ D.nonempty ∧ D ⊆ C ∧ emetric.diam D ≤ ε :=
begin
  have : x ∈ (emetric.ball x (ε / 2)),
  { apply emetric.mem_ball_self,
    rw ennreal.div_pos_iff,
    exact ⟨ne_of_gt ε_pos, by norm_num⟩, },
  have := hC.closure_nhds_inter x xC this emetric.is_open_ball,
  refine ⟨this.1, this.2, _, _⟩,
  { rw is_closed.closure_subset_iff hC.closed,
    apply inter_subset_right, },
  rw emetric.diam_closure,
  apply le_trans (emetric.diam_mono (inter_subset_left _ _)),
  convert emetric.diam_ball,
  rw [mul_comm, ennreal.div_mul_cancel]; norm_num,
end

variable (hnonempty : C.nonempty)
include hnonempty

/-- A refinement of `perfect.splitting` for metric spaces, where we also control
the diameter of the new perfect sets. -/
lemma perfect.small_diam_splitting (ε_pos : 0 < ε) : ∃ C₀ C₁ : set α,
  (perfect C₀ ∧ C₀.nonempty ∧ C₀ ⊆ C ∧ emetric.diam C₀ ≤ ε) ∧
  (perfect C₁ ∧ C₁.nonempty ∧ C₁ ⊆ C ∧ emetric.diam C₁ ≤ ε) ∧ disjoint C₀ C₁ :=
begin
  rcases hC.splitting hnonempty with ⟨D₀, D₁, ⟨perf0, non0, sub0⟩, ⟨perf1, non1, sub1⟩, hdisj⟩,
  cases non0 with x₀ hx₀,
  cases non1 with x₁ hx₁,
  rcases perf0.small_diam_aux ε_pos hx₀ with ⟨perf0', non0', sub0', diam0⟩,
  rcases perf1.small_diam_aux ε_pos hx₁ with ⟨perf1', non1', sub1', diam1⟩,
  refine ⟨closure (emetric.ball x₀ (ε / 2) ∩ D₀), closure (emetric.ball x₁ (ε / 2) ∩ D₁),
    ⟨perf0', non0', sub0'.trans sub0, diam0⟩, ⟨perf1', non1', sub1'.trans sub1, diam1⟩, _⟩,
  apply disjoint.mono _ _ hdisj; assumption,
end

open cantor_scheme

/-- Any nonempty perfect set in a complete metric space admits a continuous injection
from the cantor space, `ℕ → bool`. -/
theorem perfect.exists_nat_bool_injection [complete_space α] :
  ∃ f : (ℕ → bool) → α, (range f) ⊆ C ∧ continuous f ∧ injective f :=
begin
  obtain ⟨u, -, upos', hu⟩ := exists_seq_strict_anti_tendsto' (zero_lt_one' ℝ≥0∞),
  have upos := λ n, (upos' n).1,
  let P := subtype (λ E : set α, perfect E ∧ E.nonempty),
  choose C0 C1 h0 h1 hdisj using λ {C : set α} (hC : perfect C) (hnonempty : C.nonempty)
    {ε : ℝ≥0∞} (hε : 0 < ε), hC.small_diam_splitting hnonempty hε,
  let DP : list bool → P := λ l,
  begin
    induction l with a l ih, { exact ⟨C, ⟨hC, hnonempty⟩⟩ },
    cases a,
    { use C0 ih.property.1 ih.property.2 (upos l.length.succ),
      exact ⟨(h0 _ _ _).1, (h0 _ _ _).2.1⟩, },
    use C1 ih.property.1 ih.property.2 (upos l.length.succ),
    exact ⟨(h1 _ _ _).1, (h1 _ _ _).2.1⟩,
  end,
  let D : list bool → set α := λ l, (DP l).val,
  have hanti : closure_antitone D,
  { refine antitone.closure_antitone _ (λ l, (DP l).property.1.closed),
    intros l a,
    cases a,
    { exact (h0 _ _ _).2.2.1, },
    exact (h1 _ _ _).2.2.1, },
  have hdiam : vanishing_diam D,
  { intro x,
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu,
    { simp },
    rw eventually_at_top,
    refine ⟨1, λ m (hm : 1 ≤ m), _⟩,
    rw nat.one_le_iff_ne_zero at hm,
    rcases nat.exists_eq_succ_of_ne_zero hm with ⟨n, rfl⟩,
    dsimp,
    cases (x n),
    { convert (h0 _ _ _).2.2.2,
      rw pi_nat.res_length },
    convert (h1 _ _ _).2.2.2,
    rw pi_nat.res_length, },
  have hdisj' : cantor_scheme.disjoint D,
  { rintros l (a | a) (b | b) hab; try { contradiction },
    { exact hdisj _ _ _, },
    exact (hdisj _ _ _).symm, },
  have hdom : ∀ {x : ℕ → bool}, x ∈ (induced_map D).1 := λ x,
    by simp [hanti.map_of_vanishing_diam hdiam (λ l, (DP l).property.2)],
  refine ⟨λ x, (induced_map D).2 ⟨x, hdom⟩, _, _, _⟩,
  { rintros y ⟨x, rfl⟩,
    exact map_mem ⟨_, hdom⟩ 0, },
  { continuity,
    exact hdiam.map_continuous, },
  intros x y hxy,
  simpa only [← subtype.val_inj] using hdisj'.map_injective hxy,
end

end cantor_inj_metric

/-
--set_option pp.implicit true
theorem is_closed.exists_nat_bool_injection_of_uncountable {α : Type*}
  [topological_space α] [polish_space α] {C : set α} (hC : is_closed C) (hunc : ¬ C.countable) :
  ∃ f : (ℕ → bool) → α, (range f) ⊆ C ∧ continuous f ∧ function.injective f :=
begin
  letI := upgrade_polish_space α,
  obtain ⟨D, hD, Dnonempty, hDC⟩ := exists_perfect_nonempty_of_is_closed_of_not_countable hC hunc,
  obtain ⟨f, hf⟩ := hD.exists_nat_bool_injection Dnonempty,
end -/
