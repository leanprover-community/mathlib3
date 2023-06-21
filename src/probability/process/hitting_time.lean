/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
import probability.process.stopping

/-!
# Hitting time

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given a stochastic process, the hitting time provides the first time the process ``hits'' some
subset of the state space. The hitting time is a stopping time in the case that the time index is
discrete and the process is adapted (this is true in a far more general setting however we have
only proved it for the discrete case so far).

## Main definition

* `measure_theory.hitting`: the hitting time of a stochastic process

## Main results

* `measure_theory.hitting_is_stopping_time`: a discrete hitting time of an adapted process is a
  stopping time

## Implementation notes

In the definition of the hitting time, we bound the hitting time by an upper and lower bound.
This is to ensure that our result is meaningful in the case we are taking the infimum of an
empty set or the infimum of a set which is unbounded from below. With this, we can talk about
hitting times indexed by the natural numbers or the reals. By taking the bounds to be
`⊤` and `⊥`, we obtain the standard definition in the case that the index is `ℕ∞` or `ℝ≥0∞`.

-/

open filter order topological_space
open_locale classical measure_theory nnreal ennreal topology big_operators

namespace measure_theory

variables {Ω β ι : Type*} {m : measurable_space Ω}

/-- Hitting time: given a stochastic process `u` and a set `s`, `hitting u s n m` is the first time
`u` is in `s` after time `n` and before time `m` (if `u` does not hit `s` after time `n` and
before `m` then the hitting time is simply `m`).

The hitting time is a stopping time if the process is adapted and discrete. -/
noncomputable def hitting [preorder ι] [has_Inf ι] (u : ι → Ω → β) (s : set β) (n m : ι) : Ω → ι :=
λ x, if ∃ j ∈ set.Icc n m, u j x ∈ s then Inf (set.Icc n m ∩ {i : ι | u i x ∈ s}) else m

section inequalities

variables [conditionally_complete_linear_order ι] {u : ι → Ω → β} {s : set β} {n i : ι} {ω : Ω}

/-- This lemma is strictly weaker than `hitting_of_le`. -/
lemma hitting_of_lt {m : ι} (h : m < n) : hitting u s n m ω = m :=
begin
  simp_rw [hitting],
  have h_not : ¬ ∃ (j : ι) (H : j ∈ set.Icc n m), u j ω ∈ s,
  { push_neg,
    intro j,
    rw set.Icc_eq_empty_of_lt h,
    simp only [set.mem_empty_iff_false, is_empty.forall_iff], },
  simp only [h_not, if_false],
end

lemma hitting_le {m : ι} (ω : Ω) : hitting u s n m ω ≤ m :=
begin
  cases le_or_lt n m with h_le h_lt,
  { simp only [hitting],
    split_ifs,
    { obtain ⟨j, hj₁, hj₂⟩ := h,
      exact (cInf_le (bdd_below.inter_of_left bdd_below_Icc) (set.mem_inter hj₁ hj₂)).trans hj₁.2 },
    { exact le_rfl }, },
  { rw hitting_of_lt h_lt, },
end

lemma not_mem_of_lt_hitting {m k : ι}
  (hk₁ : k < hitting u s n m ω) (hk₂ : n ≤ k) :
  u k ω ∉ s :=
begin
  classical,
  intro h,
  have hexists : ∃ j ∈ set.Icc n m, u j ω ∈ s,
  refine ⟨k, ⟨hk₂, le_trans hk₁.le $ hitting_le _⟩, h⟩,
  refine not_le.2 hk₁ _,
  simp_rw [hitting, if_pos hexists],
  exact cInf_le bdd_below_Icc.inter_of_left ⟨⟨hk₂, le_trans hk₁.le $ hitting_le _⟩, h⟩,
end

lemma hitting_eq_end_iff {m : ι} :
  hitting u s n m ω = m ↔ (∃ j ∈ set.Icc n m, u j ω ∈ s) →
    Inf (set.Icc n m ∩ {i : ι | u i ω ∈ s}) = m :=
by rw [hitting, ite_eq_right_iff]

lemma hitting_of_le {m : ι} (hmn : m ≤ n) :
  hitting u s n m ω = m :=
begin
  obtain (rfl | h) := le_iff_eq_or_lt.1 hmn,
  { simp only [hitting, set.Icc_self, ite_eq_right_iff, set.mem_Icc, exists_prop,
      forall_exists_index, and_imp],
    intros i hi₁ hi₂ hi,
    rw [set.inter_eq_left_iff_subset.2, cInf_singleton],
    exact set.singleton_subset_iff.2 (le_antisymm hi₂ hi₁ ▸ hi) },
  { exact hitting_of_lt h }
end

lemma le_hitting {m : ι} (hnm : n ≤ m) (ω : Ω) : n ≤ hitting u s n m ω :=
begin
  simp only [hitting],
  split_ifs,
  { refine le_cInf _ (λ b hb, _),
    { obtain ⟨k, hk_Icc, hk_s⟩ := h,
      exact ⟨k, hk_Icc, hk_s⟩, },
    { rw set.mem_inter_iff at hb,
      exact hb.1.1, }, },
  { exact hnm },
end

lemma le_hitting_of_exists {m : ι} (h_exists : ∃ j ∈ set.Icc n m, u j ω ∈ s) :
  n ≤ hitting u s n m ω :=
begin
  refine le_hitting _ ω,
  by_contra,
  rw set.Icc_eq_empty_of_lt (not_le.mp h) at h_exists,
  simpa using h_exists,
end

lemma hitting_mem_Icc {m : ι} (hnm : n ≤ m) (ω : Ω) : hitting u s n m ω ∈ set.Icc n m :=
⟨le_hitting hnm ω, hitting_le ω⟩

lemma hitting_mem_set [is_well_order ι (<)] {m : ι} (h_exists : ∃ j ∈ set.Icc n m, u j ω ∈ s) :
  u (hitting u s n m ω) ω ∈ s :=
begin
  simp_rw [hitting, if_pos h_exists],
  have h_nonempty : (set.Icc n m ∩ {i : ι | u i ω ∈ s}).nonempty,
  { obtain ⟨k, hk₁, hk₂⟩ := h_exists,
    exact ⟨k, set.mem_inter hk₁ hk₂⟩, },
  have h_mem := Inf_mem h_nonempty,
  rw [set.mem_inter_iff] at h_mem,
  exact h_mem.2,
end

lemma hitting_mem_set_of_hitting_lt [is_well_order ι (<)] {m : ι}
  (hl : hitting u s n m ω < m) :
  u (hitting u s n m ω) ω ∈ s :=
begin
  by_cases h : ∃ j ∈ set.Icc n m, u j ω ∈ s,
  { exact hitting_mem_set h },
  { simp_rw [hitting, if_neg h] at hl,
    exact false.elim (hl.ne rfl) }
end

lemma hitting_le_of_mem {m : ι} (hin : n ≤ i) (him : i ≤ m) (his : u i ω ∈ s) :
  hitting u s n m ω ≤ i :=
begin
  have h_exists : ∃ k ∈ set.Icc n m, u k ω ∈ s := ⟨i, ⟨hin, him⟩, his⟩,
  simp_rw [hitting, if_pos h_exists],
  exact cInf_le (bdd_below.inter_of_left bdd_below_Icc) (set.mem_inter ⟨hin, him⟩ his),
end

lemma hitting_le_iff_of_exists [is_well_order ι (<)] {m : ι}
  (h_exists : ∃ j ∈ set.Icc n m, u j ω ∈ s) :
  hitting u s n m ω ≤ i ↔ ∃ j ∈ set.Icc n i, u j ω ∈ s :=
begin
  split; intro h',
  { exact ⟨hitting u s n m ω, ⟨le_hitting_of_exists h_exists, h'⟩, hitting_mem_set h_exists⟩, },
  { have h'' : ∃ k ∈ set.Icc n (min m i), u k ω ∈ s,
    { obtain ⟨k₁, hk₁_mem, hk₁_s⟩ := h_exists,
      obtain ⟨k₂, hk₂_mem, hk₂_s⟩ := h',
      refine ⟨min k₁ k₂, ⟨le_min hk₁_mem.1 hk₂_mem.1, min_le_min hk₁_mem.2 hk₂_mem.2⟩, _⟩,
      exact min_rec' (λ j, u j ω ∈ s) hk₁_s hk₂_s, },
    obtain ⟨k, hk₁, hk₂⟩ := h'',
    refine le_trans _ (hk₁.2.trans (min_le_right _ _)),
    exact hitting_le_of_mem hk₁.1 (hk₁.2.trans (min_le_left _ _)) hk₂, },
end

lemma hitting_le_iff_of_lt [is_well_order ι (<)] {m : ι} (i : ι) (hi : i < m) :
  hitting u s n m ω ≤ i ↔ ∃ j ∈ set.Icc n i, u j ω ∈ s :=
begin
  by_cases h_exists : ∃ j ∈ set.Icc n m, u j ω ∈ s,
  { rw hitting_le_iff_of_exists h_exists, },
  { simp_rw [hitting, if_neg h_exists],
    push_neg at h_exists,
    simp only [not_le.mpr hi, set.mem_Icc, false_iff, not_exists, and_imp],
    exact λ k hkn hki, h_exists k ⟨hkn, hki.trans hi.le⟩, },
end

lemma hitting_lt_iff [is_well_order ι (<)] {m : ι} (i : ι) (hi : i ≤ m) :
  hitting u s n m ω < i ↔ ∃ j ∈ set.Ico n i, u j ω ∈ s :=
begin
  split; intro h',
  { have h : ∃ j ∈ set.Icc n m, u j ω ∈ s,
    { by_contra,
      simp_rw [hitting, if_neg h, ← not_le] at h',
      exact h' hi, },
    exact ⟨hitting u s n m ω, ⟨le_hitting_of_exists h, h'⟩, hitting_mem_set h⟩, },
  { obtain ⟨k, hk₁, hk₂⟩ := h',
    refine lt_of_le_of_lt _ hk₁.2,
    exact hitting_le_of_mem hk₁.1 (hk₁.2.le.trans hi) hk₂, },
end

lemma hitting_eq_hitting_of_exists
  {m₁ m₂ : ι} (h : m₁ ≤ m₂) (h' : ∃ j ∈ set.Icc n m₁, u j ω ∈ s) :
  hitting u s n m₁ ω = hitting u s n m₂ ω :=
begin
  simp only [hitting, if_pos h'],
  obtain ⟨j, hj₁, hj₂⟩ := h',
  rw if_pos,
  { refine le_antisymm _ (cInf_le_cInf bdd_below_Icc.inter_of_left ⟨j, hj₁, hj₂⟩
      (set.inter_subset_inter_left _ (set.Icc_subset_Icc_right h))),
    refine le_cInf ⟨j, set.Icc_subset_Icc_right h hj₁, hj₂⟩ (λ i hi, _),
    by_cases hi' : i ≤ m₁,
    { exact cInf_le bdd_below_Icc.inter_of_left ⟨⟨hi.1.1, hi'⟩, hi.2⟩ },
    { exact ((cInf_le bdd_below_Icc.inter_of_left ⟨hj₁, hj₂⟩).trans (hj₁.2.trans le_rfl)).trans
        (le_of_lt (not_le.1 hi')) } },
  exact ⟨j, ⟨hj₁.1, hj₁.2.trans h⟩, hj₂⟩,
end

lemma hitting_mono {m₁ m₂ : ι} (hm : m₁ ≤ m₂) :
  hitting u s n m₁ ω ≤ hitting u s n m₂ ω :=
begin
  by_cases h : ∃ j ∈ set.Icc n m₁, u j ω ∈ s,
  { exact (hitting_eq_hitting_of_exists hm h).le },
  { simp_rw [hitting, if_neg h],
    split_ifs with h',
    { obtain ⟨j, hj₁, hj₂⟩ := h',
      refine le_cInf ⟨j, hj₁, hj₂⟩ _,
      by_contra hneg, push_neg at hneg,
      obtain ⟨i, hi₁, hi₂⟩ := hneg,
      exact h ⟨i, ⟨hi₁.1.1, hi₂.le⟩, hi₁.2⟩ },
    { exact hm } }
end

end inequalities

/-- A discrete hitting time is a stopping time. -/
lemma hitting_is_stopping_time
  [conditionally_complete_linear_order ι] [is_well_order ι (<)] [countable ι]
  [topological_space β] [pseudo_metrizable_space β] [measurable_space β] [borel_space β]
  {f : filtration ι m} {u : ι → Ω → β} {s : set β} {n n' : ι}
  (hu : adapted f u) (hs : measurable_set s) :
  is_stopping_time f (hitting u s n n') :=
begin
  intro i,
  cases le_or_lt n' i with hi hi,
  { have h_le : ∀ ω, hitting u s n n' ω ≤ i := λ x, (hitting_le x).trans hi,
    simp [h_le], },
  { have h_set_eq_Union : {ω | hitting u s n n' ω ≤ i} = ⋃ j ∈ set.Icc n i, u j ⁻¹' s,
    { ext x,
      rw [set.mem_set_of_eq, hitting_le_iff_of_lt _ hi],
      simp only [set.mem_Icc, exists_prop, set.mem_Union, set.mem_preimage], },
    rw h_set_eq_Union,
    exact measurable_set.Union (λ j, measurable_set.Union $
      λ hj, f.mono hj.2 _ ((hu j).measurable hs)) }
end

lemma stopped_value_hitting_mem [conditionally_complete_linear_order ι] [is_well_order ι (<)]
  {u : ι → Ω → β} {s : set β} {n m : ι} {ω : Ω} (h : ∃ j ∈ set.Icc n m, u j ω ∈ s) :
  stopped_value u (hitting u s n m) ω ∈ s :=
begin
  simp only [stopped_value, hitting, if_pos h],
  obtain ⟨j, hj₁, hj₂⟩ := h,
  have : Inf (set.Icc n m ∩ {i | u i ω ∈ s}) ∈ set.Icc n m ∩ {i | u i ω ∈ s} :=
    Inf_mem (set.nonempty_of_mem ⟨hj₁, hj₂⟩),
  exact this.2,
end

/-- The hitting time of a discrete process with the starting time indexed by a stopping time
is a stopping time. -/
lemma is_stopping_time_hitting_is_stopping_time
  [conditionally_complete_linear_order ι] [is_well_order ι (<)] [countable ι]
  [topological_space ι] [order_topology ι] [first_countable_topology ι]
  [topological_space β] [pseudo_metrizable_space β] [measurable_space β] [borel_space β]
  {f : filtration ι m} {u : ι → Ω → β} {τ : Ω → ι} (hτ : is_stopping_time f τ)
  {N : ι} (hτbdd : ∀ x, τ x ≤ N) {s : set β} (hs : measurable_set s) (hf : adapted f u) :
  is_stopping_time f (λ x, hitting u s (τ x) N x) :=
begin
  intro n,
  have h₁ : {x | hitting u s (τ x) N x ≤ n} =
    (⋃ i ≤ n, {x | τ x = i} ∩ {x | hitting u s i N x ≤ n}) ∪
    (⋃ i > n, {x | τ x = i} ∩ {x | hitting u s i N x ≤ n}),
  { ext x,
    simp [← exists_or_distrib, ← or_and_distrib_right, le_or_lt] },
  have h₂ : (⋃ i > n, {x | τ x = i} ∩ {x | hitting u s i N x ≤ n}) = ∅,
  { ext x,
    simp only [gt_iff_lt, set.mem_Union, set.mem_inter_iff, set.mem_set_of_eq,
      exists_prop, set.mem_empty_iff_false, iff_false, not_exists, not_and, not_le],
    rintro m hm rfl,
    exact lt_of_lt_of_le hm (le_hitting (hτbdd _) _) },
  rw [h₁, h₂, set.union_empty],
  exact measurable_set.Union (λ i, measurable_set.Union
    (λ hi, (f.mono hi _ (hτ.measurable_set_eq i)).inter (hitting_is_stopping_time hf hs n))),
end

section complete_lattice

variables [complete_lattice ι] {u : ι → Ω → β} {s : set β} {f : filtration ι m}

lemma hitting_eq_Inf (ω : Ω) : hitting u s ⊥ ⊤ ω = Inf {i : ι | u i ω ∈ s} :=
begin
  simp only [hitting, set.mem_Icc, bot_le, le_top, and_self, exists_true_left, set.Icc_bot,
    set.Iic_top, set.univ_inter, ite_eq_left_iff, not_exists],
  intro h_nmem_s,
  symmetry,
  rw Inf_eq_top,
  exact λ i hi_mem_s, absurd hi_mem_s (h_nmem_s i),
end

end complete_lattice

section conditionally_complete_linear_order_bot

variables [conditionally_complete_linear_order_bot ι] [is_well_order ι (<)]
variables {u : ι → Ω → β} {s : set β} {f : filtration ℕ m}

lemma hitting_bot_le_iff {i n : ι} {ω : Ω} (hx : ∃ j, j ≤ n ∧ u j ω ∈ s) :
  hitting u s ⊥ n ω ≤ i ↔ ∃ j ≤ i, u j ω ∈ s :=
begin
  cases lt_or_le i n with hi hi,
  { rw hitting_le_iff_of_lt _ hi,
    simp, },
  { simp only [(hitting_le ω).trans hi, true_iff],
    obtain ⟨j, hj₁, hj₂⟩ := hx,
    exact ⟨j, hj₁.trans hi, hj₂⟩, },
end

end conditionally_complete_linear_order_bot

end measure_theory
