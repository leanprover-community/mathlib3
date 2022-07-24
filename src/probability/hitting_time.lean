/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
import probability.stopping

/-!
# Hitting time

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
`⊤` and `⊥`, we obtain the standard definition in the case that the index is `with_top ℕ` or `ℝ≥0∞`.

-/

open filter order topological_space
open_locale classical measure_theory nnreal ennreal topological_space big_operators

namespace measure_theory

variables {α β ι : Type*} {m : measurable_space α}

/-- Hitting time: given a stochastic process `u` and a set `s`, `hitting u s n m` is the first time
`u` is in `s` after time `n` and before time `m` (if `u` does not hit `s` after time `n` and
before `m` then the hitting time is simply `m`).

The hitting time is a stopping time if the process is adapted and discrete. -/
noncomputable def hitting [preorder ι] [has_Inf ι] (u : ι → α → β) (s : set β) (n m : ι) : α → ι :=
λ x, if ∃ j ∈ set.Icc n m, u j x ∈ s then Inf (set.Icc n m ∩ {i : ι | u i x ∈ s}) else m

section inequalities

variables [conditionally_complete_linear_order ι] {u : ι → α → β} {s : set β} {n i : ι} {x : α}

lemma hitting_of_lt {m : ι} (h : m < n) : hitting u s n m x = m :=
begin
  simp_rw [hitting],
  have h_not : ¬∃ (j : ι) (H : j ∈ set.Icc n m), u j x ∈ s,
  { push_neg,
    intro j,
    rw set.Icc_eq_empty_of_lt h,
    simp only [set.mem_empty_eq, is_empty.forall_iff], },
  simp only [h_not, if_false],
end

lemma hitting_le {m : ι} (x : α) : hitting u s n m x ≤ m :=
begin
  cases le_or_lt n m with h_le h_lt,
  { simp only [hitting],
    split_ifs,
    { obtain ⟨j, hj₁, hj₂⟩ := h,
      exact (cInf_le (bdd_below.inter_of_left bdd_below_Icc) (set.mem_inter hj₁ hj₂)).trans hj₁.2 },
    { exact le_rfl }, },
  { rw hitting_of_lt h_lt, },
end

lemma le_hitting {m : ι} (hnm : n ≤ m) (x : α) : n ≤ hitting u s n m x :=
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

lemma le_hitting_of_exists {m : ι} (h_exists : ∃ j ∈ set.Icc n m, u j x ∈ s) :
  n ≤ hitting u s n m x :=
begin
  refine le_hitting _ x,
  by_contra,
  rw set.Icc_eq_empty_of_lt (not_le.mp h) at h_exists,
  simpa using h_exists,
end

lemma hitting_mem_Icc {m : ι} (hnm : n ≤ m) (x : α) : hitting u s n m x ∈ set.Icc n m :=
⟨le_hitting hnm x, hitting_le x⟩

lemma hitting_mem_set [is_well_order ι (<)] {m : ι} (h_exists : ∃ j ∈ set.Icc n m, u j x ∈ s) :
  u (hitting u s n m x) x ∈ s :=
begin
  simp_rw [hitting, if_pos h_exists],
  have h_nonempty : (set.Icc n m ∩ {i : ι | u i x ∈ s}).nonempty,
  { obtain ⟨k, hk₁, hk₂⟩ := h_exists,
    exact ⟨k, set.mem_inter hk₁ hk₂⟩, },
  have h_mem := Inf_mem h_nonempty,
  rw [set.mem_inter_iff] at h_mem,
  exact h_mem.2,
end

lemma hitting_le_of_mem {m : ι} (hin : n ≤ i) (him : i ≤ m) (his : u i x ∈ s) :
  hitting u s n m x ≤ i :=
begin
  have h_exists : ∃ k ∈ set.Icc n m, u k x ∈ s := ⟨i, ⟨hin, him⟩, his⟩,
  simp_rw [hitting, if_pos h_exists],
  exact cInf_le (bdd_below.inter_of_left bdd_below_Icc) (set.mem_inter ⟨hin, him⟩ his),
end

lemma hitting_le_iff_of_exists [is_well_order ι (<)] {m : ι}
  (h_exists : ∃ j ∈ set.Icc n m, u j x ∈ s) :
  hitting u s n m x ≤ i ↔ ∃ j ∈ set.Icc n i, u j x ∈ s :=
begin
  split; intro h',
  { exact ⟨hitting u s n m x, ⟨le_hitting_of_exists h_exists, h'⟩, hitting_mem_set h_exists⟩, },
  { have h'' : ∃ k ∈ set.Icc n (min m i), u k x ∈ s,
    { obtain ⟨k₁, hk₁_mem, hk₁_s⟩ := h_exists,
      obtain ⟨k₂, hk₂_mem, hk₂_s⟩ := h',
      refine ⟨min k₁ k₂, ⟨le_min hk₁_mem.1 hk₂_mem.1, min_le_min hk₁_mem.2 hk₂_mem.2⟩, _⟩,
      exact min_rec' (λ j, u j x ∈ s) hk₁_s hk₂_s, },
    obtain ⟨k, hk₁, hk₂⟩ := h'',
    refine le_trans _ (hk₁.2.trans (min_le_right _ _)),
    exact hitting_le_of_mem hk₁.1 (hk₁.2.trans (min_le_left _ _)) hk₂, },
end

lemma hitting_le_iff_of_lt [is_well_order ι (<)] {m : ι} (i : ι) (hi : i < m) :
  hitting u s n m x ≤ i ↔ ∃ j ∈ set.Icc n i, u j x ∈ s :=
begin
  by_cases h_exists : ∃ j ∈ set.Icc n m, u j x ∈ s,
  { rw hitting_le_iff_of_exists h_exists, },
  { simp_rw [hitting, if_neg h_exists],
    push_neg at h_exists,
    simp only [not_le.mpr hi, set.mem_Icc, false_iff, not_exists, and_imp],
    exact λ k hkn hki, h_exists k ⟨hkn, hki.trans hi.le⟩, },
end

lemma hitting_lt_iff [is_well_order ι (<)] {m : ι} (i : ι) (hi : i ≤ m) :
  hitting u s n m x < i ↔ ∃ j ∈ set.Ico n i, u j x ∈ s :=
begin
  split; intro h',
  { have h : ∃ j ∈ set.Icc n m, u j x ∈ s,
    { by_contra,
      simp_rw [hitting, if_neg h, ← not_le] at h',
      exact h' hi, },
    exact ⟨hitting u s n m x, ⟨le_hitting_of_exists h, h'⟩, hitting_mem_set h⟩, },
  { obtain ⟨k, hk₁, hk₂⟩ := h',
    refine lt_of_le_of_lt _ hk₁.2,
    exact hitting_le_of_mem hk₁.1 (hk₁.2.le.trans hi) hk₂, },
end

end inequalities

/-- A discrete hitting time is a stopping time. -/
lemma hitting_is_stopping_time
  [conditionally_complete_linear_order ι] [is_well_order ι (<)] [encodable ι]
  [topological_space β] [pseudo_metrizable_space β] [measurable_space β] [borel_space β]
  {f : filtration ι m} {u : ι → α → β} {s : set β} {n n' : ι}
  (hu : adapted f u) (hs : measurable_set s) :
  is_stopping_time f (hitting u s n n') :=
begin
  intro i,
  cases le_or_lt n' i with hi hi,
  { have h_le : ∀ x, hitting u s n n' x ≤ i := λ x, (hitting_le x).trans hi,
    simp [h_le], },
  { have h_set_eq_Union : {x | hitting u s n n' x ≤ i} = ⋃ j ∈ set.Icc n i, u j ⁻¹' s,
    { ext x,
      rw [set.mem_set_of_eq, hitting_le_iff_of_lt _ hi],
      simp only [set.mem_Icc, exists_prop, set.mem_Union, set.mem_preimage], },
    rw h_set_eq_Union,
    exact measurable_set.Union (λ j, measurable_set.Union_Prop $
      λ hj, f.mono hj.2 _ ((hu j).measurable hs)) }
end

lemma stopped_value_hitting_mem [conditionally_complete_linear_order ι] [is_well_order ι (<)]
  {u : ι → α → β} {s : set β} {n m : ι} {x : α} (h : ∃ j ∈ set.Icc n m, u j x ∈ s) :
  stopped_value u (hitting u s n m) x ∈ s :=
begin
  simp only [stopped_value, hitting, if_pos h],
  obtain ⟨j, hj₁, hj₂⟩ := h,
  have : Inf (set.Icc n m ∩ {i | u i x ∈ s}) ∈ set.Icc n m ∩ {i | u i x ∈ s} :=
    Inf_mem (set.nonempty_of_mem ⟨hj₁, hj₂⟩),
  exact this.2,
end

section complete_lattice

variables [complete_lattice ι] {u : ι → α → β} {s : set β} {f : filtration ι m}

lemma hitting_eq_Inf (x : α) : hitting u s ⊥ ⊤ x = Inf {i : ι | u i x ∈ s} :=
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
variables {u : ι → α → β} {s : set β} {f : filtration ℕ m}

lemma hitting_bot_le_iff {i n : ι} {x : α} (hx : ∃ j, j ≤ n ∧ u j x ∈ s) :
  hitting u s ⊥ n x ≤ i ↔ ∃ j ≤ i, u j x ∈ s :=
begin
  cases lt_or_le i n with hi hi,
  { rw hitting_le_iff_of_lt _ hi,
    simp, },
  { simp only [(hitting_le x).trans hi, true_iff],
    obtain ⟨j, hj₁, hj₂⟩ := hx,
    exact ⟨j, hj₁.trans hi, hj₂⟩, },
end

end conditionally_complete_linear_order_bot

end measure_theory
