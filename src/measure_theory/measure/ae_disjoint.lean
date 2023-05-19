/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import measure_theory.measure.measure_space_def

/-!
# Almost everywhere disjoint sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We say that sets `s` and `t` are `μ`-a.e. disjoint (see `measure_theory.ae_disjoint`) if their
intersection has measure zero. This assumption can be used instead of `disjoint` in most theorems in
measure theory.
-/

open set function

namespace measure_theory

variables {ι α : Type*} {m : measurable_space α} (μ : measure α)

/-- Two sets are said to be `μ`-a.e. disjoint if their intersection has measure zero. -/
def ae_disjoint (s t : set α) := μ (s ∩ t) = 0

variables {μ} {s t u v : set α}

/-- If `s : ι → set α` is a countable family of pairwise a.e. disjoint sets, then there exists a
family of measurable null sets `t i` such that `s i \ t i` are pairwise disjoint. -/
lemma exists_null_pairwise_disjoint_diff [countable ι] {s : ι → set α}
  (hd : pairwise (ae_disjoint μ on s)) :
  ∃ t : ι → set α, (∀ i, measurable_set (t i)) ∧ (∀ i, μ (t i) = 0) ∧
    pairwise (disjoint on (λ i, s i \ t i)) :=
begin
  refine ⟨λ i, to_measurable μ (s i ∩ ⋃ j ∈ ({i}ᶜ : set ι), s j),
    λ i, measurable_set_to_measurable _ _, λ i, _, _⟩,
  { simp only [measure_to_measurable, inter_Union],
    exact (measure_bUnion_null_iff $ to_countable _).2 (λ j hj, hd (ne.symm hj)) },
  { simp only [pairwise, disjoint_left, on_fun, mem_diff, not_and, and_imp, not_not],
    intros i j hne x hi hU hj,
    replace hU : x ∉ s i ∩ ⋃ j ≠ i, s j := λ h, hU (subset_to_measurable _ _ h),
    simp only [mem_inter_iff, mem_Union, not_and, not_exists] at hU,
    exact (hU hi j hne.symm hj).elim }
end

namespace ae_disjoint

protected lemma eq (h : ae_disjoint μ s t) : μ (s ∩ t) = 0 := h

@[symm] protected lemma symm (h : ae_disjoint μ s t) : ae_disjoint μ t s :=
by rwa [ae_disjoint, inter_comm]

protected lemma symmetric : symmetric (ae_disjoint μ) := λ s t h, h.symm

protected lemma comm : ae_disjoint μ s t ↔ ae_disjoint μ t s := ⟨λ h, h.symm, λ h, h.symm⟩

protected lemma _root_.disjoint.ae_disjoint (h : disjoint s t) : ae_disjoint μ s t :=
by rw [ae_disjoint, disjoint_iff_inter_eq_empty.1 h, measure_empty]

protected lemma _root_.pairwise.ae_disjoint {f : ι → set α} (hf : pairwise (disjoint on f)) :
  pairwise (ae_disjoint μ on f) :=
hf.mono $ λ i j h, h.ae_disjoint

protected lemma _root_.set.pairwise_disjoint.ae_disjoint {f : ι → set α} {s : set ι}
  (hf : s.pairwise_disjoint f) :
  s.pairwise (ae_disjoint μ on f) :=
hf.mono' $ λ i j h, h.ae_disjoint

lemma mono_ae (h : ae_disjoint μ s t) (hu : u ≤ᵐ[μ] s) (hv : v ≤ᵐ[μ] t) : ae_disjoint μ u v :=
measure_mono_null_ae (hu.inter hv) h

protected lemma mono (h : ae_disjoint μ s t) (hu : u ⊆ s) (hv : v ⊆ t) : ae_disjoint μ u v :=
h.mono_ae hu.eventually_le hv.eventually_le

protected lemma congr (h : ae_disjoint μ s t) (hu : u =ᵐ[μ] s) (hv : v =ᵐ[μ] t) :
  ae_disjoint μ u v :=
h.mono_ae (filter.eventually_eq.le hu) (filter.eventually_eq.le hv)

@[simp] lemma Union_left_iff [countable ι] {s : ι → set α} :
  ae_disjoint μ (⋃ i, s i) t ↔ ∀ i, ae_disjoint μ (s i) t :=
by simp only [ae_disjoint, Union_inter, measure_Union_null_iff]

@[simp] lemma Union_right_iff [countable ι] {t : ι → set α} :
  ae_disjoint μ s (⋃ i, t i) ↔ ∀ i, ae_disjoint μ s (t i) :=
by simp only [ae_disjoint, inter_Union, measure_Union_null_iff]

@[simp] lemma union_left_iff : ae_disjoint μ (s ∪ t) u ↔ ae_disjoint μ s u ∧ ae_disjoint μ t u :=
by simp [union_eq_Union, and.comm]

@[simp] lemma union_right_iff : ae_disjoint μ s (t ∪ u) ↔ ae_disjoint μ s t ∧ ae_disjoint μ s u :=
by simp [union_eq_Union, and.comm]

lemma union_left (hs : ae_disjoint μ s u) (ht : ae_disjoint μ t u) : ae_disjoint μ (s ∪ t) u :=
union_left_iff.mpr ⟨hs, ht⟩

lemma union_right (ht : ae_disjoint μ s t) (hu : ae_disjoint μ s u) : ae_disjoint μ s (t ∪ u) :=
union_right_iff.2 ⟨ht, hu⟩

lemma diff_ae_eq_left (h : ae_disjoint μ s t) : (s \ t : set α) =ᵐ[μ] s :=
@diff_self_inter _ s t ▸ diff_null_ae_eq_self h

lemma diff_ae_eq_right (h : ae_disjoint μ s t) : (t \ s : set α) =ᵐ[μ] t := h.symm.diff_ae_eq_left

lemma measure_diff_left (h : ae_disjoint μ s t) : μ (s \ t) = μ s := measure_congr h.diff_ae_eq_left

lemma measure_diff_right (h : ae_disjoint μ s t) : μ (t \ s) = μ t :=
measure_congr h.diff_ae_eq_right

/-- If `s` and `t` are `μ`-a.e. disjoint, then `s \ u` and `t` are disjoint for some measurable null
set `u`. -/
lemma exists_disjoint_diff (h : ae_disjoint μ s t) :
  ∃ u, measurable_set u ∧ μ u = 0 ∧ disjoint (s \ u) t :=
⟨to_measurable μ (s ∩ t), measurable_set_to_measurable _ _, (measure_to_measurable _).trans h,
  disjoint_sdiff_self_left.mono_left $ λ x hx, ⟨hx.1, λ hxt, hx.2 $
    subset_to_measurable _ _ ⟨hx.1, hxt⟩⟩⟩

lemma of_null_right (h : μ t = 0) : ae_disjoint μ s t :=
measure_mono_null (inter_subset_right _ _) h

lemma of_null_left (h : μ s = 0) : ae_disjoint μ s t := (of_null_right h).symm

end ae_disjoint

lemma ae_disjoint_compl_left : ae_disjoint μ sᶜ s := (@disjoint_compl_left _ _ s).ae_disjoint
lemma ae_disjoint_compl_right : ae_disjoint μ s sᶜ := (@disjoint_compl_right _ _ s).ae_disjoint

end measure_theory
