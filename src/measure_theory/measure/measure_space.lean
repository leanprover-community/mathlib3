/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import measure_theory.measure.null_measurable
import measure_theory.measurable_space

/-!
# Measure spaces

The definition of a measure and a measure space are in `measure_theory.measure_space_def`, with
only a few basic properties. This file provides many more properties of these objects.
This separation allows the measurability tactic to import only the file `measure_space_def`, and to
be available in `measure_space` (through `measurable_space`).

Given a measurable space `α`, a measure on `α` is a function that sends measurable sets to the
extended nonnegative reals that satisfies the following conditions:
1. `μ ∅ = 0`;
2. `μ` is countably additive. This means that the measure of a countable union of pairwise disjoint
   sets is equal to the measure of the individual sets.

Every measure can be canonically extended to an outer measure, so that it assigns values to
all subsets, not just the measurable subsets. On the other hand, a measure that is countably
additive on measurable sets can be restricted to measurable sets to obtain a measure.
In this file a measure is defined to be an outer measure that is countably additive on
measurable sets, with the additional assumption that the outer measure is the canonical
extension of the restricted measure.

Measures on `α` form a complete lattice, and are closed under scalar multiplication with `ℝ≥0∞`.

We introduce the following typeclasses for measures:

* `is_probability_measure μ`: `μ univ = 1`;
* `is_finite_measure μ`: `μ univ < ∞`;
* `sigma_finite μ`: there exists a countable collection of sets that cover `univ`
  where `μ` is finite;
* `is_locally_finite_measure μ` : `∀ x, ∃ s ∈ 𝓝 x, μ s < ∞`;
* `has_no_atoms μ` : `∀ x, μ {x} = 0`; possibly should be redefined as
  `∀ s, 0 < μ s → ∃ t ⊆ s, 0 < μ t ∧ μ t < μ s`.

Given a measure, the null sets are the sets where `μ s = 0`, where `μ` denotes the corresponding
outer measure (so `s` might not be measurable). We can then define the completion of `μ` as the
measure on the least `σ`-algebra that also contains all null sets, by defining the measure to be `0`
on the null sets.

## Main statements

* `completion` is the completion of a measure to all null measurable sets.
* `measure.of_measurable` and `outer_measure.to_measure` are two important ways to define a measure.

## Implementation notes

Given `μ : measure α`, `μ s` is the value of the *outer measure* applied to `s`.
This conveniently allows us to apply the measure to sets without proving that they are measurable.
We get countable subadditivity for all sets, but only countable additivity for measurable sets.

You often don't want to define a measure via its constructor.
Two ways that are sometimes more convenient:
* `measure.of_measurable` is a way to define a measure by only giving its value on measurable sets
  and proving the properties (1) and (2) mentioned above.
* `outer_measure.to_measure` is a way of obtaining a measure from an outer measure by showing that
  all measurable sets in the measurable space are Carathéodory measurable.

To prove that two measures are equal, there are multiple options:
* `ext`: two measures are equal if they are equal on all measurable sets.
* `ext_of_generate_from_of_Union`: two measures are equal if they are equal on a π-system generating
  the measurable sets, if the π-system contains a spanning increasing sequence of sets where the
  measures take finite value (in particular the measures are σ-finite). This is a special case of
  the more general `ext_of_generate_from_of_cover`
* `ext_of_generate_finite`: two finite measures are equal if they are equal on a π-system
  generating the measurable sets. This is a special case of `ext_of_generate_from_of_Union` using
  `C ∪ {univ}`, but is easier to work with.

A `measure_space` is a class that is a measurable space with a canonical measure.
The measure is denoted `volume`.

## References

* <https://en.wikipedia.org/wiki/Measure_(mathematics)>
* <https://en.wikipedia.org/wiki/Complete_measure>
* <https://en.wikipedia.org/wiki/Almost_everywhere>

## Tags

measure, almost everywhere, measure space, completion, null set, null measurable set
-/

noncomputable theory

open set filter (hiding map) function measurable_space topological_space (second_countable_topology)
open_locale classical topological_space big_operators filter ennreal nnreal interval

variables {α β γ δ ι R R' : Type*}

namespace measure_theory

section

variables {m : measurable_space α} {μ μ₁ μ₂ : measure α} {s s₁ s₂ t : set α}

instance ae_is_measurably_generated : is_measurably_generated μ.ae :=
⟨λ s hs, let ⟨t, hst, htm, htμ⟩ := exists_measurable_superset_of_null hs in
  ⟨tᶜ, compl_mem_ae_iff.2 htμ, htm.compl, compl_subset_comm.1 hst⟩⟩

/-- See also `measure_theory.ae_restrict_interval_oc_iff`. -/
lemma ae_interval_oc_iff [linear_order α] {a b : α} {P : α → Prop} :
  (∀ᵐ x ∂μ, x ∈ Ι a b → P x) ↔ (∀ᵐ x ∂μ, x ∈ Ioc a b → P x) ∧ (∀ᵐ x ∂μ, x ∈ Ioc b a → P x) :=
by simp only [interval_oc_eq_union, mem_union_eq, or_imp_distrib, eventually_and]

lemma measure_union (hd : disjoint s₁ s₂) (h : measurable_set s₂) :
  μ (s₁ ∪ s₂) = μ s₁ + μ s₂ :=
measure_union₀ h.null_measurable_set hd.ae_disjoint

lemma measure_union' (hd : disjoint s₁ s₂) (h : measurable_set s₁) :
  μ (s₁ ∪ s₂) = μ s₁ + μ s₂ :=
measure_union₀' h.null_measurable_set hd.ae_disjoint

lemma measure_inter_add_diff (s : set α) (ht : measurable_set t) :
  μ (s ∩ t) + μ (s \ t) = μ s :=
measure_inter_add_diff₀ _ ht.null_measurable_set

lemma measure_diff_add_inter (s : set α) (ht : measurable_set t) :
  μ (s \ t) + μ (s ∩ t) = μ s :=
(add_comm _ _).trans (measure_inter_add_diff s ht)

lemma measure_union_add_inter (s : set α) (ht : measurable_set t) :
  μ (s ∪ t) + μ (s ∩ t) = μ s + μ t :=
by { rw [← measure_inter_add_diff (s ∪ t) ht, set.union_inter_cancel_right,
  union_diff_right, ← measure_inter_add_diff s ht], ac_refl }

lemma measure_union_add_inter' (hs : measurable_set s) (t : set α) :
  μ (s ∪ t) + μ (s ∩ t) = μ s + μ t :=
by rw [union_comm, inter_comm, measure_union_add_inter t hs, add_comm]

lemma measure_add_measure_compl (h : measurable_set s) :
  μ s + μ sᶜ = μ univ :=
by { rw [← measure_union' _ h, union_compl_self], exact disjoint_compl_right }

lemma measure_bUnion {s : set β} {f : β → set α} (hs : countable s)
  (hd : s.pairwise (disjoint on f)) (h : ∀ b ∈ s, measurable_set (f b)) :
  μ (⋃ b ∈ s, f b) = ∑' p : s, μ (f p) :=
begin
  haveI := hs.to_encodable,
  rw bUnion_eq_Union,
  exact measure_Union (hd.on_injective subtype.coe_injective $ λ x, x.2) (λ x, h x x.2)
end

lemma measure_sUnion {S : set (set α)} (hs : countable S)
  (hd : S.pairwise disjoint) (h : ∀ s ∈ S, measurable_set s) :
  μ (⋃₀ S) = ∑' s : S, μ s :=
by rw [sUnion_eq_bUnion, measure_bUnion hs hd h]

lemma measure_bUnion_finset {s : finset ι} {f : ι → set α} (hd : set.pairwise ↑s (disjoint on f))
  (hm : ∀ b ∈ s, measurable_set (f b)) :
  μ (⋃ b ∈ s, f b) = ∑ p in s, μ (f p) :=
begin
  rw [← finset.sum_attach, finset.attach_eq_univ, ← tsum_fintype],
  exact measure_bUnion s.countable_to_set hd hm
end

/-- If `s` is a countable set, then the measure of its preimage can be found as the sum of measures
of the fibers `f ⁻¹' {y}`. -/
lemma tsum_measure_preimage_singleton {s : set β} (hs : countable s) {f : α → β}
  (hf : ∀ y ∈ s, measurable_set (f ⁻¹' {y})) :
  ∑' b : s, μ (f ⁻¹' {↑b}) = μ (f ⁻¹' s) :=
by rw [← set.bUnion_preimage_singleton, measure_bUnion hs (pairwise_disjoint_fiber _ _) hf]

/-- If `s` is a `finset`, then the measure of its preimage can be found as the sum of measures
of the fibers `f ⁻¹' {y}`. -/
lemma sum_measure_preimage_singleton (s : finset β) {f : α → β}
  (hf : ∀ y ∈ s, measurable_set (f ⁻¹' {y})) :
  ∑ b in s, μ (f ⁻¹' {b}) = μ (f ⁻¹' ↑s) :=
by simp only [← measure_bUnion_finset (pairwise_disjoint_fiber _ _) hf,
  finset.set_bUnion_preimage_singleton]

lemma measure_diff_null' (h : μ (s₁ ∩ s₂) = 0) : μ (s₁ \ s₂) = μ s₁ :=
measure_congr $ diff_ae_eq_self.2 h

lemma measure_diff_null (h : μ s₂ = 0) : μ (s₁ \ s₂) = μ s₁ :=
measure_diff_null' $ measure_mono_null (inter_subset_right _ _) h

lemma measure_add_diff (hs : measurable_set s) (t : set α) : μ s + μ (t \ s) = μ (s ∪ t) :=
by rw [← measure_union' disjoint_diff hs, union_diff_self]

lemma measure_diff' (s : set α) (hm : measurable_set t) (h_fin : μ t ≠ ∞) :
  μ (s \ t) = μ (s ∪ t) - μ t :=
eq.symm $ ennreal.sub_eq_of_add_eq h_fin $ by rw [add_comm, measure_add_diff hm, union_comm]

lemma measure_diff (h : s₂ ⊆ s₁) (h₂ : measurable_set s₂) (h_fin : μ s₂ ≠ ∞) :
  μ (s₁ \ s₂) = μ s₁ - μ s₂ :=
by rw [measure_diff' _ h₂ h_fin, union_eq_self_of_subset_right h]

lemma le_measure_diff : μ s₁ - μ s₂ ≤ μ (s₁ \ s₂) :=
tsub_le_iff_left.2 $
calc μ s₁ ≤ μ (s₂ ∪ s₁)        : measure_mono (subset_union_right _ _)
      ... = μ (s₂ ∪ s₁ \ s₂)   : congr_arg μ union_diff_self.symm
      ... ≤ μ s₂ + μ (s₁ \ s₂) : measure_union_le _ _

lemma measure_diff_lt_of_lt_add (hs : measurable_set s) (hst : s ⊆ t)
  (hs' : μ s ≠ ∞) {ε : ℝ≥0∞} (h : μ t < μ s + ε) : μ (t \ s) < ε :=
begin
  rw [measure_diff hst hs hs'], rw add_comm at h,
  exact ennreal.sub_lt_of_lt_add (measure_mono hst) h
end

lemma measure_diff_le_iff_le_add (hs : measurable_set s) (hst : s ⊆ t)
  (hs' : μ s ≠ ∞) {ε : ℝ≥0∞} : μ (t \ s) ≤ ε ↔ μ t ≤ μ s + ε :=
by rwa [measure_diff hst hs hs', tsub_le_iff_left]

lemma measure_eq_measure_of_null_diff {s t : set α} (hst : s ⊆ t) (h_nulldiff : μ (t \ s) = 0) :
  μ s = μ t :=
measure_congr (hst.eventually_le.antisymm $ ae_le_set.mpr h_nulldiff)

lemma measure_eq_measure_of_between_null_diff {s₁ s₂ s₃ : set α}
  (h12 : s₁ ⊆ s₂) (h23 : s₂ ⊆ s₃) (h_nulldiff : μ (s₃ \ s₁) = 0) :
  (μ s₁ = μ s₂) ∧ (μ s₂ = μ s₃) :=
begin
  have le12 : μ s₁ ≤ μ s₂ := measure_mono h12,
  have le23 : μ s₂ ≤ μ s₃ := measure_mono h23,
  have key : μ s₃ ≤ μ s₁ := calc
    μ s₃ = μ ((s₃ \ s₁) ∪ s₁)  : by rw (diff_union_of_subset (h12.trans h23))
     ... ≤ μ (s₃ \ s₁) + μ s₁  : measure_union_le _ _
     ... = μ s₁                : by simp only [h_nulldiff, zero_add],
  exact ⟨le12.antisymm (le23.trans key), le23.antisymm (key.trans le12)⟩,
end

lemma measure_eq_measure_smaller_of_between_null_diff {s₁ s₂ s₃ : set α}
  (h12 : s₁ ⊆ s₂) (h23 : s₂ ⊆ s₃) (h_nulldiff : μ (s₃ \ s₁) = 0) : μ s₁ = μ s₂ :=
(measure_eq_measure_of_between_null_diff h12 h23 h_nulldiff).1

lemma measure_eq_measure_larger_of_between_null_diff {s₁ s₂ s₃ : set α}
  (h12 : s₁ ⊆ s₂) (h23 : s₂ ⊆ s₃) (h_nulldiff : μ (s₃ \ s₁) = 0) : μ s₂ = μ s₃ :=
(measure_eq_measure_of_between_null_diff h12 h23 h_nulldiff).2

lemma measure_compl (h₁ : measurable_set s) (h_fin : μ s ≠ ∞) : μ (sᶜ) = μ univ - μ s :=
by { rw compl_eq_univ_diff, exact measure_diff (subset_univ s) h₁ h_fin }

/-- If `s ⊆ t`, `μ t ≤ μ s`, `μ t ≠ ∞`, and `s` is measurable, then `s =ᵐ[μ] t`. -/
lemma ae_eq_of_subset_of_measure_ge (h₁ : s ⊆ t) (h₂ : μ t ≤ μ s) (hsm : measurable_set s)
  (ht : μ t ≠ ∞) : s =ᵐ[μ] t :=
have A : μ t = μ s, from h₂.antisymm (measure_mono h₁),
have B : μ s ≠ ∞, from A ▸ ht,
h₁.eventually_le.antisymm $ ae_le_set.2 $ by rw [measure_diff h₁ hsm B, A, tsub_self]

lemma measure_Union_congr_of_subset [encodable β] {s : β → set α} {t : β → set α}
  (hsub : ∀ b, s b ⊆ t b) (h_le : ∀ b, μ (t b) ≤ μ (s b)) :
  μ (⋃ b, s b) = μ (⋃ b, t b) :=
begin
  rcases em (∃ b, μ (t b) = ∞) with ⟨b, hb⟩|htop,
  { calc μ (⋃ b, s b) = ∞ : top_unique (hb ▸ (h_le b).trans $ measure_mono $ subset_Union _ _)
    ... = μ (⋃ b, t b) : eq.symm $ top_unique $ hb ▸ measure_mono $ subset_Union _ _ },
  push_neg at htop,
  refine le_antisymm (measure_mono (Union_mono hsub)) _,
  set M := to_measurable μ,
  have H : ∀ b, (M (t b) ∩ M (⋃ b, s b) : set α) =ᵐ[μ] M (t b),
  { refine λ b, ae_eq_of_subset_of_measure_ge (inter_subset_left _ _) _ _ _,
    { calc μ (M (t b)) = μ (t b) : measure_to_measurable _
      ... ≤ μ (s b) : h_le b
      ... ≤ μ (M (t b) ∩ M (⋃ b, s b)) : measure_mono $
        subset_inter ((hsub b).trans $ subset_to_measurable _ _)
          ((subset_Union _ _).trans $ subset_to_measurable _ _) },
    { exact (measurable_set_to_measurable _ _).inter (measurable_set_to_measurable _ _) },
    { rw measure_to_measurable, exact htop b } },
  calc μ (⋃ b, t b) ≤ μ (⋃ b, M (t b)) :
    measure_mono (Union_mono $ λ b, subset_to_measurable _ _)
  ... = μ (⋃ b, M (t b) ∩ M (⋃ b, s b)) :
    measure_congr (eventually_eq.countable_Union H).symm
  ... ≤ μ (M (⋃ b, s b)) :
    measure_mono (Union_subset $ λ b, inter_subset_right _ _)
  ... = μ (⋃ b, s b) : measure_to_measurable _
end

lemma measure_union_congr_of_subset {t₁ t₂ : set α} (hs : s₁ ⊆ s₂) (hsμ : μ s₂ ≤ μ s₁)
  (ht : t₁ ⊆ t₂) (htμ : μ t₂ ≤ μ t₁) :
  μ (s₁ ∪ t₁) = μ (s₂ ∪ t₂) :=
begin
  rw [union_eq_Union, union_eq_Union],
  exact measure_Union_congr_of_subset (bool.forall_bool.2 ⟨ht, hs⟩) (bool.forall_bool.2 ⟨htμ, hsμ⟩)
end

@[simp] lemma measure_Union_to_measurable [encodable β] (s : β → set α) :
  μ (⋃ b, to_measurable μ (s b)) = μ (⋃ b, s b) :=
eq.symm $ measure_Union_congr_of_subset (λ b, subset_to_measurable _ _)
  (λ b, (measure_to_measurable _).le)

lemma measure_bUnion_to_measurable {I : set β} (hc : countable I) (s : β → set α) :
  μ (⋃ b ∈ I, to_measurable μ (s b)) = μ (⋃ b ∈ I, s b) :=
by { haveI := hc.to_encodable, simp only [bUnion_eq_Union, measure_Union_to_measurable] }

@[simp] lemma measure_to_measurable_union : μ (to_measurable μ s ∪ t) = μ (s ∪ t) :=
eq.symm $ measure_union_congr_of_subset (subset_to_measurable _ _) (measure_to_measurable _).le
  subset.rfl le_rfl

@[simp] lemma measure_union_to_measurable : μ (s ∪ to_measurable μ t) = μ (s ∪ t) :=
eq.symm $ measure_union_congr_of_subset subset.rfl le_rfl (subset_to_measurable _ _)
  (measure_to_measurable _).le

lemma sum_measure_le_measure_univ {s : finset ι} {t : ι → set α} (h : ∀ i ∈ s, measurable_set (t i))
  (H : set.pairwise ↑s (disjoint on t)) :
  ∑ i in s, μ (t i) ≤ μ (univ : set α) :=
by { rw ← measure_bUnion_finset H h, exact measure_mono (subset_univ _) }

lemma tsum_measure_le_measure_univ {s : ι → set α} (hs : ∀ i, measurable_set (s i))
  (H : pairwise (disjoint on s)) :
  ∑' i, μ (s i) ≤ μ (univ : set α) :=
begin
  rw [ennreal.tsum_eq_supr_sum],
  exact supr_le (λ s, sum_measure_le_measure_univ (λ i hi, hs i) (λ i hi j hj hij, H i j hij))
end

/-- Pigeonhole principle for measure spaces: if `∑' i, μ (s i) > μ univ`, then
one of the intersections `s i ∩ s j` is not empty. -/
lemma exists_nonempty_inter_of_measure_univ_lt_tsum_measure {m : measurable_space α} (μ : measure α)
  {s : ι → set α} (hs : ∀ i, measurable_set (s i)) (H : μ (univ : set α) < ∑' i, μ (s i)) :
  ∃ i j (h : i ≠ j), (s i ∩ s j).nonempty :=
begin
  contrapose! H,
  apply tsum_measure_le_measure_univ hs,
  exact λ i j hij x hx, H i j hij ⟨x, hx⟩
end

/-- Pigeonhole principle for measure spaces: if `s` is a `finset` and
`∑ i in s, μ (t i) > μ univ`, then one of the intersections `t i ∩ t j` is not empty. -/
lemma exists_nonempty_inter_of_measure_univ_lt_sum_measure {m : measurable_space α} (μ : measure α)
  {s : finset ι} {t : ι → set α} (h : ∀ i ∈ s, measurable_set (t i))
  (H : μ (univ : set α) < ∑ i in s, μ (t i)) :
  ∃ (i ∈ s) (j ∈ s) (h : i ≠ j), (t i ∩ t j).nonempty :=
begin
  contrapose! H,
  apply sum_measure_le_measure_univ h,
  exact λ i hi j hj hij x hx, H i hi j hj hij ⟨x, hx⟩
end

/-- If two sets `s` and `t` are included in a set `u`, and `μ s + μ t > μ u`,
then `s` intersects `t`. Version assuming that `t` is measurable. -/
lemma nonempty_inter_of_measure_lt_add
  {m : measurable_space α} (μ : measure α)
  {s t u : set α} (ht : measurable_set t) (h's : s ⊆ u) (h't : t ⊆ u)
  (h : μ u < μ s + μ t) :
  (s ∩ t).nonempty :=
begin
  contrapose! h,
  calc μ s + μ t = μ (s ∪ t) :
    by { rw measure_union _ ht, exact λ x hx, h ⟨x, hx⟩ }
  ... ≤ μ u : measure_mono (union_subset h's h't)
end

/-- If two sets `s` and `t` are included in a set `u`, and `μ s + μ t > μ u`,
then `s` intersects `t`. Version assuming that `s` is measurable. -/
lemma nonempty_inter_of_measure_lt_add'
  {m : measurable_space α} (μ : measure α)
  {s t u : set α} (hs : measurable_set s) (h's : s ⊆ u) (h't : t ⊆ u)
  (h : μ u < μ s + μ t) :
  (s ∩ t).nonempty :=
begin
  rw add_comm at h,
  rw inter_comm,
  exact nonempty_inter_of_measure_lt_add μ hs h't h's h
end

/-- Continuity from below: the measure of the union of a directed sequence of (not necessarily
-measurable) sets is the supremum of the measures. -/
lemma measure_Union_eq_supr [encodable ι] {s : ι → set α} (hd : directed (⊆) s) :
  μ (⋃ i, s i) = ⨆ i, μ (s i) :=
begin
  -- WLOG, `ι = ℕ`
  generalize ht : function.extend encodable.encode s ⊥ = t,
  replace hd : directed (⊆) t := ht ▸ hd.extend_bot encodable.encode_injective,
  suffices : μ (⋃ n, t n) = ⨆ n, μ (t n),
  { simp only [← ht, apply_extend encodable.encode_injective μ, ← supr_eq_Union,
      supr_extend_bot encodable.encode_injective, (∘), pi.bot_apply, bot_eq_empty,
      measure_empty] at this,
    exact this.trans (supr_extend_bot encodable.encode_injective _) },
  unfreezingI { clear_dependent ι },
  -- The `≥` inequality is trivial
  refine le_antisymm _ (supr_le $ λ i, measure_mono $ subset_Union _ _),
  -- Choose `T n ⊇ t n` of the same measure, put `Td n = disjointed T`
  set T : ℕ → set α := λ n, to_measurable μ (t n),
  set Td : ℕ → set α := disjointed T,
  have hm : ∀ n, measurable_set (Td n),
    from measurable_set.disjointed (λ n, measurable_set_to_measurable _ _),
  calc μ (⋃ n, t n) ≤ μ (⋃ n, T n) : measure_mono (Union_mono $ λ i, subset_to_measurable _ _)
  ... = μ (⋃ n, Td n) : by rw [Union_disjointed]
  ... ≤ ∑' n, μ (Td n) : measure_Union_le _
  ... = ⨆ I : finset ℕ, ∑ n in I, μ (Td n) : ennreal.tsum_eq_supr_sum
  ... ≤ ⨆ n, μ (t n) : supr_le (λ I, _),
  rcases hd.finset_le I with ⟨N, hN⟩,
  calc ∑ n in I, μ (Td n) = μ (⋃ n ∈ I, Td n) :
    (measure_bUnion_finset ((disjoint_disjointed T).set_pairwise I) (λ n _, hm n)).symm
  ... ≤ μ (⋃ n ∈ I, T n) : measure_mono (Union₂_mono $ λ n hn, disjointed_subset _ _)
  ... = μ (⋃ n ∈ I, t n) : measure_bUnion_to_measurable I.countable_to_set _
  ... ≤ μ (t N) : measure_mono (Union₂_subset hN)
  ... ≤ ⨆ n, μ (t n) : le_supr (μ ∘ t) N,
end

lemma measure_bUnion_eq_supr {s : ι → set α} {t : set ι} (ht : countable t)
  (hd : directed_on ((⊆) on s) t) :
  μ (⋃ i ∈ t, s i) = ⨆ i ∈ t, μ (s i) :=
begin
  haveI := ht.to_encodable,
  rw [bUnion_eq_Union, measure_Union_eq_supr hd.directed_coe, ← supr_subtype'']
end

/-- Continuity from above: the measure of the intersection of a decreasing sequence of measurable
sets is the infimum of the measures. -/
lemma measure_Inter_eq_infi [encodable ι] {s : ι → set α}
  (h : ∀ i, measurable_set (s i)) (hd : directed (⊇) s) (hfin : ∃ i, μ (s i) ≠ ∞) :
  μ (⋂ i, s i) = (⨅ i, μ (s i)) :=
begin
  rcases hfin with ⟨k, hk⟩,
  have : ∀ t ⊆ s k, μ t ≠ ∞, from λ t ht, ne_top_of_le_ne_top hk (measure_mono ht),
  rw [← ennreal.sub_sub_cancel (by exact hk) (infi_le _ k), ennreal.sub_infi,
    ← ennreal.sub_sub_cancel (by exact hk) (measure_mono (Inter_subset _ k)),
    ← measure_diff (Inter_subset _ k) (measurable_set.Inter h) (this _ (Inter_subset _ k)),
    diff_Inter, measure_Union_eq_supr],
  { congr' 1,
    refine le_antisymm (supr_mono' $ λ i, _) (supr_mono $ λ i, _),
    { rcases hd i k with ⟨j, hji, hjk⟩,
      use j,
      rw [← measure_diff hjk (h _) (this _ hjk)],
      exact measure_mono (diff_subset_diff_right hji) },
    { rw [tsub_le_iff_right, ← measure_union disjoint_diff.symm (h i), set.union_comm],
      exact measure_mono (diff_subset_iff.1 $ subset.refl _) } },
  { exact hd.mono_comp _ (λ _ _, diff_subset_diff_right) }
end

/-- Continuity from below: the measure of the union of an increasing sequence of measurable sets
is the limit of the measures. -/
lemma tendsto_measure_Union [semilattice_sup ι] [encodable ι] {s : ι → set α} (hm : monotone s) :
  tendsto (μ ∘ s) at_top (𝓝 (μ (⋃ n, s n))) :=
begin
  rw measure_Union_eq_supr (directed_of_sup hm),
  exact tendsto_at_top_supr (λ n m hnm, measure_mono $ hm hnm)
end

/-- Continuity from above: the measure of the intersection of a decreasing sequence of measurable
sets is the limit of the measures. -/
lemma tendsto_measure_Inter [encodable ι] [semilattice_sup ι] {s : ι → set α}
  (hs : ∀ n, measurable_set (s n)) (hm : antitone s) (hf : ∃ i, μ (s i) ≠ ∞) :
  tendsto (μ ∘ s) at_top (𝓝 (μ (⋂ n, s n))) :=
begin
  rw measure_Inter_eq_infi hs (directed_of_sup hm) hf,
  exact tendsto_at_top_infi (λ n m hnm, measure_mono $ hm hnm),
end

/-- The measure of the intersection of a decreasing sequence of measurable
sets indexed by a linear order with first countable topology is the limit of the measures. -/
lemma tendsto_measure_bInter_gt {ι : Type*} [linear_order ι] [topological_space ι]
  [order_topology ι] [densely_ordered ι] [topological_space.first_countable_topology ι]
  {s : ι → set α} {a : ι}
  (hs : ∀ r > a, measurable_set (s r)) (hm : ∀ i j, a < i → i ≤ j → s i ⊆ s j)
  (hf : ∃ r > a, μ (s r) ≠ ∞) :
  tendsto (μ ∘ s) (𝓝[Ioi a] a) (𝓝 (μ (⋂ r > a, s r))) :=
begin
  refine tendsto_order.2 ⟨λ l hl, _, λ L hL, _⟩,
  { filter_upwards [self_mem_nhds_within] with r hr
      using hl.trans_le (measure_mono (bInter_subset_of_mem hr)), },
  obtain ⟨u, u_anti, u_pos, u_lim⟩ : ∃ (u : ℕ → ι), strict_anti u ∧ (∀ (n : ℕ), a < u n)
    ∧ tendsto u at_top (𝓝 a),
  { rcases hf with ⟨r, ar, hr⟩,
    rcases exists_seq_strict_anti_tendsto' ar with ⟨w, w_anti, w_mem, w_lim⟩,
    exact ⟨w, w_anti, λ n, (w_mem n).1, w_lim⟩ },
  have A : tendsto (μ ∘ (s ∘ u)) at_top (𝓝(μ (⋂ n, s (u n)))),
  { refine tendsto_measure_Inter (λ n, hs _ (u_pos n)) _ _,
    { intros m n hmn,
      exact hm _ _ (u_pos n) (u_anti.antitone hmn) },
    { rcases hf with ⟨r, rpos, hr⟩,
      obtain ⟨n, hn⟩ : ∃ (n : ℕ), u n < r := ((tendsto_order.1 u_lim).2 r rpos).exists,
      refine ⟨n, ne_of_lt (lt_of_le_of_lt _ hr.lt_top)⟩,
      exact measure_mono (hm _ _ (u_pos n) hn.le) } },
  have B : (⋂ n, s (u n)) = (⋂ r > a, s r),
  { apply subset.antisymm,
    { simp only [subset_Inter_iff, gt_iff_lt],
      intros r rpos,
      obtain ⟨n, hn⟩ : ∃ n, u n < r := ((tendsto_order.1 u_lim).2 _ rpos).exists,
      exact subset.trans (Inter_subset _ n) (hm (u n) r (u_pos n) hn.le) },
    { simp only [subset_Inter_iff, gt_iff_lt],
      intros n,
      apply bInter_subset_of_mem,
      exact u_pos n } },
  rw B at A,
  obtain ⟨n, hn⟩ : ∃ n, μ (s (u n)) < L := ((tendsto_order.1 A).2 _ hL).exists,
  have : Ioc a (u n) ∈ 𝓝[>] a := Ioc_mem_nhds_within_Ioi ⟨le_rfl, u_pos n⟩,
  filter_upwards [this] with r hr using lt_of_le_of_lt (measure_mono (hm _ _ hr.1 hr.2)) hn,
end

/-- One direction of the **Borel-Cantelli lemma**: if (sᵢ) is a sequence of sets such
that `∑ μ sᵢ` is finite, then the limit superior of the `sᵢ` is a null set. -/
lemma measure_limsup_eq_zero {s : ℕ → set α} (hs : ∑' i, μ (s i) ≠ ∞) : μ (limsup at_top s) = 0 :=
begin
  -- First we replace the sequence `sₙ` with a sequence of measurable sets `tₙ ⊇ sₙ` of the same
  -- measure.
  set t : ℕ → set α := λ n, to_measurable μ (s n),
  have ht : ∑' i, μ (t i) ≠ ∞, by simpa only [t, measure_to_measurable] using hs,
  suffices : μ (limsup at_top t) = 0,
  { have A : s ≤ t := λ n, subset_to_measurable μ (s n),
    -- TODO default args fail
    exact measure_mono_null (limsup_le_limsup (eventually_of_forall (pi.le_def.mp A))
      is_cobounded_le_of_bot is_bounded_le_of_top) this },
  -- Next we unfold `limsup` for sets and replace equality with an inequality
  simp only [limsup_eq_infi_supr_of_nat', set.infi_eq_Inter, set.supr_eq_Union,
    ← nonpos_iff_eq_zero],
  -- Finally, we estimate `μ (⋃ i, t (i + n))` by `∑ i', μ (t (i + n))`
  refine le_of_tendsto_of_tendsto'
    (tendsto_measure_Inter (λ i, measurable_set.Union (λ b, measurable_set_to_measurable _ _)) _
      ⟨0, ne_top_of_le_ne_top ht (measure_Union_le t)⟩)
    (ennreal.tendsto_sum_nat_add (μ ∘ t) ht) (λ n, measure_Union_le _),
  intros n m hnm x,
  simp only [set.mem_Union],
  exact λ ⟨i, hi⟩, ⟨i + (m - n), by simpa only [add_assoc, tsub_add_cancel_of_le hnm] using hi⟩
end

lemma measure_if {x : β} {t : set β} {s : set α} :
  μ (if x ∈ t then s else ∅) = indicator t (λ _, μ s) x :=
by { split_ifs; simp [h] }

end

section outer_measure

variables [ms : measurable_space α] {s t : set α}
include ms

/-- Obtain a measure by giving an outer measure where all sets in the σ-algebra are
  Carathéodory measurable. -/
def outer_measure.to_measure (m : outer_measure α) (h : ms ≤ m.caratheodory) : measure α :=
measure.of_measurable (λ s _, m s) m.empty
  (λ f hf hd, m.Union_eq_of_caratheodory (λ i, h _ (hf i)) hd)

lemma le_to_outer_measure_caratheodory (μ : measure α) : ms ≤ μ.to_outer_measure.caratheodory :=
λ s hs t, (measure_inter_add_diff _ hs).symm

@[simp] lemma to_measure_to_outer_measure (m : outer_measure α) (h : ms ≤ m.caratheodory) :
  (m.to_measure h).to_outer_measure = m.trim := rfl

@[simp] lemma to_measure_apply (m : outer_measure α) (h : ms ≤ m.caratheodory)
  {s : set α} (hs : measurable_set s) : m.to_measure h s = m s :=
m.trim_eq hs

lemma le_to_measure_apply (m : outer_measure α) (h : ms ≤ m.caratheodory) (s : set α) :
  m s ≤ m.to_measure h s :=
m.le_trim s

lemma to_measure_apply₀ (m : outer_measure α) (h : ms ≤ m.caratheodory)
  {s : set α} (hs : null_measurable_set s (m.to_measure h)) : m.to_measure h s = m s :=
begin
  refine le_antisymm _ (le_to_measure_apply _ _ _),
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, hts, htm, heq⟩,
  calc m.to_measure h s = m.to_measure h t : measure_congr heq.symm
                    ... = m t              : to_measure_apply m h htm
                    ... ≤ m s              : m.mono hts
end

@[simp] lemma to_outer_measure_to_measure {μ : measure α} :
  μ.to_outer_measure.to_measure (le_to_outer_measure_caratheodory _) = μ :=
measure.ext $ λ s, μ.to_outer_measure.trim_eq

@[simp] lemma bounded_by_measure (μ : measure α) :
  outer_measure.bounded_by μ = μ.to_outer_measure :=
μ.to_outer_measure.bounded_by_eq_self

end outer_measure

variables {m0 : measurable_space α} [measurable_space β] [measurable_space γ]
variables {μ μ₁ μ₂ μ₃ ν ν' ν₁ ν₂ : measure α} {s s' t : set α}

namespace measure

/-- If `u` is a superset of `t` with the same (finite) measure (both sets possibly non-measurable),
then for any measurable set `s` one also has `μ (t ∩ s) = μ (u ∩ s)`. -/
lemma measure_inter_eq_of_measure_eq {s t u : set α} (hs : measurable_set s)
  (h : μ t = μ u) (htu : t ⊆ u) (ht_ne_top : μ t ≠ ∞) :
  μ (t ∩ s) = μ (u ∩ s) :=
begin
  rw h at ht_ne_top,
  refine le_antisymm (measure_mono (inter_subset_inter_left _ htu)) _,
  have A : μ (u ∩ s) + μ (u \ s) ≤ μ (t ∩ s) + μ (u \ s) := calc
    μ (u ∩ s) + μ (u \ s) = μ u : measure_inter_add_diff _ hs
    ... = μ t : h.symm
    ... = μ (t ∩ s) + μ (t \ s) : (measure_inter_add_diff _ hs).symm
    ... ≤ μ (t ∩ s) + μ (u \ s) :
      add_le_add le_rfl (measure_mono (diff_subset_diff htu subset.rfl)),
  have B : μ (u \ s) ≠ ∞ := (lt_of_le_of_lt (measure_mono (diff_subset _ _)) ht_ne_top.lt_top).ne,
  exact ennreal.le_of_add_le_add_right B A
end

/-- The measurable superset `to_measurable μ t` of `t` (which has the same measure as `t`)
satisfies, for any measurable set `s`, the equality `μ (to_measurable μ t ∩ s) = μ (u ∩ s)`.
Here, we require that the measure of `t` is finite. The conclusion holds without this assumption
when the measure is sigma_finite, see `measure_to_measurable_inter_of_sigma_finite`. -/
lemma measure_to_measurable_inter {s t : set α} (hs : measurable_set s) (ht : μ t ≠ ∞) :
  μ (to_measurable μ t ∩ s) = μ (t ∩ s) :=
(measure_inter_eq_of_measure_eq hs (measure_to_measurable t).symm
  (subset_to_measurable μ t) ht).symm
/-! ### The `ℝ≥0∞`-module of measures -/

instance [measurable_space α] : has_zero (measure α) :=
⟨{ to_outer_measure := 0,
   m_Union := λ f hf hd, tsum_zero.symm,
   trimmed := outer_measure.trim_zero }⟩

@[simp] theorem zero_to_outer_measure {m : measurable_space α} :
  (0 : measure α).to_outer_measure = 0 := rfl

@[simp, norm_cast] theorem coe_zero {m : measurable_space α} : ⇑(0 : measure α) = 0 := rfl

lemma eq_zero_of_is_empty [is_empty α] {m : measurable_space α} (μ : measure α) : μ = 0 :=
ext $ λ s hs, by simp only [eq_empty_of_is_empty s, measure_empty]

instance [measurable_space α] : inhabited (measure α) := ⟨0⟩

instance [measurable_space α] : has_add (measure α) :=
⟨λ μ₁ μ₂,
{ to_outer_measure := μ₁.to_outer_measure + μ₂.to_outer_measure,
  m_Union := λ s hs hd,
    show μ₁ (⋃ i, s i) + μ₂ (⋃ i, s i) = ∑' i, (μ₁ (s i) + μ₂ (s i)),
    by rw [ennreal.tsum_add, measure_Union hd hs, measure_Union hd hs],
  trimmed := by rw [outer_measure.trim_add, μ₁.trimmed, μ₂.trimmed] }⟩

@[simp] theorem add_to_outer_measure {m : measurable_space α} (μ₁ μ₂ : measure α) :
  (μ₁ + μ₂).to_outer_measure = μ₁.to_outer_measure + μ₂.to_outer_measure := rfl

@[simp, norm_cast] theorem coe_add {m : measurable_space α} (μ₁ μ₂ : measure α) :
  ⇑(μ₁ + μ₂) = μ₁ + μ₂ := rfl

theorem add_apply {m : measurable_space α} (μ₁ μ₂ : measure α) (s : set α) :
  (μ₁ + μ₂) s = μ₁ s + μ₂ s := rfl

section has_scalar
variables [has_scalar R ℝ≥0∞] [is_scalar_tower R ℝ≥0∞ ℝ≥0∞]
variables [has_scalar R' ℝ≥0∞] [is_scalar_tower R' ℝ≥0∞ ℝ≥0∞]

instance [measurable_space α] : has_scalar R (measure α) :=
⟨λ c μ,
  { to_outer_measure := c • μ.to_outer_measure,
    m_Union := λ s hs hd, begin
      rw ←smul_one_smul ℝ≥0∞ c (_ : outer_measure α),
      dsimp,
      simp_rw [measure_Union hd hs, ennreal.tsum_mul_left],
    end,
    trimmed := by rw [outer_measure.trim_smul, μ.trimmed] }⟩

@[simp] theorem smul_to_outer_measure {m : measurable_space α} (c : R) (μ : measure α) :
  (c • μ).to_outer_measure = c • μ.to_outer_measure :=
rfl

@[simp, norm_cast] theorem coe_smul {m : measurable_space α} (c : R) (μ : measure α) :
  ⇑(c • μ) = c • μ :=
rfl

@[simp] theorem smul_apply {m : measurable_space α} (c : R) (μ : measure α) (s : set α) :
  (c • μ) s = c • μ s :=
rfl

instance [smul_comm_class R R' ℝ≥0∞] [measurable_space α] :
  smul_comm_class R R' (measure α) :=
⟨λ _ _ _, ext $ λ _ _, smul_comm _ _ _⟩

instance [has_scalar R R'] [is_scalar_tower R R' ℝ≥0∞] [measurable_space α] :
  is_scalar_tower R R' (measure α) :=
⟨λ _ _ _, ext $ λ _ _, smul_assoc _ _ _⟩

instance [has_scalar Rᵐᵒᵖ ℝ≥0∞] [is_central_scalar R ℝ≥0∞] [measurable_space α] :
  is_central_scalar R (measure α) :=
⟨λ _ _, ext $ λ _ _, op_smul_eq_smul _ _⟩

end has_scalar

instance [monoid R] [mul_action R ℝ≥0∞] [is_scalar_tower R ℝ≥0∞ ℝ≥0∞] [measurable_space α] :
  mul_action R (measure α) :=
injective.mul_action _ to_outer_measure_injective smul_to_outer_measure

instance add_comm_monoid [measurable_space α] : add_comm_monoid (measure α) :=
to_outer_measure_injective.add_comm_monoid to_outer_measure zero_to_outer_measure
      add_to_outer_measure (λ _ _, smul_to_outer_measure _ _)

/-- Coercion to function as an additive monoid homomorphism. -/
def coe_add_hom {m : measurable_space α} : measure α →+ (set α → ℝ≥0∞) :=
⟨coe_fn, coe_zero, coe_add⟩

@[simp] lemma coe_finset_sum {m : measurable_space α} (I : finset ι) (μ : ι → measure α) :
  ⇑(∑ i in I, μ i) = ∑ i in I, μ i :=
(@coe_add_hom α m).map_sum _ _

theorem finset_sum_apply {m : measurable_space α} (I : finset ι) (μ : ι → measure α) (s : set α) :
  (∑ i in I, μ i) s = ∑ i in I, μ i s :=
by rw [coe_finset_sum, finset.sum_apply]

instance [monoid R] [distrib_mul_action R ℝ≥0∞] [is_scalar_tower R ℝ≥0∞ ℝ≥0∞]
  [measurable_space α] :
  distrib_mul_action R (measure α) :=
injective.distrib_mul_action ⟨to_outer_measure, zero_to_outer_measure, add_to_outer_measure⟩
  to_outer_measure_injective smul_to_outer_measure

instance [semiring R] [module R ℝ≥0∞] [is_scalar_tower R ℝ≥0∞ ℝ≥0∞] [measurable_space α] :
  module R (measure α) :=
injective.module R ⟨to_outer_measure, zero_to_outer_measure, add_to_outer_measure⟩
  to_outer_measure_injective smul_to_outer_measure

@[simp] theorem coe_nnreal_smul_apply {m : measurable_space α} (c : ℝ≥0) (μ : measure α)
  (s : set α) :
  (c • μ) s = c * μ s :=
rfl

lemma ae_smul_measure_iff {p : α → Prop} {c : ℝ≥0∞} (hc : c ≠ 0) :
  (∀ᵐ x ∂(c • μ), p x) ↔ ∀ᵐ x ∂μ, p x :=
by simp [ae_iff, hc]

lemma measure_eq_left_of_subset_of_measure_add_eq {s t : set α}
  (h : (μ + ν) t ≠ ∞) (h' : s ⊆ t) (h'' : (μ + ν) s = (μ + ν) t) :
  μ s = μ t :=
begin
  refine le_antisymm (measure_mono h') _,
  have : μ t + ν t ≤ μ s + ν t := calc
    μ t + ν t = μ s + ν s : h''.symm
    ... ≤ μ s + ν t : add_le_add le_rfl (measure_mono h'),
  apply ennreal.le_of_add_le_add_right _ this,
  simp only [not_or_distrib, ennreal.add_eq_top, pi.add_apply, ne.def, coe_add] at h,
  exact h.2
end

lemma measure_eq_right_of_subset_of_measure_add_eq {s t : set α}
  (h : (μ + ν) t ≠ ∞) (h' : s ⊆ t) (h'' : (μ + ν) s = (μ + ν) t) :
  ν s = ν t :=
begin
  rw add_comm at h'' h,
  exact measure_eq_left_of_subset_of_measure_add_eq h h' h''
end

lemma measure_to_measurable_add_inter_left {s t : set α}
  (hs : measurable_set s) (ht : (μ + ν) t ≠ ∞) :
  μ (to_measurable (μ + ν) t ∩ s) = μ (t ∩ s) :=
begin
  refine (measure_inter_eq_of_measure_eq hs _ (subset_to_measurable _ _) _).symm,
  { refine measure_eq_left_of_subset_of_measure_add_eq _ (subset_to_measurable _ _)
      (measure_to_measurable t).symm,
    rwa measure_to_measurable t, },
  { simp only [not_or_distrib, ennreal.add_eq_top, pi.add_apply, ne.def, coe_add] at ht,
    exact ht.1 }
end

lemma measure_to_measurable_add_inter_right {s t : set α}
  (hs : measurable_set s) (ht : (μ + ν) t ≠ ∞) :
  ν (to_measurable (μ + ν) t ∩ s) = ν (t ∩ s) :=
begin
  rw add_comm at ht ⊢,
  exact measure_to_measurable_add_inter_left hs ht
end

/-! ### The complete lattice of measures -/

/-- Measures are partially ordered.

The definition of less equal here is equivalent to the definition without the
measurable set condition, and this is shown by `measure.le_iff'`. It is defined
this way since, to prove `μ ≤ ν`, we may simply `intros s hs` instead of rewriting followed
by `intros s hs`. -/
instance [measurable_space α] : partial_order (measure α) :=
{ le          := λ m₁ m₂, ∀ s, measurable_set s → m₁ s ≤ m₂ s,
  le_refl     := λ m s hs, le_rfl,
  le_trans    := λ m₁ m₂ m₃ h₁ h₂ s hs, le_trans (h₁ s hs) (h₂ s hs),
  le_antisymm := λ m₁ m₂ h₁ h₂, ext $
    λ s hs, le_antisymm (h₁ s hs) (h₂ s hs) }

theorem le_iff : μ₁ ≤ μ₂ ↔ ∀ s, measurable_set s → μ₁ s ≤ μ₂ s := iff.rfl

theorem to_outer_measure_le : μ₁.to_outer_measure ≤ μ₂.to_outer_measure ↔ μ₁ ≤ μ₂ :=
by rw [← μ₂.trimmed, outer_measure.le_trim_iff]; refl

theorem le_iff' : μ₁ ≤ μ₂ ↔ ∀ s, μ₁ s ≤ μ₂ s :=
to_outer_measure_le.symm

theorem lt_iff : μ < ν ↔ μ ≤ ν ∧ ∃ s, measurable_set s ∧ μ s < ν s :=
lt_iff_le_not_le.trans $ and_congr iff.rfl $ by simp only [le_iff, not_forall, not_le, exists_prop]

theorem lt_iff' : μ < ν ↔ μ ≤ ν ∧ ∃ s, μ s < ν s :=
lt_iff_le_not_le.trans $ and_congr iff.rfl $ by simp only [le_iff', not_forall, not_le]

instance covariant_add_le [measurable_space α] : covariant_class (measure α) (measure α) (+) (≤) :=
⟨λ ν μ₁ μ₂ hμ s hs, add_le_add_left (hμ s hs) _⟩

protected lemma le_add_left (h : μ ≤ ν) : μ ≤ ν' + ν :=
λ s hs, le_add_left (h s hs)

protected lemma le_add_right (h : μ ≤ ν) : μ ≤ ν + ν' :=
λ s hs, le_add_right (h s hs)

section Inf
variables {m : set (measure α)}

lemma Inf_caratheodory (s : set α) (hs : measurable_set s) :
  (Inf (to_outer_measure '' m)).caratheodory.measurable_set' s :=
begin
  rw [outer_measure.Inf_eq_bounded_by_Inf_gen],
  refine outer_measure.bounded_by_caratheodory (λ t, _),
  simp only [outer_measure.Inf_gen, le_infi_iff, ball_image_iff, coe_to_outer_measure,
    measure_eq_infi t],
  intros μ hμ u htu hu,
  have hm : ∀ {s t}, s ⊆ t → outer_measure.Inf_gen (to_outer_measure '' m) s ≤ μ t,
  { intros s t hst,
    rw [outer_measure.Inf_gen_def],
    refine infi_le_of_le (μ.to_outer_measure) (infi_le_of_le (mem_image_of_mem _ hμ) _),
    rw [to_outer_measure_apply],
    refine measure_mono hst },
  rw [← measure_inter_add_diff u hs],
  refine add_le_add (hm $ inter_subset_inter_left _ htu) (hm $ diff_subset_diff_left htu)
end

instance [measurable_space α] : has_Inf (measure α) :=
⟨λ m, (Inf (to_outer_measure '' m)).to_measure $ Inf_caratheodory⟩

lemma Inf_apply (hs : measurable_set s) : Inf m s = Inf (to_outer_measure '' m) s :=
to_measure_apply _ _ hs

private lemma measure_Inf_le (h : μ ∈ m) : Inf m ≤ μ :=
have Inf (to_outer_measure '' m) ≤ μ.to_outer_measure := Inf_le (mem_image_of_mem _ h),
λ s hs, by rw [Inf_apply hs, ← to_outer_measure_apply]; exact this s

private lemma measure_le_Inf (h : ∀ μ' ∈ m, μ ≤ μ') : μ ≤ Inf m :=
have μ.to_outer_measure ≤ Inf (to_outer_measure '' m) :=
  le_Inf $ ball_image_of_ball $ λ μ hμ, to_outer_measure_le.2 $ h _ hμ,
λ s hs, by rw [Inf_apply hs, ← to_outer_measure_apply]; exact this s

instance [measurable_space α] : complete_semilattice_Inf (measure α) :=
{ Inf_le := λ s a, measure_Inf_le,
  le_Inf := λ s a, measure_le_Inf,
  ..(by apply_instance : partial_order (measure α)),
  ..(by apply_instance : has_Inf (measure α)), }

instance [measurable_space α] : complete_lattice (measure α) :=
{ bot := 0,
  bot_le := λ a s hs, by exact bot_le,
/- Adding an explicit `top` makes `leanchecker` fail, see lean#364, disable for now

  top := (⊤ : outer_measure α).to_measure (by rw [outer_measure.top_caratheodory]; exact le_top),
  le_top := λ a s hs,
    by cases s.eq_empty_or_nonempty with h  h;
      simp [h, to_measure_apply ⊤ _ hs, outer_measure.top_apply],
-/
  .. complete_lattice_of_complete_semilattice_Inf (measure α) }

end Inf

@[simp] lemma top_add : ⊤ + μ = ⊤ := top_unique $ measure.le_add_right le_rfl
@[simp] lemma add_top : μ + ⊤ = ⊤ := top_unique $ measure.le_add_left le_rfl

protected lemma zero_le {m0 : measurable_space α} (μ : measure α) : 0 ≤ μ := bot_le

lemma nonpos_iff_eq_zero' : μ ≤ 0 ↔ μ = 0 :=
μ.zero_le.le_iff_eq

@[simp] lemma measure_univ_eq_zero : μ univ = 0 ↔ μ = 0 :=
⟨λ h, bot_unique $ λ s hs, trans_rel_left (≤) (measure_mono (subset_univ s)) h, λ h, h.symm ▸ rfl⟩

/-! ### Pushforward and pullback -/

/-- Lift a linear map between `outer_measure` spaces such that for each measure `μ` every measurable
set is caratheodory-measurable w.r.t. `f μ` to a linear map between `measure` spaces. -/
def lift_linear {m0 : measurable_space α} (f : outer_measure α →ₗ[ℝ≥0∞] outer_measure β)
  (hf : ∀ μ : measure α, ‹_› ≤ (f μ.to_outer_measure).caratheodory) :
  measure α →ₗ[ℝ≥0∞] measure β :=
{ to_fun := λ μ, (f μ.to_outer_measure).to_measure (hf μ),
  map_add' := λ μ₁ μ₂, ext $ λ s hs, by simp [hs],
  map_smul' := λ c μ, ext $ λ s hs, by simp [hs] }

@[simp] lemma lift_linear_apply {f : outer_measure α →ₗ[ℝ≥0∞] outer_measure β} (hf)
  {s : set β} (hs : measurable_set s) : lift_linear f hf μ s = f μ.to_outer_measure s :=
to_measure_apply _ _ hs

lemma le_lift_linear_apply {f : outer_measure α →ₗ[ℝ≥0∞] outer_measure β} (hf) (s : set β) :
  f μ.to_outer_measure s ≤ lift_linear f hf μ s :=
le_to_measure_apply _ _ s

/-- The pushforward of a measure as a linear map. It is defined to be `0` if `f` is not
a measurable function. -/
def mapₗ [measurable_space α] (f : α → β) : measure α →ₗ[ℝ≥0∞] measure β :=
if hf : measurable f then
  lift_linear (outer_measure.map f) $ λ μ s hs t,
    le_to_outer_measure_caratheodory μ _ (hf hs) (f ⁻¹' t)
else 0

lemma mapₗ_congr {f g : α → β} (hf : measurable f) (hg : measurable g) (h : f =ᵐ[μ] g) :
  mapₗ f μ = mapₗ g μ :=
begin
  ext1 s hs,
  simpa only [mapₗ, hf, hg, hs, dif_pos, lift_linear_apply, outer_measure.map_apply,
    coe_to_outer_measure] using measure_congr (h.preimage s),
end

/-- The pushforward of a measure. It is defined to be `0` if `f` is not an almost everywhere
measurable function. -/
@[irreducible] def map [measurable_space α] (f : α → β) (μ : measure α) : measure β :=
if hf : ae_measurable f μ then mapₗ (hf.mk f) μ else 0

include m0

lemma mapₗ_mk_apply_of_ae_measurable {f : α → β} (hf : ae_measurable f μ) :
  mapₗ (hf.mk f) μ = map f μ :=
by simp [map, hf]

lemma mapₗ_apply_of_measurable {f : α → β} (hf : measurable f) (μ : measure α) :
  mapₗ f μ = map f μ :=
begin
  simp only [← mapₗ_mk_apply_of_ae_measurable hf.ae_measurable],
  exact mapₗ_congr hf hf.ae_measurable.measurable_mk hf.ae_measurable.ae_eq_mk
end

@[simp] lemma map_add (μ ν : measure α) {f : α → β} (hf : measurable f) :
  (μ + ν).map f = μ.map f + ν.map f :=
by simp [← mapₗ_apply_of_measurable hf]

@[simp] lemma map_zero (f : α → β) :
  (0 : measure α).map f = 0 :=
begin
  by_cases hf : ae_measurable f (0 : measure α);
  simp [map, hf],
end

theorem map_of_not_ae_measurable {f : α → β} {μ : measure α} (hf : ¬ ae_measurable f μ) :
  μ.map f = 0 :=
by simp [map, hf]

lemma map_congr {f g : α → β} (h : f =ᵐ[μ] g) : measure.map f μ = measure.map g μ :=
begin
  by_cases hf : ae_measurable f μ,
  { have hg : ae_measurable g μ := hf.congr h,
    simp only [← mapₗ_mk_apply_of_ae_measurable hf, ← mapₗ_mk_apply_of_ae_measurable hg],
    exact mapₗ_congr hf.measurable_mk hg.measurable_mk
      (hf.ae_eq_mk.symm.trans (h.trans hg.ae_eq_mk)) },
  { have hg : ¬ (ae_measurable g μ), by simpa [← ae_measurable_congr h] using hf,
    simp [map_of_not_ae_measurable, hf, hg] }
end

@[simp] protected lemma map_smul (c : ℝ≥0∞) (μ : measure α) (f : α → β) :
  (c • μ).map f = c • μ.map f :=
begin
  rcases eq_or_ne c 0 with rfl|hc, { simp },
  by_cases hf : ae_measurable f μ,
  { have hfc : ae_measurable f (c • μ) :=
      ⟨hf.mk f, hf.measurable_mk, (ae_smul_measure_iff hc).2 hf.ae_eq_mk⟩,
    simp only [←mapₗ_mk_apply_of_ae_measurable hf, ←mapₗ_mk_apply_of_ae_measurable hfc,
      linear_map.map_smulₛₗ, ring_hom.id_apply],
    congr' 1,
    apply mapₗ_congr hfc.measurable_mk hf.measurable_mk,
    exact eventually_eq.trans ((ae_smul_measure_iff hc).1 hfc.ae_eq_mk.symm) hf.ae_eq_mk },
  { have hfc : ¬ (ae_measurable f (c • μ)),
    { assume hfc,
      exact hf ⟨hfc.mk f, hfc.measurable_mk, (ae_smul_measure_iff hc).1 hfc.ae_eq_mk⟩ },
    simp [map_of_not_ae_measurable hf, map_of_not_ae_measurable hfc] }
end

/-- We can evaluate the pushforward on measurable sets. For non-measurable sets, see
  `measure_theory.measure.le_map_apply` and `measurable_equiv.map_apply`. -/
@[simp] theorem map_apply_of_ae_measurable
  {f : α → β} (hf : ae_measurable f μ) {s : set β} (hs : measurable_set s) :
  μ.map f s = μ (f ⁻¹' s) :=
by simpa only [mapₗ, hf.measurable_mk, hs, dif_pos, lift_linear_apply, outer_measure.map_apply,
  coe_to_outer_measure, ← mapₗ_mk_apply_of_ae_measurable hf]
  using measure_congr (hf.ae_eq_mk.symm.preimage s)

@[simp] theorem map_apply
  {f : α → β} (hf : measurable f) {s : set β} (hs : measurable_set s) :
  μ.map f s = μ (f ⁻¹' s) :=
map_apply_of_ae_measurable hf.ae_measurable hs

lemma map_to_outer_measure {f : α → β} (hf : ae_measurable f μ) :
  (μ.map f).to_outer_measure = (outer_measure.map f μ.to_outer_measure).trim :=
begin
  rw [← trimmed, outer_measure.trim_eq_trim_iff],
  intros s hs,
  rw [coe_to_outer_measure, map_apply_of_ae_measurable hf hs, outer_measure.map_apply,
    coe_to_outer_measure]
end

@[simp] lemma map_id : map id μ = μ :=
ext $ λ s, map_apply measurable_id

@[simp] lemma map_id' : map (λ x, x) μ = μ := map_id

lemma map_map {g : β → γ} {f : α → β} (hg : measurable g) (hf : measurable f) :
  (μ.map f).map g = μ.map (g ∘ f) :=
ext $ λ s hs, by simp [hf, hg, hs, hg hs, hg.comp hf, ← preimage_comp]

@[mono] lemma map_mono {f : α → β} (h : μ ≤ ν) (hf : measurable f) : μ.map f ≤ ν.map f :=
λ s hs, by simp [hf.ae_measurable, hs, h _ (hf hs)]

/-- Even if `s` is not measurable, we can bound `map f μ s` from below.
  See also `measurable_equiv.map_apply`. -/
theorem le_map_apply {f : α → β} (hf : ae_measurable f μ) (s : set β) : μ (f ⁻¹' s) ≤ μ.map f s :=
calc μ (f ⁻¹' s) ≤ μ (f ⁻¹' (to_measurable (μ.map f) s)) :
  measure_mono $ preimage_mono $ subset_to_measurable _ _
... = μ.map f (to_measurable (μ.map f) s) :
  (map_apply_of_ae_measurable hf $ measurable_set_to_measurable _ _).symm
... = μ.map f s : measure_to_measurable _

/-- Even if `s` is not measurable, `map f μ s = 0` implies that `μ (f ⁻¹' s) = 0`. -/
lemma preimage_null_of_map_null {f : α → β} (hf : ae_measurable f μ) {s : set β}
  (hs : μ.map f s = 0) : μ (f ⁻¹' s) = 0 :=
nonpos_iff_eq_zero.mp $ (le_map_apply hf s).trans_eq hs

lemma tendsto_ae_map {f : α → β} (hf : ae_measurable f μ) : tendsto f μ.ae (μ.map f).ae :=
λ s hs, preimage_null_of_map_null hf hs

omit m0

/-- Pullback of a `measure`. If `f` sends each `measurable` set to a `measurable` set, then for each
measurable set `s` we have `comap f μ s = μ (f '' s)`. -/
def comap [measurable_space α] (f : α → β) : measure β →ₗ[ℝ≥0∞] measure α :=
if hf : injective f ∧ ∀ s, measurable_set s → measurable_set (f '' s) then
  lift_linear (outer_measure.comap f) $ λ μ s hs t,
  begin
    simp only [coe_to_outer_measure, outer_measure.comap_apply, ← image_inter hf.1,
      image_diff hf.1],
    apply le_to_outer_measure_caratheodory,
    exact hf.2 s hs
  end
else 0

lemma comap_apply {β} [measurable_space α] {mβ : measurable_space β} (f : α → β) (hfi : injective f)
  (hf : ∀ s, measurable_set s → measurable_set (f '' s)) (μ : measure β) (hs : measurable_set s) :
  comap f μ s = μ (f '' s) :=
begin
  rw [comap, dif_pos, lift_linear_apply _ hs, outer_measure.comap_apply, coe_to_outer_measure],
  exact ⟨hfi, hf⟩
end

/-! ### Restricting a measure -/

/-- Restrict a measure `μ` to a set `s` as an `ℝ≥0∞`-linear map. -/
def restrictₗ {m0 : measurable_space α} (s : set α) : measure α →ₗ[ℝ≥0∞] measure α :=
lift_linear (outer_measure.restrict s) $ λ μ s' hs' t,
begin
  suffices : μ (s ∩ t) = μ (s ∩ t ∩ s') + μ (s ∩ t \ s'),
  { simpa [← set.inter_assoc, set.inter_comm _ s, ← inter_diff_assoc] },
  exact le_to_outer_measure_caratheodory _ _ hs' _,
end

/-- Restrict a measure `μ` to a set `s`. -/
def restrict {m0 : measurable_space α} (μ : measure α) (s : set α) : measure α := restrictₗ s μ

@[simp] lemma restrictₗ_apply {m0 : measurable_space α} (s : set α) (μ : measure α) :
  restrictₗ s μ = μ.restrict s :=
rfl

/-- This lemma shows that `restrict` and `to_outer_measure` commute. Note that the LHS has a
restrict on measures and the RHS has a restrict on outer measures. -/
lemma restrict_to_outer_measure_eq_to_outer_measure_restrict (h : measurable_set s) :
    (μ.restrict s).to_outer_measure = outer_measure.restrict s μ.to_outer_measure :=
by simp_rw [restrict, restrictₗ, lift_linear, linear_map.coe_mk, to_measure_to_outer_measure,
  outer_measure.restrict_trim h, μ.trimmed]

lemma restrict_apply₀ (ht : null_measurable_set t (μ.restrict s)) :
  μ.restrict s t = μ (t ∩ s) :=
(to_measure_apply₀ _ _ ht).trans $ by simp only [coe_to_outer_measure, outer_measure.restrict_apply]

/-- If `t` is a measurable set, then the measure of `t` with respect to the restriction of
  the measure to `s` equals the outer measure of `t ∩ s`. An alternate version requiring that `s`
  be measurable instead of `t` exists as `measure.restrict_apply'`. -/
@[simp] lemma restrict_apply (ht : measurable_set t) : μ.restrict s t = μ (t ∩ s) :=
restrict_apply₀ ht.null_measurable_set

/-- Restriction of a measure to a subset is monotone both in set and in measure. -/
lemma restrict_mono' {m0 : measurable_space α} ⦃s s' : set α⦄ ⦃μ ν : measure α⦄
  (hs : s ≤ᵐ[μ] s') (hμν : μ ≤ ν) :
  μ.restrict s ≤ ν.restrict s' :=
assume t ht,
calc μ.restrict s t = μ (t ∩ s) : restrict_apply ht
... ≤ μ (t ∩ s') : measure_mono_ae $ hs.mono $ λ x hx ⟨hxt, hxs⟩, ⟨hxt, hx hxs⟩
... ≤ ν (t ∩ s') : le_iff'.1 hμν (t ∩ s')
... = ν.restrict s' t : (restrict_apply ht).symm

/-- Restriction of a measure to a subset is monotone both in set and in measure. -/
@[mono] lemma restrict_mono {m0 : measurable_space α} ⦃s s' : set α⦄ (hs : s ⊆ s') ⦃μ ν : measure α⦄
  (hμν : μ ≤ ν) :
  μ.restrict s ≤ ν.restrict s' :=
restrict_mono' (ae_of_all _ hs) hμν

lemma restrict_mono_ae (h : s ≤ᵐ[μ] t) : μ.restrict s ≤ μ.restrict t :=
restrict_mono' h (le_refl μ)

lemma restrict_congr_set (h : s =ᵐ[μ] t) : μ.restrict s = μ.restrict t :=
le_antisymm (restrict_mono_ae h.le) (restrict_mono_ae h.symm.le)

/-- If `s` is a measurable set, then the outer measure of `t` with respect to the restriction of
the measure to `s` equals the outer measure of `t ∩ s`. This is an alternate version of
`measure.restrict_apply`, requiring that `s` is measurable instead of `t`. -/
@[simp] lemma restrict_apply' (hs : measurable_set s) : μ.restrict s t = μ (t ∩ s) :=
by rw [← coe_to_outer_measure, measure.restrict_to_outer_measure_eq_to_outer_measure_restrict hs,
      outer_measure.restrict_apply s t _, coe_to_outer_measure]

lemma restrict_apply₀' (hs : null_measurable_set s μ) : μ.restrict s t = μ (t ∩ s) :=
by rw [← restrict_congr_set hs.to_measurable_ae_eq,
  restrict_apply' (measurable_set_to_measurable _ _),
  measure_congr ((ae_eq_refl t).inter hs.to_measurable_ae_eq)]

lemma restrict_le_self : μ.restrict s ≤ μ :=
λ t ht,
calc μ.restrict s t = μ (t ∩ s) : restrict_apply ht
... ≤ μ t : measure_mono $ inter_subset_left t s

variable (μ)

lemma restrict_eq_self (h : s ⊆ t) : μ.restrict t s = μ s :=
(le_iff'.1 restrict_le_self s).antisymm $
calc μ s ≤ μ (to_measurable (μ.restrict t) s ∩ t) :
  measure_mono (subset_inter (subset_to_measurable _ _) h)
... =  μ.restrict t s :
  by rw [← restrict_apply (measurable_set_to_measurable _ _), measure_to_measurable]

@[simp] lemma restrict_apply_self (s : set α):
  (μ.restrict s) s = μ s :=
restrict_eq_self μ subset.rfl

variable {μ}

lemma restrict_apply_univ (s : set α) : μ.restrict s univ = μ s :=
by rw [restrict_apply measurable_set.univ, set.univ_inter]

lemma le_restrict_apply (s t : set α) :
  μ (t ∩ s) ≤ μ.restrict s t :=
calc μ (t ∩ s) = μ.restrict s (t ∩ s) : (restrict_eq_self μ (inter_subset_right _ _)).symm
... ≤ μ.restrict s t : measure_mono (inter_subset_left _ _)

lemma restrict_apply_superset (h : s ⊆ t) : μ.restrict s t = μ s :=
((measure_mono (subset_univ _)).trans_eq $ restrict_apply_univ _).antisymm
  ((restrict_apply_self μ s).symm.trans_le $ measure_mono h)

@[simp] lemma restrict_add {m0 : measurable_space α} (μ ν : measure α) (s : set α) :
  (μ + ν).restrict s = μ.restrict s + ν.restrict s :=
(restrictₗ s).map_add μ ν

@[simp] lemma restrict_zero {m0 : measurable_space α} (s : set α) :
  (0 : measure α).restrict s = 0 :=
(restrictₗ s).map_zero

@[simp] lemma restrict_smul {m0 : measurable_space α} (c : ℝ≥0∞) (μ : measure α) (s : set α) :
  (c • μ).restrict s = c • μ.restrict s :=
(restrictₗ s).map_smul c μ

lemma restrict_restrict₀ (hs : null_measurable_set s (μ.restrict t)) :
  (μ.restrict t).restrict s = μ.restrict (s ∩ t) :=
ext $ λ u hu, by simp only [set.inter_assoc, restrict_apply hu,
  restrict_apply₀ (hu.null_measurable_set.inter hs)]

@[simp] lemma restrict_restrict (hs : measurable_set s) :
  (μ.restrict t).restrict s = μ.restrict (s ∩ t) :=
restrict_restrict₀ hs.null_measurable_set

lemma restrict_restrict_of_subset (h : s ⊆ t) :
  (μ.restrict t).restrict s = μ.restrict s :=
begin
  ext1 u hu,
  rw [restrict_apply hu, restrict_apply hu, restrict_eq_self],
  exact (inter_subset_right _ _).trans h
end

lemma restrict_restrict₀' (ht : null_measurable_set t μ) :
  (μ.restrict t).restrict s = μ.restrict (s ∩ t) :=
ext $ λ u hu, by simp only [restrict_apply hu, restrict_apply₀' ht, inter_assoc]

lemma restrict_restrict' (ht : measurable_set t) :
  (μ.restrict t).restrict s = μ.restrict (s ∩ t) :=
restrict_restrict₀' ht.null_measurable_set

lemma restrict_comm (hs : measurable_set s) :
  (μ.restrict t).restrict s = (μ.restrict s).restrict t :=
by rw [restrict_restrict hs, restrict_restrict' hs, inter_comm]

lemma restrict_apply_eq_zero (ht : measurable_set t) : μ.restrict s t = 0 ↔ μ (t ∩ s) = 0 :=
by rw [restrict_apply ht]

lemma measure_inter_eq_zero_of_restrict (h : μ.restrict s t = 0) : μ (t ∩ s) = 0 :=
nonpos_iff_eq_zero.1 (h ▸ le_restrict_apply _ _)

lemma restrict_apply_eq_zero' (hs : measurable_set s) : μ.restrict s t = 0 ↔ μ (t ∩ s) = 0 :=
by rw [restrict_apply' hs]

@[simp] lemma restrict_eq_zero : μ.restrict s = 0 ↔ μ s = 0 :=
by rw [← measure_univ_eq_zero, restrict_apply_univ]

lemma restrict_zero_set {s : set α} (h : μ s = 0) :
  μ.restrict s = 0 :=
restrict_eq_zero.2 h

@[simp] lemma restrict_empty : μ.restrict ∅ = 0 := restrict_zero_set measure_empty

@[simp] lemma restrict_univ : μ.restrict univ = μ := ext $ λ s hs, by simp [hs]

lemma restrict_union_add_inter₀ (s : set α) (ht : null_measurable_set t μ) :
  μ.restrict (s ∪ t) + μ.restrict (s ∩ t) = μ.restrict s + μ.restrict t :=
begin
  ext1 u hu,
  simp only [add_apply, restrict_apply hu, inter_union_distrib_left],
  convert measure_union_add_inter₀ (u ∩ s) (hu.null_measurable_set.inter ht) using 3,
  rw [set.inter_left_comm (u ∩ s), set.inter_assoc, ← set.inter_assoc u u, set.inter_self]
end

lemma restrict_union_add_inter (s : set α) (ht : measurable_set t) :
  μ.restrict (s ∪ t) + μ.restrict (s ∩ t) = μ.restrict s + μ.restrict t :=
restrict_union_add_inter₀ s ht.null_measurable_set

lemma restrict_union_add_inter' (hs : measurable_set s) (t : set α) :
  μ.restrict (s ∪ t) + μ.restrict (s ∩ t) = μ.restrict s + μ.restrict t :=
by simpa only [union_comm, inter_comm, add_comm] using restrict_union_add_inter t hs

lemma restrict_union₀ (h : ae_disjoint μ s t) (ht : null_measurable_set t μ) :
  μ.restrict (s ∪ t) = μ.restrict s + μ.restrict t :=
by simp [← restrict_union_add_inter₀ s ht, restrict_zero_set h]

lemma restrict_union (h : disjoint s t) (ht : measurable_set t) :
  μ.restrict (s ∪ t) = μ.restrict s + μ.restrict t :=
restrict_union₀ h.ae_disjoint ht.null_measurable_set

lemma restrict_union' (h : disjoint s t) (hs : measurable_set s) :
  μ.restrict (s ∪ t) = μ.restrict s + μ.restrict t :=
by rw [union_comm, restrict_union h.symm hs, add_comm]

@[simp] lemma restrict_add_restrict_compl (hs : measurable_set s) :
  μ.restrict s + μ.restrict sᶜ = μ :=
by rw [← restrict_union (@disjoint_compl_right (set α) _ _) hs.compl,
    union_compl_self, restrict_univ]

@[simp] lemma restrict_compl_add_restrict (hs : measurable_set s) :
  μ.restrict sᶜ + μ.restrict s = μ :=
by rw [add_comm, restrict_add_restrict_compl hs]

lemma restrict_union_le (s s' : set α) : μ.restrict (s ∪ s') ≤ μ.restrict s + μ.restrict s' :=
begin
  intros t ht,
  suffices : μ (t ∩ s ∪ t ∩ s') ≤ μ (t ∩ s) + μ (t ∩ s'),
    by simpa [ht, inter_union_distrib_left],
  apply measure_union_le
end

lemma restrict_Union_apply_ae [encodable ι] {s : ι → set α}
  (hd : pairwise (ae_disjoint μ on s))
  (hm : ∀ i, null_measurable_set (s i) μ) {t : set α} (ht : measurable_set t) :
  μ.restrict (⋃ i, s i) t = ∑' i, μ.restrict (s i) t :=
begin
  simp only [restrict_apply, ht, inter_Union],
  exact measure_Union₀ (hd.mono $ λ i j h, h.mono (inter_subset_right _ _) (inter_subset_right _ _))
    (λ i, (ht.null_measurable_set.inter (hm i)))
end

lemma restrict_Union_apply [encodable ι] {s : ι → set α} (hd : pairwise (disjoint on s))
  (hm : ∀ i, measurable_set (s i)) {t : set α} (ht : measurable_set t) :
  μ.restrict (⋃ i, s i) t = ∑' i, μ.restrict (s i) t :=
restrict_Union_apply_ae (hd.mono $ λ i j h, h.ae_disjoint) (λ i, (hm i).null_measurable_set) ht

lemma restrict_Union_apply_eq_supr [encodable ι] {s : ι → set α}
  (hd : directed (⊆) s) {t : set α} (ht : measurable_set t) :
  μ.restrict (⋃ i, s i) t = ⨆ i, μ.restrict (s i) t :=
begin
  simp only [restrict_apply ht, inter_Union],
  rw [measure_Union_eq_supr],
  exacts [hd.mono_comp _ (λ s₁ s₂, inter_subset_inter_right _)]
end

/-- The restriction of the pushforward measure is the pushforward of the restriction. For a version
assuming only `ae_measurable`, see `restrict_map_of_ae_measurable`. -/
lemma restrict_map {f : α → β} (hf : measurable f) {s : set β} (hs : measurable_set s) :
  (μ.map f).restrict s = (μ.restrict $ f ⁻¹' s).map f  :=
ext $ λ t ht, by simp [*, hf ht]

lemma restrict_to_measurable (h : μ s ≠ ∞) : μ.restrict (to_measurable μ s) = μ.restrict s :=
ext $ λ t ht, by rw [restrict_apply ht, restrict_apply ht, inter_comm,
  measure_to_measurable_inter ht h, inter_comm]

lemma restrict_eq_self_of_ae_mem {m0 : measurable_space α} ⦃s : set α⦄ ⦃μ : measure α⦄
  (hs : ∀ᵐ x ∂μ, x ∈ s) :
  μ.restrict s = μ :=
calc μ.restrict s = μ.restrict univ : restrict_congr_set (eventually_eq_univ.mpr hs)
... = μ : restrict_univ

lemma restrict_congr_meas (hs : measurable_set s) :
  μ.restrict s = ν.restrict s ↔ ∀ t ⊆ s, measurable_set t → μ t = ν t :=
⟨λ H t hts ht,
   by rw [← inter_eq_self_of_subset_left hts, ← restrict_apply ht, H, restrict_apply ht],
 λ H, ext $ λ t ht,
   by rw [restrict_apply ht, restrict_apply ht, H _ (inter_subset_right _ _) (ht.inter hs)]⟩

lemma restrict_congr_mono (hs : s ⊆ t) (h : μ.restrict t = ν.restrict t) :
  μ.restrict s = ν.restrict s :=
by rw [← restrict_restrict_of_subset hs, h, restrict_restrict_of_subset hs]

/-- If two measures agree on all measurable subsets of `s` and `t`, then they agree on all
measurable subsets of `s ∪ t`. -/
lemma restrict_union_congr :
  μ.restrict (s ∪ t) = ν.restrict (s ∪ t) ↔
    μ.restrict s = ν.restrict s ∧ μ.restrict t = ν.restrict t :=
begin
  refine ⟨λ h, ⟨restrict_congr_mono (subset_union_left _ _) h,
    restrict_congr_mono (subset_union_right _ _) h⟩, _⟩,
  rintro ⟨hs, ht⟩,
  ext1 u hu,
  simp only [restrict_apply hu, inter_union_distrib_left],
  rcases exists_measurable_superset₂ μ ν (u ∩ s) with ⟨US, hsub, hm, hμ, hν⟩,
  calc μ (u ∩ s ∪ u ∩ t) = μ (US ∪ u ∩ t) :
    measure_union_congr_of_subset hsub hμ.le subset.rfl le_rfl
  ... = μ US + μ (u ∩ t \ US) : (measure_add_diff hm _).symm
  ... = restrict μ s u + restrict μ t (u \ US) :
    by simp only [restrict_apply, hu, hu.diff hm, hμ, ← inter_comm t, inter_diff_assoc]
  ... = restrict ν s u + restrict ν t (u \ US) : by rw [hs, ht]
  ... = ν US + ν (u ∩ t \ US) :
    by simp only [restrict_apply, hu, hu.diff hm, hν, ← inter_comm t, inter_diff_assoc]
  ... = ν (US ∪ u ∩ t) : measure_add_diff hm _
  ... = ν (u ∩ s ∪ u ∩ t) :
    eq.symm $ measure_union_congr_of_subset hsub hν.le subset.rfl le_rfl
end

lemma restrict_finset_bUnion_congr {s : finset ι} {t : ι → set α} :
  μ.restrict (⋃ i ∈ s, t i) = ν.restrict (⋃ i ∈ s, t i) ↔
    ∀ i ∈ s, μ.restrict (t i) = ν.restrict (t i) :=
begin
  induction s using finset.induction_on with i s hi hs, { simp },
  simp only [forall_eq_or_imp, Union_Union_eq_or_left, finset.mem_insert],
  rw [restrict_union_congr, ← hs]
end

lemma restrict_Union_congr [encodable ι] {s : ι → set α} :
  μ.restrict (⋃ i, s i) = ν.restrict (⋃ i, s i) ↔
    ∀ i, μ.restrict (s i) = ν.restrict (s i) :=
begin
  refine ⟨λ h i, restrict_congr_mono (subset_Union _ _) h, λ h, _⟩,
  ext1 t ht,
  have D : directed (⊆) (λ t : finset ι, ⋃ i ∈ t, s i) :=
    directed_of_sup (λ t₁ t₂ ht, bUnion_subset_bUnion_left ht),
  rw [Union_eq_Union_finset],
  simp only [restrict_Union_apply_eq_supr D ht,
    restrict_finset_bUnion_congr.2 (λ i hi, h i)],
end

lemma restrict_bUnion_congr {s : set ι} {t : ι → set α} (hc : countable s) :
  μ.restrict (⋃ i ∈ s, t i) = ν.restrict (⋃ i ∈ s, t i) ↔
    ∀ i ∈ s, μ.restrict (t i) = ν.restrict (t i) :=
begin
  haveI := hc.to_encodable,
  simp only [bUnion_eq_Union, set_coe.forall', restrict_Union_congr]
end

lemma restrict_sUnion_congr {S : set (set α)} (hc : countable S) :
  μ.restrict (⋃₀ S) = ν.restrict (⋃₀ S) ↔ ∀ s ∈ S, μ.restrict s = ν.restrict s :=
by rw [sUnion_eq_bUnion, restrict_bUnion_congr hc]

/-- This lemma shows that `Inf` and `restrict` commute for measures. -/
lemma restrict_Inf_eq_Inf_restrict {m0 : measurable_space α} {m : set (measure α)}
  (hm : m.nonempty) (ht : measurable_set t) :
  (Inf m).restrict t = Inf ((λ μ : measure α, μ.restrict t) '' m) :=
begin
  ext1 s hs,
  simp_rw [Inf_apply hs, restrict_apply hs, Inf_apply (measurable_set.inter hs ht), set.image_image,
    restrict_to_outer_measure_eq_to_outer_measure_restrict ht, ← set.image_image _ to_outer_measure,
    ← outer_measure.restrict_Inf_eq_Inf_restrict _ (hm.image _),
    outer_measure.restrict_apply]
end

/-! ### Extensionality results -/

/-- Two measures are equal if they have equal restrictions on a spanning collection of sets
  (formulated using `Union`). -/
lemma ext_iff_of_Union_eq_univ [encodable ι] {s : ι → set α} (hs : (⋃ i, s i) = univ) :
  μ = ν ↔ ∀ i, μ.restrict (s i) = ν.restrict (s i) :=
by rw [← restrict_Union_congr, hs, restrict_univ, restrict_univ]

alias ext_iff_of_Union_eq_univ ↔ _ measure_theory.measure.ext_of_Union_eq_univ

/-- Two measures are equal if they have equal restrictions on a spanning collection of sets
  (formulated using `bUnion`). -/
lemma ext_iff_of_bUnion_eq_univ {S : set ι} {s : ι → set α} (hc : countable S)
  (hs : (⋃ i ∈ S, s i) = univ) :
  μ = ν ↔ ∀ i ∈ S, μ.restrict (s i) = ν.restrict (s i) :=
by rw [← restrict_bUnion_congr hc, hs, restrict_univ, restrict_univ]

alias ext_iff_of_bUnion_eq_univ ↔ _ measure_theory.measure.ext_of_bUnion_eq_univ

/-- Two measures are equal if they have equal restrictions on a spanning collection of sets
  (formulated using `sUnion`). -/
lemma ext_iff_of_sUnion_eq_univ {S : set (set α)} (hc : countable S) (hs : (⋃₀ S) = univ) :
  μ = ν ↔ ∀ s ∈ S, μ.restrict s = ν.restrict s :=
ext_iff_of_bUnion_eq_univ hc $ by rwa ← sUnion_eq_bUnion

alias ext_iff_of_sUnion_eq_univ ↔ _ measure_theory.measure.ext_of_sUnion_eq_univ

lemma ext_of_generate_from_of_cover {S T : set (set α)}
  (h_gen : ‹_› = generate_from S) (hc : countable T)
  (h_inter : is_pi_system S) (hU : ⋃₀ T = univ) (htop : ∀ t ∈ T, μ t ≠ ∞)
  (ST_eq : ∀ (t ∈ T) (s ∈ S), μ (s ∩ t) = ν (s ∩ t)) (T_eq : ∀ t ∈ T, μ t = ν t) :
  μ = ν :=
begin
  refine ext_of_sUnion_eq_univ hc hU (λ t ht, _),
  ext1 u hu,
  simp only [restrict_apply hu],
  refine induction_on_inter h_gen h_inter _ (ST_eq t ht) _ _ hu,
  { simp only [set.empty_inter, measure_empty] },
  { intros v hv hvt,
    have := T_eq t ht,
    rw [set.inter_comm] at hvt ⊢,
    rwa [← measure_inter_add_diff t hv, ← measure_inter_add_diff t hv, ← hvt,
      ennreal.add_right_inj] at this,
    exact ne_top_of_le_ne_top (htop t ht) (measure_mono $ set.inter_subset_left _ _) },
  { intros f hfd hfm h_eq,
    simp only [← restrict_apply (hfm _), ← restrict_apply (measurable_set.Union hfm)] at h_eq ⊢,
    simp only [measure_Union hfd hfm, h_eq] }
end

/-- Two measures are equal if they are equal on the π-system generating the σ-algebra,
  and they are both finite on a increasing spanning sequence of sets in the π-system.
  This lemma is formulated using `sUnion`. -/
lemma ext_of_generate_from_of_cover_subset {S T : set (set α)}
  (h_gen : ‹_› = generate_from S) (h_inter : is_pi_system S)
  (h_sub : T ⊆ S) (hc : countable T) (hU : ⋃₀ T = univ) (htop : ∀ s ∈ T, μ s ≠ ∞)
  (h_eq : ∀ s ∈ S, μ s = ν s) :
  μ = ν :=
begin
  refine ext_of_generate_from_of_cover h_gen hc h_inter hU htop _ (λ t ht, h_eq t (h_sub ht)),
  intros t ht s hs, cases (s ∩ t).eq_empty_or_nonempty with H H,
  { simp only [H, measure_empty] },
  { exact h_eq _ (h_inter _ hs _ (h_sub ht) H) }
end

/-- Two measures are equal if they are equal on the π-system generating the σ-algebra,
  and they are both finite on a increasing spanning sequence of sets in the π-system.
  This lemma is formulated using `Union`.
  `finite_spanning_sets_in.ext` is a reformulation of this lemma. -/
lemma ext_of_generate_from_of_Union (C : set (set α)) (B : ℕ → set α)
  (hA : ‹_› = generate_from C) (hC : is_pi_system C) (h1B : (⋃ i, B i) = univ)
  (h2B : ∀ i, B i ∈ C) (hμB : ∀ i, μ (B i) ≠ ∞) (h_eq : ∀ s ∈ C, μ s = ν s) : μ = ν :=
begin
  refine ext_of_generate_from_of_cover_subset hA hC _ (countable_range B) h1B _ h_eq,
  { rintro _ ⟨i, rfl⟩, apply h2B },
  { rintro _ ⟨i, rfl⟩, apply hμB }
end

section dirac
variable [measurable_space α]

/-- The dirac measure. -/
def dirac (a : α) : measure α :=
(outer_measure.dirac a).to_measure (by simp)

instance : measure_space punit := ⟨dirac punit.star⟩

lemma le_dirac_apply {a} : s.indicator 1 a ≤ dirac a s :=
outer_measure.dirac_apply a s ▸ le_to_measure_apply _ _ _

@[simp] lemma dirac_apply' (a : α) (hs : measurable_set s) :
  dirac a s = s.indicator 1 a :=
to_measure_apply _ _ hs

@[simp] lemma dirac_apply_of_mem {a : α} (h : a ∈ s) :
  dirac a s = 1 :=
begin
  have : ∀ t : set α, a ∈ t → t.indicator (1 : α → ℝ≥0∞) a = 1,
    from λ t ht, indicator_of_mem ht 1,
  refine le_antisymm (this univ trivial ▸ _) (this s h ▸ le_dirac_apply),
  rw [← dirac_apply' a measurable_set.univ],
  exact measure_mono (subset_univ s)
end

@[simp] lemma dirac_apply [measurable_singleton_class α] (a : α) (s : set α) :
  dirac a s = s.indicator 1 a :=
begin
  by_cases h : a ∈ s, by rw [dirac_apply_of_mem h, indicator_of_mem h, pi.one_apply],
  rw [indicator_of_not_mem h, ← nonpos_iff_eq_zero],
  calc dirac a s ≤ dirac a {a}ᶜ : measure_mono (subset_compl_comm.1 $ singleton_subset_iff.2 h)
             ... = 0            : by simp [dirac_apply' _ (measurable_set_singleton _).compl]
end

lemma map_dirac {f : α → β} (hf : measurable f) (a : α) :
  (dirac a).map f  = dirac (f a) :=
ext $ λ s hs, by simp [hs, map_apply hf hs, hf hs, indicator_apply]

@[simp] lemma restrict_singleton (μ : measure α) (a : α) : μ.restrict {a} = μ {a} • dirac a :=
begin
  ext1 s hs,
  by_cases ha : a ∈ s,
  { have : s ∩ {a} = {a}, by simpa,
    simp * },
  { have : s ∩ {a} = ∅, from inter_singleton_eq_empty.2 ha,
    simp * }
end

end dirac

section sum
include m0

/-- Sum of an indexed family of measures. -/
def sum (f : ι → measure α) : measure α :=
(outer_measure.sum (λ i, (f i).to_outer_measure)).to_measure $
le_trans
  (by exact le_infi (λ i, le_to_outer_measure_caratheodory _))
  (outer_measure.le_sum_caratheodory _)

lemma le_sum_apply (f : ι → measure α) (s : set α) : (∑' i, f i s) ≤ sum f s :=
le_to_measure_apply _ _ _

@[simp] lemma sum_apply (f : ι → measure α) {s : set α} (hs : measurable_set s) :
  sum f s = ∑' i, f i s :=
to_measure_apply _ _ hs

lemma le_sum (μ : ι → measure α) (i : ι) : μ i ≤ sum μ :=
λ s hs, by simp only [sum_apply μ hs, ennreal.le_tsum i]

@[simp] lemma sum_apply_eq_zero [encodable ι] {μ : ι → measure α} {s : set α} :
  sum μ s = 0 ↔ ∀ i, μ i s = 0 :=
begin
  refine ⟨λ h i, nonpos_iff_eq_zero.1 $ h ▸ le_iff'.1 (le_sum μ i) _, λ h, nonpos_iff_eq_zero.1 _⟩,
  rcases exists_measurable_superset_forall_eq μ s with ⟨t, hst, htm, ht⟩,
  calc sum μ s ≤ sum μ t : measure_mono hst
           ... = 0       : by simp *
end

lemma sum_apply_eq_zero' {μ : ι → measure α} {s : set α} (hs : measurable_set s) :
  sum μ s = 0 ↔ ∀ i, μ i s = 0 :=
by simp [hs]

lemma ae_sum_iff [encodable ι] {μ : ι → measure α} {p : α → Prop} :
  (∀ᵐ x ∂(sum μ), p x) ↔ ∀ i, ∀ᵐ x ∂(μ i), p x :=
sum_apply_eq_zero

lemma ae_sum_iff' {μ : ι → measure α} {p : α → Prop} (h : measurable_set {x | p x}) :
  (∀ᵐ x ∂(sum μ), p x) ↔ ∀ i, ∀ᵐ x ∂(μ i), p x :=
sum_apply_eq_zero' h.compl

@[simp] lemma sum_fintype [fintype ι] (μ : ι → measure α) : sum μ = ∑ i, μ i :=
by { ext1 s hs, simp only [sum_apply, finset_sum_apply, hs, tsum_fintype] }

@[simp] lemma sum_coe_finset (s : finset ι) (μ : ι → measure α) :
  sum (λ i : s, μ i) = ∑ i in s, μ i :=
by rw [sum_fintype, finset.sum_coe_sort s μ]

@[simp] lemma ae_sum_eq [encodable ι] (μ : ι → measure α) : (sum μ).ae = ⨆ i, (μ i).ae :=
filter.ext $ λ s, ae_sum_iff.trans mem_supr.symm

@[simp] lemma sum_bool (f : bool → measure α) : sum f = f tt + f ff :=
by rw [sum_fintype, fintype.sum_bool]

@[simp] lemma sum_cond (μ ν : measure α) : sum (λ b, cond b μ ν) = μ + ν := sum_bool _

@[simp] lemma restrict_sum (μ : ι → measure α) {s : set α} (hs : measurable_set s) :
  (sum μ).restrict s = sum (λ i, (μ i).restrict s) :=
ext $ λ t ht, by simp only [sum_apply, restrict_apply, ht, ht.inter hs]

@[simp] lemma sum_of_empty [is_empty ι] (μ : ι → measure α) : sum μ = 0 :=
by rw [← measure_univ_eq_zero, sum_apply _ measurable_set.univ, tsum_empty]

lemma sum_add_sum_compl (s : set ι) (μ : ι → measure α) :
  sum (λ i : s, μ i) + sum (λ i : sᶜ, μ i) = sum μ :=
begin
  ext1 t ht,
  simp only [add_apply, sum_apply _ ht],
  exact @tsum_add_tsum_compl ℝ≥0∞ ι _ _ _ (λ i, μ i t) _ s ennreal.summable ennreal.summable
end

lemma sum_congr {μ ν : ℕ → measure α} (h : ∀ n, μ n = ν n) : sum μ = sum ν :=
congr_arg sum (funext h)

lemma sum_add_sum (μ ν : ℕ → measure α) : sum μ + sum ν = sum (λ n, μ n + ν n) :=
begin
  ext1 s hs,
  simp only [add_apply, sum_apply _ hs, pi.add_apply, coe_add,
             tsum_add ennreal.summable ennreal.summable],
end

/-- If `f` is a map with encodable codomain, then `μ.map f` is the sum of Dirac measures -/
lemma map_eq_sum [encodable β] [measurable_singleton_class β]
  (μ : measure α) (f : α → β) (hf : measurable f) :
  μ.map f = sum (λ b : β, μ (f ⁻¹' {b}) • dirac b) :=
begin
  ext1 s hs,
  have : ∀ y ∈ s, measurable_set (f ⁻¹' {y}), from λ y _, hf (measurable_set_singleton _),
  simp [← tsum_measure_preimage_singleton (countable_encodable s) this, *,
    tsum_subtype s (λ b, μ (f ⁻¹' {b})), ← indicator_mul_right s (λ b, μ (f ⁻¹' {b}))]
end

/-- A measure on an encodable type is a sum of dirac measures. -/
@[simp] lemma sum_smul_dirac [encodable α] [measurable_singleton_class α] (μ : measure α) :
  sum (λ a, μ {a} • dirac a) = μ :=
by simpa using (map_eq_sum μ id measurable_id).symm

omit m0
end sum

lemma restrict_Union_ae [encodable ι] {s : ι → set α} (hd : pairwise (ae_disjoint μ on s))
  (hm : ∀ i, null_measurable_set (s i) μ) :
  μ.restrict (⋃ i, s i) = sum (λ i, μ.restrict (s i)) :=
ext $ λ t ht, by simp only [sum_apply _ ht, restrict_Union_apply_ae hd hm ht]

lemma restrict_Union [encodable ι] {s : ι → set α} (hd : pairwise (disjoint on s))
  (hm : ∀ i, measurable_set (s i)) :
  μ.restrict (⋃ i, s i) = sum (λ i, μ.restrict (s i)) :=
ext $ λ t ht, by simp only [sum_apply _ ht, restrict_Union_apply hd hm ht]

lemma restrict_Union_le [encodable ι] {s : ι → set α} :
  μ.restrict (⋃ i, s i) ≤ sum (λ i, μ.restrict (s i)) :=
begin
  intros t ht,
  suffices : μ (⋃ i, t ∩ s i) ≤ ∑' i, μ (t ∩ s i), by simpa [ht, inter_Union],
  apply measure_Union_le
end

section count

variable [measurable_space α]

/-- Counting measure on any measurable space. -/
def count : measure α := sum dirac

lemma le_count_apply : (∑' i : s, 1 : ℝ≥0∞) ≤ count s :=
calc (∑' i : s, 1 : ℝ≥0∞) = ∑' i, indicator s 1 i : tsum_subtype s 1
... ≤ ∑' i, dirac i s : ennreal.tsum_le_tsum $ λ x, le_dirac_apply
... ≤ count s : le_sum_apply _ _

lemma count_apply (hs : measurable_set s) : count s = ∑' i : s, 1 :=
by simp only [count, sum_apply, hs, dirac_apply', ← tsum_subtype s 1, pi.one_apply]

@[simp] lemma count_empty : count (∅ : set α) = 0 :=
by rw [count_apply measurable_set.empty, tsum_empty]

@[simp] lemma count_apply_finset [measurable_singleton_class α] (s : finset α) :
  count (↑s : set α) = s.card :=
calc count (↑s : set α) = ∑' i : (↑s : set α), 1 : count_apply s.measurable_set
                    ... = ∑ i in s, 1 : s.tsum_subtype 1
                    ... = s.card : by simp

lemma count_apply_finite [measurable_singleton_class α] (s : set α) (hs : finite s) :
  count s = hs.to_finset.card :=
by rw [← count_apply_finset, finite.coe_to_finset]

/-- `count` measure evaluates to infinity at infinite sets. -/
lemma count_apply_infinite (hs : s.infinite) : count s = ∞ :=
begin
  refine top_unique (le_of_tendsto' ennreal.tendsto_nat_nhds_top $ λ n, _),
  rcases hs.exists_subset_card_eq n with ⟨t, ht, rfl⟩,
  calc (t.card : ℝ≥0∞) = ∑ i in t, 1 : by simp
  ... = ∑' i : (t : set α), 1 : (t.tsum_subtype 1).symm
  ... ≤ count (t : set α) : le_count_apply
  ... ≤ count s : measure_mono ht
end

variable [measurable_singleton_class α]

@[simp] lemma count_apply_eq_top : count s = ∞ ↔ s.infinite :=
begin
  by_cases hs : s.finite,
  { simp [set.infinite, hs, count_apply_finite] },
  { change s.infinite at hs,
    simp [hs, count_apply_infinite] }
end

@[simp] lemma count_apply_lt_top : count s < ∞ ↔ s.finite :=
calc count s < ∞ ↔ count s ≠ ∞ : lt_top_iff_ne_top
             ... ↔ ¬s.infinite : not_congr count_apply_eq_top
             ... ↔ s.finite    : not_not

lemma empty_of_count_eq_zero (hsc : count s = 0) : s = ∅ :=
begin
  have hs : s.finite,
  { rw [← count_apply_lt_top, hsc],
    exact with_top.zero_lt_top },
  rw count_apply_finite _ hs at hsc,
  simpa using hsc,
end

@[simp] lemma count_eq_zero_iff : count s = 0 ↔ s = ∅ :=
⟨empty_of_count_eq_zero, λ h, h.symm ▸ count_empty⟩

lemma count_ne_zero (hs' : s.nonempty) : count s ≠ 0 :=
begin
  rw [ne.def, count_eq_zero_iff],
  exact hs'.ne_empty,
end

@[simp] lemma count_singleton (a : α) : count ({a} : set α) = 1 :=
begin
  rw [count_apply_finite ({a} : set α) (set.finite_singleton _), set.finite.to_finset],
  simp,
end

end count

/-! ### Absolute continuity -/

/-- We say that `μ` is absolutely continuous with respect to `ν`, or that `μ` is dominated by `ν`,
  if `ν(A) = 0` implies that `μ(A) = 0`. -/
def absolutely_continuous {m0 : measurable_space α} (μ ν : measure α) : Prop :=
∀ ⦃s : set α⦄, ν s = 0 → μ s = 0

localized "infix ` ≪ `:50 := measure_theory.measure.absolutely_continuous" in measure_theory

lemma absolutely_continuous_of_le (h : μ ≤ ν) : μ ≪ ν :=
λ s hs, nonpos_iff_eq_zero.1 $ hs ▸ le_iff'.1 h s

alias absolutely_continuous_of_le ← has_le.le.absolutely_continuous

lemma absolutely_continuous_of_eq (h : μ = ν) : μ ≪ ν :=
h.le.absolutely_continuous

alias absolutely_continuous_of_eq ← eq.absolutely_continuous

namespace absolutely_continuous

lemma mk (h : ∀ ⦃s : set α⦄, measurable_set s → ν s = 0 → μ s = 0) : μ ≪ ν :=
begin
  intros s hs,
  rcases exists_measurable_superset_of_null hs with ⟨t, h1t, h2t, h3t⟩,
  exact measure_mono_null h1t (h h2t h3t),
end

@[refl] protected lemma refl {m0 : measurable_space α} (μ : measure α) : μ ≪ μ :=
rfl.absolutely_continuous

protected lemma rfl : μ ≪ μ := λ s hs, hs

instance [measurable_space α] : is_refl (measure α) (≪) := ⟨λ μ, absolutely_continuous.rfl⟩

@[trans] protected lemma trans (h1 : μ₁ ≪ μ₂) (h2 : μ₂ ≪ μ₃) : μ₁ ≪ μ₃ :=
λ s hs, h1 $ h2 hs

@[mono] protected lemma map (h : μ ≪ ν) {f : α → β} (hf : measurable f) : μ.map f ≪ ν.map f :=
absolutely_continuous.mk $ λ s hs, by simpa [hf, hs] using @h _

protected lemma smul [monoid R] [distrib_mul_action R ℝ≥0∞] [is_scalar_tower R ℝ≥0∞ ℝ≥0∞]
  (h : μ ≪ ν) (c : R) : c • μ ≪ ν :=
λ s hνs, by simp only [h hνs, smul_eq_mul, smul_apply, smul_zero]

end absolutely_continuous

lemma absolutely_continuous_of_le_smul {μ' : measure α} {c : ℝ≥0∞} (hμ'_le : μ' ≤ c • μ) :
  μ' ≪ μ :=
(measure.absolutely_continuous_of_le hμ'_le).trans (measure.absolutely_continuous.rfl.smul c)

lemma ae_le_iff_absolutely_continuous : μ.ae ≤ ν.ae ↔ μ ≪ ν :=
⟨λ h s, by { rw [measure_zero_iff_ae_nmem, measure_zero_iff_ae_nmem], exact λ hs, h hs },
  λ h s hs, h hs⟩

alias ae_le_iff_absolutely_continuous ↔ has_le.le.absolutely_continuous_of_ae
  measure_theory.measure.absolutely_continuous.ae_le
alias absolutely_continuous.ae_le ← ae_mono'

lemma absolutely_continuous.ae_eq (h : μ ≪ ν) {f g : α → δ} (h' : f =ᵐ[ν] g) : f =ᵐ[μ] g :=
h.ae_le h'

/-! ### Quasi measure preserving maps (a.k.a. non-singular maps) -/

/-- A map `f : α → β` is said to be *quasi measure preserving* (a.k.a. non-singular) w.r.t. measures
`μa` and `μb` if it is measurable and `μb s = 0` implies `μa (f ⁻¹' s) = 0`. -/
@[protect_proj]
structure quasi_measure_preserving {m0 : measurable_space α} (f : α → β)
  (μa : measure α . volume_tac) (μb : measure β . volume_tac) : Prop :=
(measurable : measurable f)
(absolutely_continuous : μa.map f ≪ μb)

namespace quasi_measure_preserving

protected lemma id {m0 : measurable_space α} (μ : measure α) : quasi_measure_preserving id μ μ :=
⟨measurable_id, map_id.absolutely_continuous⟩

variables {μa μa' : measure α} {μb μb' : measure β} {μc : measure γ} {f : α → β}

protected lemma _root_.measurable.quasi_measure_preserving {m0 : measurable_space α}
  (hf : measurable f) (μ : measure α) : quasi_measure_preserving f μ (μ.map f) :=
⟨hf, absolutely_continuous.rfl⟩

lemma mono_left (h : quasi_measure_preserving f μa μb)
  (ha : μa' ≪ μa) : quasi_measure_preserving f μa' μb :=
⟨h.1, (ha.map h.1).trans h.2⟩

lemma mono_right (h : quasi_measure_preserving f μa μb)
  (ha : μb ≪ μb') : quasi_measure_preserving f μa μb' :=
⟨h.1, h.2.trans ha⟩

@[mono] lemma mono (ha : μa' ≪ μa) (hb : μb ≪ μb') (h : quasi_measure_preserving f μa μb) :
  quasi_measure_preserving f μa' μb' :=
(h.mono_left ha).mono_right hb

protected lemma comp {g : β → γ} {f : α → β} (hg : quasi_measure_preserving g μb μc)
  (hf : quasi_measure_preserving f μa μb) :
  quasi_measure_preserving (g ∘ f) μa μc :=
⟨hg.measurable.comp hf.measurable, by { rw ← map_map hg.1 hf.1, exact (hf.2.map hg.1).trans hg.2 }⟩

protected lemma iterate {f : α → α} (hf : quasi_measure_preserving f μa μa) :
  ∀ n, quasi_measure_preserving (f^[n]) μa μa
| 0 := quasi_measure_preserving.id μa
| (n + 1) := (iterate n).comp hf

protected lemma ae_measurable (hf : quasi_measure_preserving f μa μb) : ae_measurable f μa :=
hf.1.ae_measurable

lemma ae_map_le (h : quasi_measure_preserving f μa μb) : (μa.map f).ae ≤ μb.ae :=
h.2.ae_le

lemma tendsto_ae (h : quasi_measure_preserving f μa μb) : tendsto f μa.ae μb.ae :=
(tendsto_ae_map h.ae_measurable).mono_right h.ae_map_le

lemma ae (h : quasi_measure_preserving f μa μb) {p : β → Prop} (hg : ∀ᵐ x ∂μb, p x) :
  ∀ᵐ x ∂μa, p (f x) :=
h.tendsto_ae hg

lemma ae_eq (h : quasi_measure_preserving f μa μb) {g₁ g₂ : β → δ} (hg : g₁ =ᵐ[μb] g₂) :
  g₁ ∘ f =ᵐ[μa] g₂ ∘ f :=
h.ae hg

lemma preimage_null (h : quasi_measure_preserving f μa μb) {s : set β} (hs : μb s = 0) :
  μa (f ⁻¹' s) = 0 :=
preimage_null_of_map_null h.ae_measurable (h.2 hs)

end quasi_measure_preserving

/-! ### The `cofinite` filter -/

/-- The filter of sets `s` such that `sᶜ` has finite measure. -/
def cofinite {m0 : measurable_space α} (μ : measure α) : filter α :=
{ sets := {s | μ sᶜ < ∞},
  univ_sets := by simp,
  inter_sets := λ s t hs ht, by { simp only [compl_inter, mem_set_of_eq],
    calc μ (sᶜ ∪ tᶜ) ≤ μ sᶜ + μ tᶜ : measure_union_le _ _
                ... < ∞ : ennreal.add_lt_top.2 ⟨hs, ht⟩ },
  sets_of_superset := λ s t hs hst, lt_of_le_of_lt (measure_mono $ compl_subset_compl.2 hst) hs }

lemma mem_cofinite : s ∈ μ.cofinite ↔ μ sᶜ < ∞ := iff.rfl

lemma compl_mem_cofinite : sᶜ ∈ μ.cofinite ↔ μ s < ∞ :=
by rw [mem_cofinite, compl_compl]

lemma eventually_cofinite {p : α → Prop} : (∀ᶠ x in μ.cofinite, p x) ↔ μ {x | ¬p x} < ∞ := iff.rfl

end measure

open measure
open_locale measure_theory

/-- The preimage of a null measurable set under a (quasi) measure preserving map is a null
measurable set. -/
lemma null_measurable_set.preimage {ν : measure β} {f : α → β} {t : set β}
  (ht : null_measurable_set t ν) (hf : quasi_measure_preserving f μ ν) :
  null_measurable_set (f ⁻¹' t) μ :=
⟨f ⁻¹' (to_measurable ν t), hf.measurable (measurable_set_to_measurable _ _),
  hf.ae_eq ht.to_measurable_ae_eq.symm⟩

lemma null_measurable_set.mono_ac (h : null_measurable_set s μ) (hle : ν ≪ μ) :
  null_measurable_set s ν :=
h.preimage $ (quasi_measure_preserving.id μ).mono_left hle

lemma null_measurable_set.mono (h : null_measurable_set s μ) (hle : ν ≤ μ) :
  null_measurable_set s ν :=
h.mono_ac hle.absolutely_continuous

lemma ae_disjoint.preimage {ν : measure β} {f : α → β} {s t : set β}
  (ht : ae_disjoint ν s t) (hf : quasi_measure_preserving f μ ν) :
  ae_disjoint μ (f ⁻¹' s) (f ⁻¹' t) :=
hf.preimage_null ht

@[simp] lemma ae_eq_bot : μ.ae = ⊥ ↔ μ = 0 :=
by rw [← empty_mem_iff_bot, mem_ae_iff, compl_empty, measure_univ_eq_zero]

@[simp] lemma ae_ne_bot : μ.ae.ne_bot ↔ μ ≠ 0 :=
ne_bot_iff.trans (not_congr ae_eq_bot)

@[simp] lemma ae_zero {m0 : measurable_space α} : (0 : measure α).ae = ⊥ := ae_eq_bot.2 rfl

@[mono] lemma ae_mono (h : μ ≤ ν) : μ.ae ≤ ν.ae := h.absolutely_continuous.ae_le

lemma mem_ae_map_iff {f : α → β} (hf : ae_measurable f μ) {s : set β} (hs : measurable_set s) :
  s ∈ (μ.map f).ae ↔ (f ⁻¹' s) ∈ μ.ae :=
by simp only [mem_ae_iff, map_apply_of_ae_measurable hf hs.compl, preimage_compl]

lemma mem_ae_of_mem_ae_map
  {f : α → β} (hf : ae_measurable f μ) {s : set β} (hs : s ∈ (μ.map f).ae) :
  f ⁻¹' s ∈ μ.ae :=
(tendsto_ae_map hf).eventually hs

lemma ae_map_iff
  {f : α → β} (hf : ae_measurable f μ) {p : β → Prop} (hp : measurable_set {x | p x}) :
  (∀ᵐ y ∂ (μ.map f), p y) ↔ ∀ᵐ x ∂ μ, p (f x) :=
mem_ae_map_iff hf hp

lemma ae_of_ae_map {f : α → β} (hf : ae_measurable f μ) {p : β → Prop} (h : ∀ᵐ y ∂ (μ.map f), p y) :
  ∀ᵐ x ∂ μ, p (f x) :=
mem_ae_of_mem_ae_map hf h

lemma ae_map_mem_range {m0 : measurable_space α} (f : α → β) (hf : measurable_set (range f))
  (μ : measure α) :
  ∀ᵐ x ∂(μ.map f), x ∈ range f :=
begin
  by_cases h : ae_measurable f μ,
  { change range f ∈ (μ.map f).ae,
    rw mem_ae_map_iff h hf,
    apply eventually_of_forall,
    exact mem_range_self },
  { simp [map_of_not_ae_measurable h] }
end

@[simp] lemma ae_restrict_Union_eq [encodable ι] (s : ι → set α) :
  (μ.restrict (⋃ i, s i)).ae = ⨆ i, (μ.restrict (s i)).ae :=
le_antisymm (ae_sum_eq (λ i, μ.restrict (s i)) ▸ ae_mono restrict_Union_le) $
  supr_le $ λ i, ae_mono $ restrict_mono (subset_Union s i) le_rfl

@[simp] lemma ae_restrict_union_eq (s t : set α) :
  (μ.restrict (s ∪ t)).ae = (μ.restrict s).ae ⊔ (μ.restrict t).ae :=
by simp [union_eq_Union, supr_bool_eq]

lemma ae_restrict_interval_oc_eq [linear_order α] (a b : α) :
  (μ.restrict (Ι a b)).ae = (μ.restrict (Ioc a b)).ae ⊔ (μ.restrict (Ioc b a)).ae :=
by simp only [interval_oc_eq_union, ae_restrict_union_eq]

/-- See also `measure_theory.ae_interval_oc_iff`. -/
lemma ae_restrict_interval_oc_iff [linear_order α] {a b : α} {P : α → Prop} :
  (∀ᵐ x ∂μ.restrict (Ι a b), P x) ↔
    (∀ᵐ x ∂μ.restrict (Ioc a b), P x) ∧ (∀ᵐ x ∂μ.restrict (Ioc b a), P x) :=
by rw [ae_restrict_interval_oc_eq, eventually_sup]

lemma ae_restrict_iff {p : α → Prop} (hp : measurable_set {x | p x}) :
  (∀ᵐ x ∂(μ.restrict s), p x) ↔ ∀ᵐ x ∂μ, x ∈ s → p x :=
begin
  simp only [ae_iff, ← compl_set_of, restrict_apply hp.compl],
  congr' with x, simp [and_comm]
end

lemma ae_imp_of_ae_restrict {s : set α} {p : α → Prop} (h : ∀ᵐ x ∂(μ.restrict s), p x) :
  ∀ᵐ x ∂μ, x ∈ s → p x :=
begin
  simp only [ae_iff] at h ⊢,
  simpa [set_of_and, inter_comm] using measure_inter_eq_zero_of_restrict h
end

lemma ae_restrict_iff' {p : α → Prop} (hs : measurable_set s) :
  (∀ᵐ x ∂(μ.restrict s), p x) ↔ ∀ᵐ x ∂μ, x ∈ s → p x :=
begin
  simp only [ae_iff, ← compl_set_of, restrict_apply_eq_zero' hs],
  congr' with x, simp [and_comm]
end

lemma _root_.filter.eventually_eq.restrict {f g : α → δ} {s : set α} (hfg : f =ᵐ[μ] g) :
  f =ᵐ[μ.restrict s] g :=
begin -- note that we cannot use `ae_restrict_iff` since we do not require measurability
  refine hfg.filter_mono _,
  rw measure.ae_le_iff_absolutely_continuous,
  exact measure.absolutely_continuous_of_le measure.restrict_le_self,
end

lemma ae_restrict_mem (hs : measurable_set s) :
  ∀ᵐ x ∂(μ.restrict s), x ∈ s :=
(ae_restrict_iff' hs).2 (filter.eventually_of_forall (λ x, id))

lemma ae_restrict_mem₀ (hs : null_measurable_set s μ) : ∀ᵐ x ∂(μ.restrict s), x ∈ s :=
begin
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, hts, htm, ht_eq⟩,
  rw ← restrict_congr_set ht_eq,
  exact (ae_restrict_mem htm).mono hts
end

lemma ae_restrict_of_ae {s : set α} {p : α → Prop} (h : ∀ᵐ x ∂μ, p x) :
  (∀ᵐ x ∂(μ.restrict s), p x) :=
eventually.filter_mono (ae_mono measure.restrict_le_self) h

lemma ae_restrict_of_ae_restrict_of_subset {s t : set α} {p : α → Prop} (hst : s ⊆ t)
  (h : ∀ᵐ x ∂(μ.restrict t), p x) :
  (∀ᵐ x ∂(μ.restrict s), p x) :=
h.filter_mono (ae_mono $ measure.restrict_mono hst (le_refl μ))

lemma ae_of_ae_restrict_of_ae_restrict_compl (t : set α) {p : α → Prop}
  (ht : ∀ᵐ x ∂(μ.restrict t), p x) (htc : ∀ᵐ x ∂(μ.restrict tᶜ), p x) :
  ∀ᵐ x ∂μ, p x :=
nonpos_iff_eq_zero.1 $
calc μ {x | ¬p x} = μ ({x | ¬p x} ∩ t ∪ {x | ¬p x} ∩ tᶜ) :
  by rw [← inter_union_distrib_left, union_compl_self, inter_univ]
... ≤ μ ({x | ¬p x} ∩ t) + μ ({x | ¬p x} ∩ tᶜ) : measure_union_le _ _
... ≤ μ.restrict t {x | ¬p x} + μ.restrict tᶜ {x | ¬p x} :
  add_le_add (le_restrict_apply _ _) (le_restrict_apply _ _)
... = 0 : by rw [ae_iff.1 ht, ae_iff.1 htc, zero_add]

lemma mem_map_restrict_ae_iff {β} {s : set α} {t : set β} {f : α → β} (hs : measurable_set s) :
  t ∈ filter.map f (μ.restrict s).ae ↔ μ ((f ⁻¹' t)ᶜ ∩ s) = 0 :=
by rw [mem_map, mem_ae_iff, measure.restrict_apply' hs]

lemma ae_smul_measure {p : α → Prop} [monoid R] [distrib_mul_action R ℝ≥0∞]
  [is_scalar_tower R ℝ≥0∞ ℝ≥0∞] (h : ∀ᵐ x ∂μ, p x) (c : R) :
  ∀ᵐ x ∂(c • μ), p x :=
ae_iff.2 $ by rw [smul_apply, ae_iff.1 h, smul_zero]

lemma ae_add_measure_iff {p : α → Prop} {ν} : (∀ᵐ x ∂μ + ν, p x) ↔ (∀ᵐ x ∂μ, p x) ∧ ∀ᵐ x ∂ν, p x :=
add_eq_zero_iff

lemma ae_eq_comp' {ν : measure β} {f : α → β} {g g' : β → δ} (hf : ae_measurable f μ)
  (h : g =ᵐ[ν] g') (h2 : μ.map f ≪ ν) : g ∘ f =ᵐ[μ] g' ∘ f :=
(tendsto_ae_map hf).mono_right h2.ae_le h

lemma ae_eq_comp {f : α → β} {g g' : β → δ} (hf : ae_measurable f μ)
  (h : g =ᵐ[μ.map f] g') : g ∘ f =ᵐ[μ] g' ∘ f :=
ae_eq_comp' hf h absolutely_continuous.rfl

lemma sub_ae_eq_zero {β} [add_group β] (f g : α → β) : f - g =ᵐ[μ] 0 ↔ f =ᵐ[μ] g :=
begin
  refine ⟨λ h, h.mono (λ x hx, _), λ h, h.mono (λ x hx, _)⟩,
  { rwa [pi.sub_apply, pi.zero_apply, sub_eq_zero] at hx, },
  { rwa [pi.sub_apply, pi.zero_apply, sub_eq_zero], },
end

lemma le_ae_restrict : μ.ae ⊓ 𝓟 s ≤ (μ.restrict s).ae :=
λ s hs, eventually_inf_principal.2 (ae_imp_of_ae_restrict hs)

@[simp] lemma ae_restrict_eq (hs : measurable_set s) : (μ.restrict s).ae = μ.ae ⊓ 𝓟 s :=
begin
  ext t,
  simp only [mem_inf_principal, mem_ae_iff, restrict_apply_eq_zero' hs, compl_set_of,
    not_imp, and_comm (_ ∈ s)],
  refl
end

@[simp] lemma ae_restrict_eq_bot {s} : (μ.restrict s).ae = ⊥ ↔ μ s = 0 :=
ae_eq_bot.trans restrict_eq_zero

@[simp] lemma ae_restrict_ne_bot {s} : (μ.restrict s).ae.ne_bot ↔ 0 < μ s :=
ne_bot_iff.trans $ (not_congr ae_restrict_eq_bot).trans pos_iff_ne_zero.symm

lemma self_mem_ae_restrict {s} (hs : measurable_set s) : s ∈ (μ.restrict s).ae :=
by simp only [ae_restrict_eq hs, exists_prop, mem_principal, mem_inf_iff];
  exact ⟨_, univ_mem, s, subset.rfl, (univ_inter s).symm⟩

/-- A version of the **Borel-Cantelli lemma**: if `pᵢ` is a sequence of predicates such that
`∑ μ {x | pᵢ x}` is finite, then the measure of `x` such that `pᵢ x` holds frequently as `i → ∞` (or
equivalently, `pᵢ x` holds for infinitely many `i`) is equal to zero. -/
lemma measure_set_of_frequently_eq_zero {p : ℕ → α → Prop} (hp : ∑' i, μ {x | p i x} ≠ ∞) :
  μ {x | ∃ᶠ n in at_top, p n x} = 0 :=
by simpa only [limsup_eq_infi_supr_of_nat, frequently_at_top, set_of_forall, set_of_exists]
  using measure_limsup_eq_zero hp

/-- A version of the **Borel-Cantelli lemma**: if `sᵢ` is a sequence of sets such that
`∑ μ sᵢ` exists, then for almost all `x`, `x` does not belong to almost all `sᵢ`. -/
lemma ae_eventually_not_mem {s : ℕ → set α} (hs : ∑' i, μ (s i) ≠ ∞) :
  ∀ᵐ x ∂ μ, ∀ᶠ n in at_top, x ∉ s n :=
measure_set_of_frequently_eq_zero hs

section intervals

lemma bsupr_measure_Iic [preorder α] {s : set α} (hsc : countable s)
  (hst : ∀ x : α, ∃ y ∈ s, x ≤ y) (hdir : directed_on (≤) s) :
  (⨆ x ∈ s, μ (Iic x)) = μ univ :=
begin
  rw ← measure_bUnion_eq_supr hsc,
  { congr, exact Union₂_eq_univ_iff.2 hst },
  { exact directed_on_iff_directed.2 (hdir.directed_coe.mono_comp _ $ λ x y, Iic_subset_Iic.2) }
end

variables [partial_order α] {a b : α}

lemma Iio_ae_eq_Iic' (ha : μ {a} = 0) : Iio a =ᵐ[μ] Iic a :=
by rw [←Iic_diff_right, diff_ae_eq_self, measure_mono_null (set.inter_subset_right _ _) ha]

lemma Ioi_ae_eq_Ici' (ha : μ {a} = 0) : Ioi a =ᵐ[μ] Ici a := @Iio_ae_eq_Iic' αᵒᵈ ‹_› ‹_› _ _ ha

lemma Ioo_ae_eq_Ioc' (hb : μ {b} = 0) : Ioo a b =ᵐ[μ] Ioc a b :=
(ae_eq_refl _).inter (Iio_ae_eq_Iic' hb)

lemma Ioc_ae_eq_Icc' (ha : μ {a} = 0) : Ioc a b =ᵐ[μ] Icc a b :=
(Ioi_ae_eq_Ici' ha).inter (ae_eq_refl _)

lemma Ioo_ae_eq_Ico' (ha : μ {a} = 0) : Ioo a b =ᵐ[μ] Ico a b :=
(Ioi_ae_eq_Ici' ha).inter (ae_eq_refl _)

lemma Ioo_ae_eq_Icc' (ha : μ {a} = 0) (hb : μ {b} = 0) : Ioo a b =ᵐ[μ] Icc a b :=
(Ioi_ae_eq_Ici' ha).inter (Iio_ae_eq_Iic' hb)

lemma Ico_ae_eq_Icc' (hb : μ {b} = 0) : Ico a b =ᵐ[μ] Icc a b :=
(ae_eq_refl _).inter (Iio_ae_eq_Iic' hb)

lemma Ico_ae_eq_Ioc' (ha : μ {a} = 0) (hb : μ {b} = 0) : Ico a b =ᵐ[μ] Ioc a b :=
(Ioo_ae_eq_Ico' ha).symm.trans (Ioo_ae_eq_Ioc' hb)

end intervals

section dirac
variable [measurable_space α]

lemma mem_ae_dirac_iff {a : α} (hs : measurable_set s) : s ∈ (dirac a).ae ↔ a ∈ s :=
by by_cases a ∈ s; simp [mem_ae_iff, dirac_apply', hs.compl, indicator_apply, *]

lemma ae_dirac_iff {a : α} {p : α → Prop} (hp : measurable_set {x | p x}) :
  (∀ᵐ x ∂(dirac a), p x) ↔ p a :=
mem_ae_dirac_iff hp

@[simp] lemma ae_dirac_eq [measurable_singleton_class α] (a : α) : (dirac a).ae = pure a :=
by { ext s, simp [mem_ae_iff, imp_false] }

lemma ae_eq_dirac' [measurable_singleton_class β] {a : α} {f : α → β} (hf : measurable f) :
  f =ᵐ[dirac a] const α (f a) :=
(ae_dirac_iff $ show measurable_set (f ⁻¹' {f a}), from hf $ measurable_set_singleton _).2 rfl

lemma ae_eq_dirac [measurable_singleton_class α] {a : α} (f : α → δ) :
  f =ᵐ[dirac a] const α (f a) :=
by simp [filter.eventually_eq]

end dirac

section is_finite_measure

include m0

/-- A measure `μ` is called finite if `μ univ < ∞`. -/
class is_finite_measure (μ : measure α) : Prop := (measure_univ_lt_top : μ univ < ∞)

instance restrict.is_finite_measure (μ : measure α) [hs : fact (μ s < ∞)] :
  is_finite_measure (μ.restrict s) :=
⟨by simp [hs.elim]⟩

lemma measure_lt_top (μ : measure α) [is_finite_measure μ] (s : set α) : μ s < ∞ :=
(measure_mono (subset_univ s)).trans_lt is_finite_measure.measure_univ_lt_top

instance is_finite_measure_restrict (μ : measure α) (s : set α) [h : is_finite_measure μ] :
  is_finite_measure (μ.restrict s) :=
⟨by simp [measure_lt_top μ s]⟩

lemma measure_ne_top (μ : measure α) [is_finite_measure μ] (s : set α) : μ s ≠ ∞ :=
ne_of_lt (measure_lt_top μ s)

lemma measure_compl_le_add_of_le_add [is_finite_measure μ] (hs : measurable_set s)
  (ht : measurable_set t) {ε : ℝ≥0∞} (h : μ s ≤ μ t + ε) :
  μ tᶜ ≤ μ sᶜ + ε :=
begin
  rw [measure_compl ht (measure_ne_top μ _), measure_compl hs (measure_ne_top μ _),
    tsub_le_iff_right],
  calc μ univ = μ univ - μ s + μ s :
    (tsub_add_cancel_of_le $ measure_mono s.subset_univ).symm
  ... ≤ μ univ - μ s + (μ t + ε) : add_le_add_left h _
  ... = _ : by rw [add_right_comm, add_assoc]
end

lemma measure_compl_le_add_iff [is_finite_measure μ] (hs : measurable_set s)
  (ht : measurable_set t) {ε : ℝ≥0∞} :
  μ sᶜ ≤ μ tᶜ + ε ↔ μ t ≤ μ s + ε :=
⟨λ h, compl_compl s ▸ compl_compl t ▸ measure_compl_le_add_of_le_add hs.compl ht.compl h,
  measure_compl_le_add_of_le_add ht hs⟩

/-- The measure of the whole space with respect to a finite measure, considered as `ℝ≥0`. -/
def measure_univ_nnreal (μ : measure α) : ℝ≥0 := (μ univ).to_nnreal

@[simp] lemma coe_measure_univ_nnreal (μ : measure α) [is_finite_measure μ] :
  ↑(measure_univ_nnreal μ) = μ univ :=
ennreal.coe_to_nnreal (measure_ne_top μ univ)

instance is_finite_measure_zero : is_finite_measure (0 : measure α) := ⟨by simp⟩

@[priority 100]
instance is_finite_measure_of_is_empty [is_empty α] : is_finite_measure μ :=
by { rw eq_zero_of_is_empty μ, apply_instance }

@[simp] lemma measure_univ_nnreal_zero : measure_univ_nnreal (0 : measure α) = 0 := rfl

omit m0

instance is_finite_measure_add [is_finite_measure μ] [is_finite_measure ν] :
  is_finite_measure (μ + ν) :=
{ measure_univ_lt_top :=
  begin
    rw [measure.coe_add, pi.add_apply, ennreal.add_lt_top],
    exact ⟨measure_lt_top _ _, measure_lt_top _ _⟩,
  end }

instance is_finite_measure_smul_nnreal [is_finite_measure μ] {r : ℝ≥0} :
  is_finite_measure (r • μ) :=
{ measure_univ_lt_top := ennreal.mul_lt_top ennreal.coe_ne_top (measure_ne_top _ _) }

instance is_finite_measure_smul_of_nnreal_tower
  {R} [has_scalar R ℝ≥0] [has_scalar R ℝ≥0∞] [is_scalar_tower R ℝ≥0 ℝ≥0∞]
  [is_scalar_tower R ℝ≥0∞ ℝ≥0∞]
  [is_finite_measure μ] {r : R} :
  is_finite_measure (r • μ) :=
begin
  rw ←smul_one_smul ℝ≥0 r μ,
  apply_instance,
end

lemma is_finite_measure_of_le (μ : measure α) [is_finite_measure μ] (h : ν ≤ μ) :
  is_finite_measure ν :=
{ measure_univ_lt_top := lt_of_le_of_lt (h set.univ measurable_set.univ) (measure_lt_top _ _) }

@[instance] lemma measure.is_finite_measure_map {m : measurable_space α}
  (μ : measure α) [is_finite_measure μ] (f : α → β) :
  is_finite_measure (μ.map f) :=
begin
  by_cases hf : ae_measurable f μ,
  { constructor, rw map_apply_of_ae_measurable hf measurable_set.univ, exact measure_lt_top μ _ },
  { rw map_of_not_ae_measurable hf, exact measure_theory.is_finite_measure_zero }
end

@[simp] lemma measure_univ_nnreal_eq_zero [is_finite_measure μ] :
  measure_univ_nnreal μ = 0 ↔ μ = 0 :=
begin
  rw [← measure_theory.measure.measure_univ_eq_zero, ← coe_measure_univ_nnreal],
  norm_cast
end

lemma measure_univ_nnreal_pos [is_finite_measure μ] (hμ : μ ≠ 0) : 0 < measure_univ_nnreal μ :=
begin
  contrapose! hμ,
  simpa [measure_univ_nnreal_eq_zero, le_zero_iff] using hμ
end

/-- `le_of_add_le_add_left` is normally applicable to `ordered_cancel_add_comm_monoid`,
but it holds for measures with the additional assumption that μ is finite. -/
lemma measure.le_of_add_le_add_left [is_finite_measure μ] (A2 : μ + ν₁ ≤ μ + ν₂) : ν₁ ≤ ν₂ :=
λ S B1, ennreal.le_of_add_le_add_left (measure_theory.measure_ne_top μ S) (A2 S B1)

lemma summable_measure_to_real [hμ : is_finite_measure μ]
  {f : ℕ → set α} (hf₁ : ∀ (i : ℕ), measurable_set (f i)) (hf₂ : pairwise (disjoint on f)) :
  summable (λ x, (μ (f x)).to_real) :=
begin
  apply ennreal.summable_to_real,
  rw ← measure_theory.measure_Union hf₂ hf₁,
  exact ne_of_lt (measure_lt_top _ _)
end

end is_finite_measure

section is_probability_measure

include m0

/-- A measure `μ` is called a probability measure if `μ univ = 1`. -/
class is_probability_measure (μ : measure α) : Prop := (measure_univ : μ univ = 1)

export is_probability_measure (measure_univ)
attribute [simp] is_probability_measure.measure_univ

@[priority 100]
instance is_probability_measure.to_is_finite_measure (μ : measure α) [is_probability_measure μ] :
  is_finite_measure μ :=
⟨by simp only [measure_univ, ennreal.one_lt_top]⟩

lemma is_probability_measure.ne_zero (μ : measure α) [is_probability_measure μ] : μ ≠ 0 :=
mt measure_univ_eq_zero.2 $ by simp [measure_univ]

@[priority 200]
instance is_probability_measure.ae_ne_bot [is_probability_measure μ] : ne_bot μ.ae :=
ae_ne_bot.2 (is_probability_measure.ne_zero μ)

omit m0

instance measure.dirac.is_probability_measure [measurable_space α] {x : α} :
  is_probability_measure (dirac x) :=
⟨dirac_apply_of_mem $ mem_univ x⟩

lemma prob_add_prob_compl [is_probability_measure μ]
  (h : measurable_set s) : μ s + μ sᶜ = 1 :=
(measure_add_measure_compl h).trans measure_univ

lemma prob_le_one [is_probability_measure μ] : μ s ≤ 1 :=
(measure_mono $ set.subset_univ _).trans_eq measure_univ

lemma is_probability_measure_smul [is_finite_measure μ] (h : μ ≠ 0) :
  is_probability_measure ((μ univ)⁻¹ • μ) :=
begin
  constructor,
  rw [smul_apply, smul_eq_mul, ennreal.inv_mul_cancel],
  { rwa [ne, measure_univ_eq_zero] },
  { exact measure_ne_top _ _ }
end

lemma is_probability_measure_map [is_probability_measure μ] {f : α → β} (hf : ae_measurable f μ) :
  is_probability_measure (map f μ) :=
⟨by simp [map_apply_of_ae_measurable, hf]⟩

end is_probability_measure

section no_atoms

/-- Measure `μ` *has no atoms* if the measure of each singleton is zero.

NB: Wikipedia assumes that for any measurable set `s` with positive `μ`-measure,
there exists a measurable `t ⊆ s` such that `0 < μ t < μ s`. While this implies `μ {x} = 0`,
the converse is not true. -/
class has_no_atoms {m0 : measurable_space α} (μ : measure α) : Prop :=
(measure_singleton : ∀ x, μ {x} = 0)

export has_no_atoms (measure_singleton)
attribute [simp] measure_singleton

variables [has_no_atoms μ]

lemma _root_.set.subsingleton.measure_zero {α : Type*} {m : measurable_space α} {s : set α}
  (hs : s.subsingleton) (μ : measure α) [has_no_atoms μ] :
  μ s = 0 :=
hs.induction_on measure_empty measure_singleton

lemma measure.restrict_singleton' {a : α} :
  μ.restrict {a} = 0 :=
by simp only [measure_singleton, measure.restrict_eq_zero]

instance (s : set α) : has_no_atoms (μ.restrict s) :=
begin
  refine ⟨λ x, _⟩,
  obtain ⟨t, hxt, ht1, ht2⟩ := exists_measurable_superset_of_null (measure_singleton x : μ {x} = 0),
  apply measure_mono_null hxt,
  rw measure.restrict_apply ht1,
  apply measure_mono_null (inter_subset_left t s) ht2
end

lemma _root_.set.countable.measure_zero {α : Type*} {m : measurable_space α} {s : set α}
  (h : countable s) (μ : measure α) [has_no_atoms μ] :
  μ s = 0 :=
begin
  rw [← bUnion_of_singleton s, ← nonpos_iff_eq_zero],
  refine le_trans (measure_bUnion_le h _) _,
  simp
end

lemma _root_.set.countable.ae_not_mem {α : Type*} {m : measurable_space α} {s : set α}
  (h : countable s) (μ : measure α) [has_no_atoms μ] :
  ∀ᵐ x ∂μ, x ∉ s :=
by simpa only [ae_iff, not_not] using h.measure_zero μ

lemma _root_.set.finite.measure_zero {α : Type*} {m : measurable_space α} {s : set α}
  (h : s.finite) (μ : measure α) [has_no_atoms μ] : μ s = 0 :=
h.countable.measure_zero μ

lemma _root_.finset.measure_zero {α : Type*} {m : measurable_space α}
  (s : finset α) (μ : measure α) [has_no_atoms μ] : μ s = 0 :=
s.finite_to_set.measure_zero μ

lemma insert_ae_eq_self (a : α) (s : set α) :
  (insert a s : set α) =ᵐ[μ] s :=
union_ae_eq_right.2 $ measure_mono_null (diff_subset _ _) (measure_singleton _)

variables [partial_order α] {a b : α}

lemma Iio_ae_eq_Iic : Iio a =ᵐ[μ] Iic a :=
Iio_ae_eq_Iic' (measure_singleton a)

lemma Ioi_ae_eq_Ici : Ioi a =ᵐ[μ] Ici a :=
Ioi_ae_eq_Ici' (measure_singleton a)

lemma Ioo_ae_eq_Ioc : Ioo a b =ᵐ[μ] Ioc a b :=
Ioo_ae_eq_Ioc' (measure_singleton b)

lemma Ioc_ae_eq_Icc : Ioc a b =ᵐ[μ] Icc a b :=
Ioc_ae_eq_Icc' (measure_singleton a)

lemma Ioo_ae_eq_Ico : Ioo a b =ᵐ[μ] Ico a b :=
Ioo_ae_eq_Ico' (measure_singleton a)

lemma Ioo_ae_eq_Icc : Ioo a b =ᵐ[μ] Icc a b :=
Ioo_ae_eq_Icc' (measure_singleton a) (measure_singleton b)

lemma Ico_ae_eq_Icc : Ico a b =ᵐ[μ] Icc a b :=
Ico_ae_eq_Icc' (measure_singleton b)

lemma Ico_ae_eq_Ioc : Ico a b =ᵐ[μ] Ioc a b :=
Ico_ae_eq_Ioc' (measure_singleton a) (measure_singleton b)

end no_atoms

lemma ite_ae_eq_of_measure_zero {γ} (f : α → γ) (g : α → γ) (s : set α) (hs_zero : μ s = 0) :
  (λ x, ite (x ∈ s) (f x) (g x)) =ᵐ[μ] g :=
begin
  have h_ss : sᶜ ⊆ {a : α | ite (a ∈ s) (f a) (g a) = g a},
    from λ x hx, by simp [(set.mem_compl_iff _ _).mp hx],
  refine measure_mono_null _ hs_zero,
  nth_rewrite 0 ←compl_compl s,
  rwa set.compl_subset_compl,
end

lemma ite_ae_eq_of_measure_compl_zero {γ} (f : α → γ) (g : α → γ) (s : set α) (hs_zero : μ sᶜ = 0) :
  (λ x, ite (x ∈ s) (f x) (g x)) =ᵐ[μ] f :=
by { filter_upwards [hs_zero], intros, split_ifs, refl }

namespace measure

/-- A measure is called finite at filter `f` if it is finite at some set `s ∈ f`.
Equivalently, it is eventually finite at `s` in `f.small_sets`. -/
def finite_at_filter {m0 : measurable_space α} (μ : measure α) (f : filter α) : Prop :=
∃ s ∈ f, μ s < ∞

lemma finite_at_filter_of_finite {m0 : measurable_space α} (μ : measure α) [is_finite_measure μ]
  (f : filter α) :
  μ.finite_at_filter f :=
⟨univ, univ_mem, measure_lt_top μ univ⟩

lemma finite_at_filter.exists_mem_basis {f : filter α} (hμ : finite_at_filter μ f)
  {p : ι → Prop} {s : ι → set α} (hf : f.has_basis p s) :
  ∃ i (hi : p i), μ (s i) < ∞ :=
(hf.exists_iff (λ s t hst ht, (measure_mono hst).trans_lt ht)).1 hμ

lemma finite_at_bot {m0 : measurable_space α} (μ : measure α) : μ.finite_at_filter ⊥ :=
⟨∅, mem_bot, by simp only [measure_empty, with_top.zero_lt_top]⟩

/-- `μ` has finite spanning sets in `C` if there is a countable sequence of sets in `C` that have
  finite measures. This structure is a type, which is useful if we want to record extra properties
  about the sets, such as that they are monotone.
  `sigma_finite` is defined in terms of this: `μ` is σ-finite if there exists a sequence of
  finite spanning sets in the collection of all measurable sets. -/
@[protect_proj, nolint has_inhabited_instance]
structure finite_spanning_sets_in {m0 : measurable_space α} (μ : measure α) (C : set (set α)) :=
(set : ℕ → set α)
(set_mem : ∀ i, set i ∈ C)
(finite : ∀ i, μ (set i) < ∞)
(spanning : (⋃ i, set i) = univ)

end measure
open measure

/-- A measure `μ` is called σ-finite if there is a countable collection of sets
 `{ A i | i ∈ ℕ }` such that `μ (A i) < ∞` and `⋃ i, A i = s`. -/
class sigma_finite {m0 : measurable_space α} (μ : measure α) : Prop :=
(out' : nonempty (μ.finite_spanning_sets_in univ))

theorem sigma_finite_iff :
  sigma_finite μ ↔ nonempty (μ.finite_spanning_sets_in univ) :=
⟨λ h, h.1, λ h, ⟨h⟩⟩

theorem sigma_finite.out (h : sigma_finite μ) :
  nonempty (μ.finite_spanning_sets_in univ) := h.1

include m0

/-- If `μ` is σ-finite it has finite spanning sets in the collection of all measurable sets. -/
def measure.to_finite_spanning_sets_in (μ : measure α) [h : sigma_finite μ] :
  μ.finite_spanning_sets_in {s | measurable_set s} :=
{ set := λ n, to_measurable μ (h.out.some.set n),
  set_mem := λ n, measurable_set_to_measurable _ _,
  finite := λ n, by { rw measure_to_measurable, exact h.out.some.finite n },
  spanning := eq_univ_of_subset (Union_mono $ λ n, subset_to_measurable _ _)
    h.out.some.spanning }

/-- A noncomputable way to get a monotone collection of sets that span `univ` and have finite
  measure using `classical.some`. This definition satisfies monotonicity in addition to all other
  properties in `sigma_finite`. -/
def spanning_sets (μ : measure α) [sigma_finite μ] (i : ℕ) : set α :=
accumulate μ.to_finite_spanning_sets_in.set i

lemma monotone_spanning_sets (μ : measure α) [sigma_finite μ] :
  monotone (spanning_sets μ) :=
monotone_accumulate

lemma measurable_spanning_sets (μ : measure α) [sigma_finite μ] (i : ℕ) :
  measurable_set (spanning_sets μ i) :=
measurable_set.Union $ λ j, measurable_set.Union_Prop $
  λ hij, μ.to_finite_spanning_sets_in.set_mem j

lemma measure_spanning_sets_lt_top (μ : measure α) [sigma_finite μ] (i : ℕ) :
  μ (spanning_sets μ i) < ∞ :=
measure_bUnion_lt_top (finite_le_nat i) $ λ j _, (μ.to_finite_spanning_sets_in.finite j).ne

lemma Union_spanning_sets (μ : measure α) [sigma_finite μ] :
  (⋃ i : ℕ, spanning_sets μ i) = univ :=
by simp_rw [spanning_sets, Union_accumulate, μ.to_finite_spanning_sets_in.spanning]

lemma is_countably_spanning_spanning_sets (μ : measure α) [sigma_finite μ] :
  is_countably_spanning (range (spanning_sets μ)) :=
⟨spanning_sets μ, mem_range_self, Union_spanning_sets μ⟩

/-- `spanning_sets_index μ x` is the least `n : ℕ` such that `x ∈ spanning_sets μ n`. -/
def spanning_sets_index (μ : measure α) [sigma_finite μ] (x : α) : ℕ :=
nat.find $ Union_eq_univ_iff.1 (Union_spanning_sets μ) x

lemma measurable_spanning_sets_index (μ : measure α) [sigma_finite μ] :
  measurable (spanning_sets_index μ) :=
measurable_find _ $ measurable_spanning_sets μ

lemma preimage_spanning_sets_index_singleton (μ : measure α) [sigma_finite μ] (n : ℕ) :
  spanning_sets_index μ ⁻¹' {n} = disjointed (spanning_sets μ) n :=
preimage_find_eq_disjointed _ _ _

lemma spanning_sets_index_eq_iff (μ : measure α) [sigma_finite μ] {x : α} {n : ℕ} :
  spanning_sets_index μ x = n ↔ x ∈ disjointed (spanning_sets μ) n :=
by convert set.ext_iff.1 (preimage_spanning_sets_index_singleton μ n) x

lemma mem_disjointed_spanning_sets_index (μ : measure α) [sigma_finite μ] (x : α) :
  x ∈ disjointed (spanning_sets μ) (spanning_sets_index μ x) :=
(spanning_sets_index_eq_iff μ).1 rfl

lemma mem_spanning_sets_index (μ : measure α) [sigma_finite μ] (x : α) :
  x ∈ spanning_sets μ (spanning_sets_index μ x) :=
disjointed_subset _ _ (mem_disjointed_spanning_sets_index μ x)

lemma mem_spanning_sets_of_index_le (μ : measure α) [sigma_finite μ] (x : α)
  {n : ℕ} (hn : spanning_sets_index μ x ≤ n) :
  x ∈ spanning_sets μ n :=
monotone_spanning_sets μ hn (mem_spanning_sets_index μ x)

lemma eventually_mem_spanning_sets (μ : measure α) [sigma_finite μ] (x : α) :
  ∀ᶠ n in at_top, x ∈ spanning_sets μ n :=
eventually_at_top.2 ⟨spanning_sets_index μ x, λ b, mem_spanning_sets_of_index_le μ x⟩

omit m0

namespace measure

lemma supr_restrict_spanning_sets [sigma_finite μ] (hs : measurable_set s) :
  (⨆ i, μ.restrict (spanning_sets μ i) s) = μ s :=
calc (⨆ i, μ.restrict (spanning_sets μ i) s) = μ.restrict (⋃ i, spanning_sets μ i) s :
  (restrict_Union_apply_eq_supr (directed_of_sup (monotone_spanning_sets μ)) hs).symm
... = μ s : by rw [Union_spanning_sets, restrict_univ]

/-- In a σ-finite space, any measurable set of measure `> r` contains a measurable subset of
finite measure `> r`. -/
lemma exists_subset_measure_lt_top [sigma_finite μ]
  {r : ℝ≥0∞} (hs : measurable_set s) (h's : r < μ s) :
  ∃ t, measurable_set t ∧ t ⊆ s ∧ r < μ t ∧ μ t < ∞ :=
begin
  rw [← supr_restrict_spanning_sets hs,
      @lt_supr_iff _ _ _ r (λ (i : ℕ), μ.restrict (spanning_sets μ i) s)] at h's,
  rcases h's with ⟨n, hn⟩,
  simp only [restrict_apply hs] at hn,
  refine ⟨s ∩ spanning_sets μ n, hs.inter (measurable_spanning_sets _ _), inter_subset_left _ _,
    hn, _⟩,
  exact (measure_mono (inter_subset_right _ _)).trans_lt (measure_spanning_sets_lt_top _ _),
end

/-- The measurable superset `to_measurable μ t` of `t` (which has the same measure as `t`)
satisfies, for any measurable set `s`, the equality `μ (to_measurable μ t ∩ s) = μ (t ∩ s)`.
This only holds when `μ` is σ-finite. For a version without this assumption (but requiring
that `t` has finite measure), see `measure_to_measurable_inter`. -/
lemma measure_to_measurable_inter_of_sigma_finite
  [sigma_finite μ] {s : set α} (hs : measurable_set s) (t : set α) :
  μ (to_measurable μ t ∩ s) = μ (t ∩ s) :=
begin
  -- we show that there is a measurable superset of `t` satisfying the conclusion for any
  -- measurable set `s`. It is built on each member of a spanning family using `to_measurable`
  -- (which is well behaved for finite measure sets thanks to `measure_to_measurable_inter`), and
  -- the desired property passes to the union.
  have A : ∃ t' ⊇ t, measurable_set t' ∧ (∀ u, measurable_set u → μ (t' ∩ u) = μ (t ∩ u)),
  { set t' := ⋃ n, to_measurable μ (t ∩ disjointed (spanning_sets μ) n) with ht',
    have tt' : t ⊆ t' := calc
      t ⊆ ⋃ n, t ∩ disjointed (spanning_sets μ) n :
        by rw [← inter_Union, Union_disjointed, Union_spanning_sets, inter_univ]
      ... ⊆ ⋃ n, to_measurable μ (t ∩ disjointed (spanning_sets μ) n) :
        Union_mono (λ n, subset_to_measurable _ _),
    refine ⟨t', tt', measurable_set.Union (λ n, measurable_set_to_measurable μ _), λ u hu, _⟩,
    apply le_antisymm _ (measure_mono (inter_subset_inter tt' subset.rfl)),
    calc μ (t' ∩ u) ≤ ∑' n, μ (to_measurable μ (t ∩ disjointed (spanning_sets μ) n) ∩ u) :
      by { rw [ht', Union_inter], exact measure_Union_le _ }
    ... = ∑' n, μ ((t ∩ disjointed (spanning_sets μ) n) ∩ u) :
      begin
        congr' 1,
        ext1 n,
        apply measure_to_measurable_inter hu,
        apply ne_of_lt,
        calc μ (t ∩ disjointed (spanning_sets μ) n)
            ≤ μ (disjointed (spanning_sets μ) n) : measure_mono (inter_subset_right _ _)
        ... ≤ μ (spanning_sets μ n) : measure_mono (disjointed_le (spanning_sets μ) n)
        ... < ∞ : measure_spanning_sets_lt_top _ _
      end
    ... = ∑' n, μ.restrict (t ∩ u) (disjointed (spanning_sets μ) n) :
      begin
        congr' 1,
        ext1 n,
        rw [restrict_apply, inter_comm t _, inter_assoc],
        exact measurable_set.disjointed (measurable_spanning_sets _) _
      end
    ... = μ.restrict (t ∩ u) (⋃ n, disjointed (spanning_sets μ) n) :
      begin
        rw measure_Union,
        { exact disjoint_disjointed _ },
        { intro i, exact measurable_set.disjointed (measurable_spanning_sets _) _ }
      end
    ... = μ (t ∩ u) :
      by rw [Union_disjointed, Union_spanning_sets, restrict_apply measurable_set.univ,
             univ_inter] },
  -- thanks to the definition of `to_measurable`, the previous property will also be shared
  -- by `to_measurable μ t`, which is enough to conclude the proof.
  rw [to_measurable],
  split_ifs with ht,
  { apply measure_congr,
    exact ae_eq_set_inter ht.some_spec.snd.2 (ae_eq_refl _) },
  { exact A.some_spec.snd.2 s hs },
end

@[simp] lemma restrict_to_measurable_of_sigma_finite [sigma_finite μ] (s : set α) :
  μ.restrict (to_measurable μ s) = μ.restrict s :=
ext $ λ t ht, by simp only [restrict_apply ht, inter_comm t,
  measure_to_measurable_inter_of_sigma_finite ht]

namespace finite_spanning_sets_in

variables {C D : set (set α)}

/-- If `μ` has finite spanning sets in `C` and `C ∩ {s | μ s < ∞} ⊆ D` then `μ` has finite spanning
sets in `D`. -/
protected def mono' (h : μ.finite_spanning_sets_in C) (hC : C ∩ {s | μ s < ∞} ⊆ D) :
  μ.finite_spanning_sets_in D :=
⟨h.set, λ i, hC ⟨h.set_mem i, h.finite i⟩, h.finite, h.spanning⟩

/-- If `μ` has finite spanning sets in `C` and `C ⊆ D` then `μ` has finite spanning sets in `D`. -/
protected def mono (h : μ.finite_spanning_sets_in C) (hC : C ⊆ D) : μ.finite_spanning_sets_in D :=
h.mono' (λ s hs, hC hs.1)

/-- If `μ` has finite spanning sets in the collection of measurable sets `C`, then `μ` is σ-finite.
-/
protected lemma sigma_finite (h : μ.finite_spanning_sets_in C) :
  sigma_finite μ :=
⟨⟨h.mono $ subset_univ C⟩⟩

/-- An extensionality for measures. It is `ext_of_generate_from_of_Union` formulated in terms of
`finite_spanning_sets_in`. -/
protected lemma ext {ν : measure α} {C : set (set α)} (hA : ‹_› = generate_from C)
  (hC : is_pi_system C) (h : μ.finite_spanning_sets_in C) (h_eq : ∀ s ∈ C, μ s = ν s) : μ = ν :=
ext_of_generate_from_of_Union C _ hA hC h.spanning h.set_mem (λ i, (h.finite i).ne) h_eq

protected lemma is_countably_spanning (h : μ.finite_spanning_sets_in C) : is_countably_spanning C :=
⟨h.set, h.set_mem, h.spanning⟩

end finite_spanning_sets_in

lemma sigma_finite_of_countable {S : set (set α)} (hc : countable S)
  (hμ : ∀ s ∈ S, μ s < ∞) (hU : ⋃₀ S = univ) :
  sigma_finite μ :=
begin
  obtain ⟨s, hμ, hs⟩ : ∃ s : ℕ → set α, (∀ n, μ (s n) < ∞) ∧ (⋃ n, s n) = univ,
    from (@exists_seq_cover_iff_countable _ (λ x, μ x < ⊤) ⟨∅, by simp⟩).2 ⟨S, hc, hμ, hU⟩,
  exact ⟨⟨⟨λ n, s n, λ n, trivial, hμ, hs⟩⟩⟩,
end

/-- Given measures `μ`, `ν` where `ν ≤ μ`, `finite_spanning_sets_in.of_le` provides the induced
`finite_spanning_set` with respect to `ν` from a `finite_spanning_set` with respect to `μ`. -/
def finite_spanning_sets_in.of_le (h : ν ≤ μ) {C : set (set α)}
  (S : μ.finite_spanning_sets_in C) : ν.finite_spanning_sets_in C :=
{ set := S.set,
  set_mem := S.set_mem,
  finite := λ n, lt_of_le_of_lt (le_iff'.1 h _) (S.finite n),
  spanning := S.spanning }

lemma sigma_finite_of_le (μ : measure α) [hs : sigma_finite μ]
  (h : ν ≤ μ) : sigma_finite ν :=
⟨hs.out.map $ finite_spanning_sets_in.of_le h⟩

end measure

include m0

/-- Every finite measure is σ-finite. -/
@[priority 100]
instance is_finite_measure.to_sigma_finite (μ : measure α) [is_finite_measure μ] :
  sigma_finite μ :=
⟨⟨⟨λ _, univ, λ _, trivial, λ _, measure_lt_top μ _, Union_const _⟩⟩⟩

instance restrict.sigma_finite (μ : measure α) [sigma_finite μ] (s : set α) :
  sigma_finite (μ.restrict s) :=
begin
  refine ⟨⟨⟨spanning_sets μ, λ _, trivial, λ i, _, Union_spanning_sets μ⟩⟩⟩,
  rw [restrict_apply (measurable_spanning_sets μ i)],
  exact (measure_mono $ inter_subset_left _ _).trans_lt (measure_spanning_sets_lt_top μ i)
end

instance sum.sigma_finite {ι} [fintype ι] (μ : ι → measure α) [∀ i, sigma_finite (μ i)] :
  sigma_finite (sum μ) :=
begin
  haveI : encodable ι := fintype.to_encodable ι,
  have : ∀ n, measurable_set (⋂ (i : ι), spanning_sets (μ i) n) :=
    λ n, measurable_set.Inter (λ i, measurable_spanning_sets (μ i) n),
  refine ⟨⟨⟨λ n, ⋂ i, spanning_sets (μ i) n, λ _, trivial, λ n, _, _⟩⟩⟩,
  { rw [sum_apply _ (this n), tsum_fintype, ennreal.sum_lt_top_iff],
    rintro i -,
    exact (measure_mono $ Inter_subset _ i).trans_lt (measure_spanning_sets_lt_top (μ i) n) },
  { rw [Union_Inter_of_monotone], simp_rw [Union_spanning_sets, Inter_univ],
    exact λ i, monotone_spanning_sets (μ i), }
end

instance add.sigma_finite (μ ν : measure α) [sigma_finite μ] [sigma_finite ν] :
  sigma_finite (μ + ν) :=
by { rw [← sum_cond], refine @sum.sigma_finite _ _ _ _ _ (bool.rec _ _); simpa }

lemma sigma_finite.of_map (μ : measure α) {f : α → β} (hf : ae_measurable f μ)
  (h : sigma_finite (μ.map f)) :
  sigma_finite μ :=
⟨⟨⟨λ n, f ⁻¹' (spanning_sets (μ.map f) n),
   λ n, trivial,
   λ n, by simp only [← map_apply_of_ae_measurable hf, measurable_spanning_sets,
     measure_spanning_sets_lt_top],
   by rw [← preimage_Union, Union_spanning_sets, preimage_univ]⟩⟩⟩

lemma _root_.measurable_equiv.sigma_finite_map {μ : measure α} (f : α ≃ᵐ β) (h : sigma_finite μ) :
  sigma_finite (μ.map f) :=
by { refine sigma_finite.of_map _ f.symm.measurable.ae_measurable _,
     rwa [map_map f.symm.measurable f.measurable, f.symm_comp_self, measure.map_id] }

/-- Similar to `ae_of_forall_measure_lt_top_ae_restrict`, but where you additionally get the
  hypothesis that another σ-finite measure has finite values on `s`. -/
lemma ae_of_forall_measure_lt_top_ae_restrict' {μ : measure α} (ν : measure α) [sigma_finite μ]
  [sigma_finite ν] (P : α → Prop)
  (h : ∀ s, measurable_set s → μ s < ∞ → ν s < ∞ → ∀ᵐ x ∂(μ.restrict s), P x) :
  ∀ᵐ x ∂μ, P x :=
begin
  have : ∀ n, ∀ᵐ x ∂μ, x ∈ spanning_sets (μ + ν) n → P x,
  { intro n,
    have := h (spanning_sets (μ + ν) n) (measurable_spanning_sets _ _) _ _,
    exacts [(ae_restrict_iff' (measurable_spanning_sets _ _)).mp this,
      (self_le_add_right _ _).trans_lt (measure_spanning_sets_lt_top (μ + ν) _),
      (self_le_add_left _ _).trans_lt (measure_spanning_sets_lt_top (μ + ν) _)] },
  filter_upwards [ae_all_iff.2 this] with _ hx using hx _ (mem_spanning_sets_index _ _)
end

/-- To prove something for almost all `x` w.r.t. a σ-finite measure, it is sufficient to show that
  this holds almost everywhere in sets where the measure has finite value. -/
lemma ae_of_forall_measure_lt_top_ae_restrict {μ : measure α} [sigma_finite μ] (P : α → Prop)
  (h : ∀ s, measurable_set s → μ s < ∞ → ∀ᵐ x ∂(μ.restrict s), P x) :
  ∀ᵐ x ∂μ, P x :=
ae_of_forall_measure_lt_top_ae_restrict' μ P $ λ s hs h2s _, h s hs h2s

/-- A measure is called locally finite if it is finite in some neighborhood of each point. -/
class is_locally_finite_measure [topological_space α] (μ : measure α) : Prop :=
(finite_at_nhds : ∀ x, μ.finite_at_filter (𝓝 x))

@[priority 100] -- see Note [lower instance priority]
instance is_finite_measure.to_is_locally_finite_measure [topological_space α] (μ : measure α)
  [is_finite_measure μ] :
  is_locally_finite_measure μ :=
⟨λ x, finite_at_filter_of_finite _ _⟩

lemma measure.finite_at_nhds [topological_space α] (μ : measure α)
  [is_locally_finite_measure μ] (x : α) :
  μ.finite_at_filter (𝓝 x) :=
is_locally_finite_measure.finite_at_nhds x

lemma measure.smul_finite (μ : measure α) [is_finite_measure μ] {c : ℝ≥0∞} (hc : c ≠ ∞) :
  is_finite_measure (c • μ) :=
begin
  lift c to ℝ≥0 using hc,
  exact measure_theory.is_finite_measure_smul_nnreal,
end

lemma measure.exists_is_open_measure_lt_top [topological_space α] (μ : measure α)
  [is_locally_finite_measure μ] (x : α) :
  ∃ s : set α, x ∈ s ∧ is_open s ∧ μ s < ∞ :=
by simpa only [exists_prop, and.assoc]
  using (μ.finite_at_nhds x).exists_mem_basis (nhds_basis_opens x)

instance is_locally_finite_measure_smul_nnreal [topological_space α] (μ : measure α)
  [is_locally_finite_measure μ] (c : ℝ≥0) : is_locally_finite_measure (c • μ) :=
begin
  refine ⟨λ x, _⟩,
  rcases μ.exists_is_open_measure_lt_top x with ⟨o, xo, o_open, μo⟩,
  refine ⟨o, o_open.mem_nhds xo, _⟩,
  apply ennreal.mul_lt_top _ μo.ne,
  simp only [ring_hom.to_monoid_hom_eq_coe, ring_hom.coe_monoid_hom, ennreal.coe_ne_top,
    ennreal.coe_of_nnreal_hom, ne.def, not_false_iff],
end

/-- A measure `μ` is finite on compacts if any compact set `K` satisfies `μ K < ∞`. -/
@[protect_proj] class is_finite_measure_on_compacts [topological_space α] (μ : measure α) : Prop :=
(lt_top_of_is_compact : ∀ ⦃K : set α⦄, is_compact K → μ K < ∞)

/-- A compact subset has finite measure for a measure which is finite on compacts. -/
lemma _root_.is_compact.measure_lt_top
  [topological_space α] {μ : measure α} [is_finite_measure_on_compacts μ]
  ⦃K : set α⦄ (hK : is_compact K) : μ K < ∞ :=
is_finite_measure_on_compacts.lt_top_of_is_compact hK

/-- A bounded subset has finite measure for a measure which is finite on compact sets, in a
proper space. -/
lemma _root_.metric.bounded.measure_lt_top [pseudo_metric_space α] [proper_space α]
  {μ : measure α} [is_finite_measure_on_compacts μ] ⦃s : set α⦄ (hs : metric.bounded s) :
  μ s < ∞ :=
calc μ s ≤ μ (closure s) : measure_mono subset_closure
... < ∞ : (metric.is_compact_of_is_closed_bounded is_closed_closure hs.closure).measure_lt_top

lemma measure_closed_ball_lt_top [pseudo_metric_space α] [proper_space α]
  {μ : measure α} [is_finite_measure_on_compacts μ] {x : α} {r : ℝ} :
  μ (metric.closed_ball x r) < ∞ :=
metric.bounded_closed_ball.measure_lt_top

lemma measure_ball_lt_top [pseudo_metric_space α] [proper_space α]
  {μ : measure α} [is_finite_measure_on_compacts μ] {x : α} {r : ℝ} :
  μ (metric.ball x r) < ∞ :=
metric.bounded_ball.measure_lt_top

protected lemma is_finite_measure_on_compacts.smul [topological_space α] (μ : measure α)
  [is_finite_measure_on_compacts μ] {c : ℝ≥0∞} (hc : c ≠ ∞) :
  is_finite_measure_on_compacts (c • μ) :=
⟨λ K hK, ennreal.mul_lt_top hc (hK.measure_lt_top).ne⟩

omit m0

@[priority 100] -- see Note [lower instance priority]
instance sigma_finite_of_locally_finite [topological_space α]
  [second_countable_topology α] [is_locally_finite_measure μ] :
  sigma_finite μ :=
begin
  choose s hsx hsμ using μ.finite_at_nhds,
  rcases topological_space.countable_cover_nhds hsx with ⟨t, htc, htU⟩,
  refine measure.sigma_finite_of_countable (htc.image s) (ball_image_iff.2 $ λ x hx, hsμ x) _,
  rwa sUnion_image
end

/-- A measure which is finite on compact sets in a locally compact space is locally finite.
Not registered as an instance to avoid a loop with the other direction. -/
lemma is_locally_finite_measure_of_is_finite_measure_on_compacts [topological_space α]
  [locally_compact_space α] [is_finite_measure_on_compacts μ] :
  is_locally_finite_measure μ :=
⟨begin
  intro x,
  rcases exists_compact_mem_nhds x with ⟨K, K_compact, K_mem⟩,
  exact ⟨K, K_mem, K_compact.measure_lt_top⟩,
end⟩

/-- If a set has zero measure in a neighborhood of each of its points, then it has zero measure
in a second-countable space. -/
lemma null_of_locally_null [topological_space α] [second_countable_topology α]
  (s : set α) (hs : ∀ x ∈ s, ∃ u ∈ 𝓝[s] x, μ u = 0) :
  μ s = 0 :=
μ.to_outer_measure.null_of_locally_null s hs

lemma exists_mem_forall_mem_nhds_within_pos_measure [topological_space α]
  [second_countable_topology α] {s : set α} (hs : μ s ≠ 0) :
  ∃ x ∈ s, ∀ t ∈ 𝓝[s] x, 0 < μ t :=
μ.to_outer_measure.exists_mem_forall_mem_nhds_within_pos hs

lemma exists_ne_forall_mem_nhds_pos_measure_preimage {β} [topological_space β] [t1_space β]
  [second_countable_topology β] [nonempty β] {f : α → β} (h : ∀ b, ∃ᵐ x ∂μ, f x ≠ b) :
  ∃ a b : β, a ≠ b ∧ (∀ s ∈ 𝓝 a, 0 < μ (f ⁻¹' s)) ∧ (∀ t ∈ 𝓝 b, 0 < μ (f ⁻¹' t)) :=
begin
  -- We use an `outer_measure` so that the proof works without `measurable f`
  set m : outer_measure β := outer_measure.map f μ.to_outer_measure,
  replace h : ∀ b : β, m {b}ᶜ ≠ 0 := λ b, not_eventually.mpr (h b),
  inhabit β,
  have : m univ ≠ 0, from ne_bot_of_le_ne_bot (h default) (m.mono' $ subset_univ _),
  rcases m.exists_mem_forall_mem_nhds_within_pos this with ⟨b, -, hb⟩,
  simp only [nhds_within_univ] at hb,
  rcases m.exists_mem_forall_mem_nhds_within_pos (h b) with ⟨a, hab : a ≠ b, ha⟩,
  simp only [is_open_compl_singleton.nhds_within_eq hab] at ha,
  exact ⟨a, b, hab, ha, hb⟩
end

/-- If two finite measures give the same mass to the whole space and coincide on a π-system made
of measurable sets, then they coincide on all sets in the σ-algebra generated by the π-system. -/
lemma ext_on_measurable_space_of_generate_finite {α} (m₀ : measurable_space α)
  {μ ν : measure α} [is_finite_measure μ]
  (C : set (set α)) (hμν : ∀ s ∈ C, μ s = ν s) {m : measurable_space α}
  (h : m ≤ m₀) (hA : m = measurable_space.generate_from C) (hC : is_pi_system C)
  (h_univ : μ set.univ = ν set.univ) {s : set α} (hs : m.measurable_set' s) :
  μ s = ν s :=
begin
  haveI : is_finite_measure ν := begin
     constructor,
     rw ← h_univ,
     apply is_finite_measure.measure_univ_lt_top,
  end,
  refine induction_on_inter hA hC (by simp) hμν _ _ hs,
  { intros t h1t h2t,
    have h1t_ : @measurable_set α m₀ t, from h _ h1t,
    rw [@measure_compl α m₀ μ t h1t_ (@measure_ne_top α m₀ μ _ t),
      @measure_compl α m₀ ν t h1t_ (@measure_ne_top α m₀ ν _ t), h_univ, h2t], },
  { intros f h1f h2f h3f,
    have h2f_ : ∀ (i : ℕ), @measurable_set α m₀ (f i), from (λ i, h _ (h2f i)),
    have h_Union : @measurable_set α m₀ (⋃ (i : ℕ), f i),from @measurable_set.Union α ℕ m₀ _ f h2f_,
    simp [measure_Union, h_Union, h1f, h3f, h2f_], },
end

/-- Two finite measures are equal if they are equal on the π-system generating the σ-algebra
  (and `univ`). -/
lemma ext_of_generate_finite (C : set (set α)) (hA : m0 = generate_from C) (hC : is_pi_system C)
  [is_finite_measure μ] (hμν : ∀ s ∈ C, μ s = ν s) (h_univ : μ univ = ν univ) :
  μ = ν :=
measure.ext (λ s hs, ext_on_measurable_space_of_generate_finite m0 C hμν le_rfl hA hC h_univ hs)

namespace measure

section disjointed

include m0

/-- Given `S : μ.finite_spanning_sets_in {s | measurable_set s}`,
`finite_spanning_sets_in.disjointed` provides a `finite_spanning_sets_in {s | measurable_set s}`
such that its underlying sets are pairwise disjoint. -/
protected def finite_spanning_sets_in.disjointed {μ : measure α}
  (S : μ.finite_spanning_sets_in {s | measurable_set s}) :
   μ.finite_spanning_sets_in {s | measurable_set s} :=
⟨disjointed S.set, measurable_set.disjointed S.set_mem,
  λ n, lt_of_le_of_lt (measure_mono (disjointed_subset S.set n)) (S.finite _),
  S.spanning ▸ Union_disjointed⟩

lemma finite_spanning_sets_in.disjointed_set_eq {μ : measure α}
  (S : μ.finite_spanning_sets_in {s | measurable_set s}) :
  S.disjointed.set = disjointed S.set :=
rfl

lemma exists_eq_disjoint_finite_spanning_sets_in
  (μ ν : measure α) [sigma_finite μ] [sigma_finite ν] :
  ∃ (S : μ.finite_spanning_sets_in {s | measurable_set s})
    (T : ν.finite_spanning_sets_in {s | measurable_set s}),
    S.set = T.set ∧ pairwise (disjoint on S.set) :=
let S := (μ + ν).to_finite_spanning_sets_in.disjointed in
⟨S.of_le (measure.le_add_right le_rfl), S.of_le (measure.le_add_left le_rfl),
  rfl, disjoint_disjointed _⟩

end disjointed

namespace finite_at_filter

variables {f g : filter α}

lemma filter_mono (h : f ≤ g) : μ.finite_at_filter g → μ.finite_at_filter f :=
λ ⟨s, hs, hμ⟩, ⟨s, h hs, hμ⟩

lemma inf_of_left (h : μ.finite_at_filter f) : μ.finite_at_filter (f ⊓ g) :=
h.filter_mono inf_le_left

lemma inf_of_right (h : μ.finite_at_filter g) : μ.finite_at_filter (f ⊓ g) :=
h.filter_mono inf_le_right

@[simp] lemma inf_ae_iff : μ.finite_at_filter (f ⊓ μ.ae) ↔ μ.finite_at_filter f :=
begin
  refine ⟨_, λ h, h.filter_mono inf_le_left⟩,
  rintros ⟨s, ⟨t, ht, u, hu, rfl⟩, hμ⟩,
  suffices : μ t ≤ μ (t ∩ u), from ⟨t, ht, this.trans_lt hμ⟩,
  exact measure_mono_ae (mem_of_superset hu (λ x hu ht, ⟨ht, hu⟩))
end

alias inf_ae_iff ↔ measure_theory.measure.finite_at_filter.of_inf_ae _

lemma filter_mono_ae (h : f ⊓ μ.ae ≤ g) (hg : μ.finite_at_filter g) : μ.finite_at_filter f :=
inf_ae_iff.1 (hg.filter_mono h)

protected lemma measure_mono (h : μ ≤ ν) : ν.finite_at_filter f → μ.finite_at_filter f :=
λ ⟨s, hs, hν⟩, ⟨s, hs, (measure.le_iff'.1 h s).trans_lt hν⟩

@[mono] protected lemma mono (hf : f ≤ g) (hμ : μ ≤ ν) :
  ν.finite_at_filter g → μ.finite_at_filter f :=
λ h, (h.filter_mono hf).measure_mono hμ

protected lemma eventually (h : μ.finite_at_filter f) : ∀ᶠ s in f.small_sets, μ s < ∞ :=
(eventually_small_sets' $ λ s t hst ht, (measure_mono hst).trans_lt ht).2 h

lemma filter_sup : μ.finite_at_filter f → μ.finite_at_filter g → μ.finite_at_filter (f ⊔ g) :=
λ ⟨s, hsf, hsμ⟩ ⟨t, htg, htμ⟩,
 ⟨s ∪ t, union_mem_sup hsf htg, (measure_union_le s t).trans_lt (ennreal.add_lt_top.2 ⟨hsμ, htμ⟩)⟩

end finite_at_filter

lemma finite_at_nhds_within [topological_space α] {m0 : measurable_space α} (μ : measure α)
  [is_locally_finite_measure μ] (x : α) (s : set α) :
  μ.finite_at_filter (𝓝[s] x) :=
(finite_at_nhds μ x).inf_of_left

@[simp] lemma finite_at_principal : μ.finite_at_filter (𝓟 s) ↔ μ s < ∞ :=
⟨λ ⟨t, ht, hμ⟩, (measure_mono ht).trans_lt hμ, λ h, ⟨s, mem_principal_self s, h⟩⟩

lemma is_locally_finite_measure_of_le [topological_space α] {m : measurable_space α}
  {μ ν : measure α} [H : is_locally_finite_measure μ] (h : ν ≤ μ) :
  is_locally_finite_measure ν :=
let F := H.finite_at_nhds in ⟨λ x, (F x).measure_mono h⟩

end measure

end measure_theory

open measure_theory measure_theory.measure

namespace measurable_embedding

variables {m0 : measurable_space α} {m1 : measurable_space β} {f : α → β}
  (hf : measurable_embedding f)
include hf

theorem map_apply (μ : measure α) (s : set β) : μ.map f s = μ (f ⁻¹' s) :=
begin
  refine le_antisymm _ (le_map_apply hf.measurable.ae_measurable s),
  set t := f '' (to_measurable μ (f ⁻¹' s)) ∪ (range f)ᶜ,
  have htm : measurable_set t,
    from (hf.measurable_set_image.2 $ measurable_set_to_measurable _ _).union
      hf.measurable_set_range.compl,
  have hst : s ⊆ t,
  { rw [subset_union_compl_iff_inter_subset, ← image_preimage_eq_inter_range],
    exact image_subset _ (subset_to_measurable _ _) },
  have hft : f ⁻¹' t = to_measurable μ (f ⁻¹' s),
    by rw [preimage_union, preimage_compl, preimage_range, compl_univ, union_empty,
      hf.injective.preimage_image],
  calc μ.map f s ≤ μ.map f t : measure_mono hst
            ... = μ (f ⁻¹' s) :
    by rw [map_apply hf.measurable htm, hft, measure_to_measurable]
end

lemma map_comap (μ : measure β) : (comap f μ).map f  = μ.restrict (range f) :=
begin
  ext1 t ht,
  rw [hf.map_apply, comap_apply f hf.injective hf.measurable_set_image' _ (hf.measurable ht),
    image_preimage_eq_inter_range, restrict_apply ht]
end

lemma comap_apply (μ : measure β) (s : set α) : comap f μ s = μ (f '' s) :=
calc comap f μ s = comap f μ (f ⁻¹' (f '' s)) : by rw hf.injective.preimage_image
... = (comap f μ).map f (f '' s) : (hf.map_apply _ _).symm
... = μ (f '' s) : by rw [hf.map_comap, restrict_apply' hf.measurable_set_range,
  inter_eq_self_of_subset_left (image_subset_range _ _)]

lemma ae_map_iff {p : β → Prop} {μ : measure α} : (∀ᵐ x ∂(μ.map f), p x) ↔ ∀ᵐ x ∂μ, p (f x) :=
by simp only [ae_iff, hf.map_apply, preimage_set_of_eq]

lemma restrict_map (μ : measure α) (s : set β) :
  (μ.map f).restrict s = (μ.restrict $ f ⁻¹' s).map f :=
measure.ext $ λ t ht, by simp [hf.map_apply, ht, hf.measurable ht]

end measurable_embedding

section subtype

lemma comap_subtype_coe_apply {m0 : measurable_space α} {s : set α} (hs : measurable_set s)
  (μ : measure α) (t : set s) :
  comap coe μ t = μ (coe '' t) :=
(measurable_embedding.subtype_coe hs).comap_apply _ _

lemma map_comap_subtype_coe {m0 : measurable_space α} {s : set α} (hs : measurable_set s)
  (μ : measure α) : (comap coe μ).map (coe : s → α) = μ.restrict s :=
by rw [(measurable_embedding.subtype_coe hs).map_comap, subtype.range_coe]

lemma ae_restrict_iff_subtype {m0 : measurable_space α} {μ : measure α} {s : set α}
  (hs : measurable_set s) {p : α → Prop} :
  (∀ᵐ x ∂(μ.restrict s), p x) ↔ ∀ᵐ x ∂(comap (coe : s → α) μ), p ↑x :=
by rw [← map_comap_subtype_coe hs, (measurable_embedding.subtype_coe hs).ae_map_iff]

variables [measure_space α]

/-!
### Volume on `s : set α`
-/

instance _root_.set_coe.measure_space (s : set α) : measure_space s :=
⟨comap (coe : s → α) volume⟩

lemma volume_set_coe_def (s : set α) : (volume : measure s) = comap (coe : s → α) volume := rfl

lemma measurable_set.map_coe_volume {s : set α} (hs : measurable_set s) :
  volume.map (coe : s → α)= restrict volume s :=
by rw [volume_set_coe_def, (measurable_embedding.subtype_coe hs).map_comap volume,
  subtype.range_coe]

lemma volume_image_subtype_coe {s : set α} (hs : measurable_set s) (t : set s) :
  volume (coe '' t : set α) = volume t :=
(comap_subtype_coe_apply hs volume t).symm

end subtype

namespace measurable_equiv

/-! Interactions of measurable equivalences and measures -/

open equiv measure_theory.measure

variables [measurable_space α] [measurable_space β] {μ : measure α} {ν : measure β}

/-- If we map a measure along a measurable equivalence, we can compute the measure on all sets
  (not just the measurable ones). -/
protected theorem map_apply (f : α ≃ᵐ β) (s : set β) : μ.map f s = μ (f ⁻¹' s) :=
f.measurable_embedding.map_apply _ _

@[simp] lemma map_symm_map (e : α ≃ᵐ β) : (μ.map e).map e.symm  = μ :=
by simp [map_map e.symm.measurable e.measurable]

@[simp] lemma map_map_symm (e : α ≃ᵐ β) : (ν.map e.symm).map e  = ν :=
by simp [map_map e.measurable e.symm.measurable]

lemma map_measurable_equiv_injective (e : α ≃ᵐ β) : injective (map e) :=
by { intros μ₁ μ₂ hμ, apply_fun map e.symm at hμ, simpa [map_symm_map e] using hμ }

lemma map_apply_eq_iff_map_symm_apply_eq (e : α ≃ᵐ β) : μ.map e = ν ↔ ν.map e.symm = μ :=
by rw [← (map_measurable_equiv_injective e).eq_iff, map_map_symm, eq_comm]

lemma restrict_map (e : α ≃ᵐ β) (s : set β) : (μ.map e).restrict s = (μ.restrict $ e ⁻¹' s).map e :=
e.measurable_embedding.restrict_map _ _

lemma map_ae (f : α ≃ᵐ β) (μ : measure α) : filter.map f μ.ae = (map f μ).ae :=
by { ext s, simp_rw [mem_map, mem_ae_iff, ← preimage_compl, f.map_apply] }

end measurable_equiv


namespace measure_theory

lemma outer_measure.to_measure_zero [measurable_space α] : (0 : outer_measure α).to_measure
  ((le_top).trans outer_measure.zero_caratheodory.symm.le) = 0 :=
by rw [← measure.measure_univ_eq_zero, to_measure_apply _ _ measurable_set.univ,
  outer_measure.coe_zero, pi.zero_apply]

section trim

/-- Restriction of a measure to a sub-sigma algebra.
It is common to see a measure `μ` on a measurable space structure `m0` as being also a measure on
any `m ≤ m0`. Since measures in mathlib have to be trimmed to the measurable space, `μ` itself
cannot be a measure on `m`, hence the definition of `μ.trim hm`.

This notion is related to `outer_measure.trim`, see the lemma
`to_outer_measure_trim_eq_trim_to_outer_measure`. -/
def measure.trim {m m0 : measurable_space α} (μ : @measure α m0) (hm : m ≤ m0) : @measure α m :=
@outer_measure.to_measure α m μ.to_outer_measure (hm.trans (le_to_outer_measure_caratheodory μ))

@[simp] lemma trim_eq_self [measurable_space α] {μ : measure α} : μ.trim le_rfl = μ :=
by simp [measure.trim]

variables {m m0 : measurable_space α} {μ : measure α} {s : set α}

lemma to_outer_measure_trim_eq_trim_to_outer_measure (μ : measure α) (hm : m ≤ m0) :
  @measure.to_outer_measure _ m (μ.trim hm) = @outer_measure.trim _ m μ.to_outer_measure :=
by rw [measure.trim, to_measure_to_outer_measure]

@[simp] lemma zero_trim (hm : m ≤ m0) : (0 : measure α).trim hm = (0 : @measure α m) :=
by simp [measure.trim, outer_measure.to_measure_zero]

lemma trim_measurable_set_eq (hm : m ≤ m0) (hs : @measurable_set α m s) : μ.trim hm s = μ s :=
by simp [measure.trim, hs]

lemma le_trim (hm : m ≤ m0) : μ s ≤ μ.trim hm s :=
by { simp_rw [measure.trim], exact (@le_to_measure_apply _ m _ _ _), }

lemma measure_eq_zero_of_trim_eq_zero (hm : m ≤ m0) (h : μ.trim hm s = 0) : μ s = 0 :=
le_antisymm ((le_trim hm).trans (le_of_eq h)) (zero_le _)

lemma measure_trim_to_measurable_eq_zero {hm : m ≤ m0} (hs : μ.trim hm s = 0) :
  μ (@to_measurable α m (μ.trim hm) s) = 0 :=
measure_eq_zero_of_trim_eq_zero hm (by rwa measure_to_measurable)

lemma ae_of_ae_trim (hm : m ≤ m0) {μ : measure α} {P : α → Prop} (h : ∀ᵐ x ∂(μ.trim hm), P x) :
  ∀ᵐ x ∂μ, P x :=
measure_eq_zero_of_trim_eq_zero hm h

lemma ae_eq_of_ae_eq_trim {E} {hm : m ≤ m0} {f₁ f₂ : α → E}
  (h12 : f₁ =ᶠ[@measure.ae α m (μ.trim hm)] f₂) :
  f₁ =ᵐ[μ] f₂ :=
measure_eq_zero_of_trim_eq_zero hm h12

lemma ae_le_of_ae_le_trim {E} [has_le E] {hm : m ≤ m0} {f₁ f₂ : α → E}
  (h12 : f₁ ≤ᶠ[@measure.ae α m (μ.trim hm)] f₂) :
  f₁ ≤ᵐ[μ] f₂ :=
measure_eq_zero_of_trim_eq_zero hm h12

lemma trim_trim {m₁ m₂ : measurable_space α} {hm₁₂ : m₁ ≤ m₂} {hm₂ : m₂ ≤ m0} :
  (μ.trim hm₂).trim hm₁₂ = μ.trim (hm₁₂.trans hm₂) :=
begin
  ext1 t ht,
  rw [trim_measurable_set_eq hm₁₂ ht, trim_measurable_set_eq (hm₁₂.trans hm₂) ht,
    trim_measurable_set_eq hm₂ (hm₁₂ t ht)],
end

lemma restrict_trim (hm : m ≤ m0) (μ : measure α) (hs : @measurable_set α m s) :
  @measure.restrict α m (μ.trim hm) s = (μ.restrict s).trim hm :=
begin
  ext1 t ht,
  rw [@measure.restrict_apply α m _ _ _ ht, trim_measurable_set_eq hm ht,
    measure.restrict_apply (hm t ht),
    trim_measurable_set_eq hm (@measurable_set.inter α m t s ht hs)],
end

instance is_finite_measure_trim (hm : m ≤ m0) [is_finite_measure μ] :
  is_finite_measure (μ.trim hm) :=
{ measure_univ_lt_top :=
    by { rw trim_measurable_set_eq hm (@measurable_set.univ _ m), exact measure_lt_top _ _, } }

end trim

end measure_theory

namespace is_compact

variables [topological_space α] [measurable_space α] {μ : measure α} {s : set α}

/-- If `s` is a compact set and `μ` is finite at `𝓝 x` for every `x ∈ s`, then `s` admits an open
superset of finite measure. -/
lemma exists_open_superset_measure_lt_top' (h : is_compact s)
  (hμ : ∀ x ∈ s, μ.finite_at_filter (𝓝 x)) :
  ∃ U ⊇ s, is_open U ∧ μ U < ∞ :=
begin
  refine is_compact.induction_on h _ _ _ _,
  { use ∅, simp [superset] },
  { rintro s t hst ⟨U, htU, hUo, hU⟩, exact ⟨U, hst.trans htU, hUo, hU⟩ },
  { rintro s t ⟨U, hsU, hUo, hU⟩ ⟨V, htV, hVo, hV⟩,
    refine ⟨U ∪ V, union_subset_union hsU htV, hUo.union hVo,
      (measure_union_le _ _).trans_lt $ ennreal.add_lt_top.2 ⟨hU, hV⟩⟩ },
  { intros x hx,
    rcases (hμ x hx).exists_mem_basis (nhds_basis_opens _) with ⟨U, ⟨hx, hUo⟩, hU⟩,
    exact ⟨U, nhds_within_le_nhds (hUo.mem_nhds hx), U, subset.rfl, hUo, hU⟩ }
end

/-- If `s` is a compact set and `μ` is a locally finite measure, then `s` admits an open superset of
finite measure. -/
lemma exists_open_superset_measure_lt_top (h : is_compact s)
  (μ : measure α) [is_locally_finite_measure μ] :
  ∃ U ⊇ s, is_open U ∧ μ U < ∞ :=
h.exists_open_superset_measure_lt_top' $ λ x hx, μ.finite_at_nhds x

lemma measure_lt_top_of_nhds_within (h : is_compact s) (hμ : ∀ x ∈ s, μ.finite_at_filter (𝓝[s] x)) :
  μ s < ∞ :=
is_compact.induction_on h (by simp) (λ s t hst ht, (measure_mono hst).trans_lt ht)
  (λ s t hs ht, (measure_union_le s t).trans_lt (ennreal.add_lt_top.2 ⟨hs, ht⟩)) hμ

lemma measure_zero_of_nhds_within (hs : is_compact s) :
  (∀ a ∈ s, ∃ t ∈ 𝓝[s] a, μ t = 0) → μ s = 0 :=
by simpa only [← compl_mem_ae_iff] using hs.compl_mem_sets_of_nhds_within

end is_compact

@[priority 100] -- see Note [lower instance priority]
instance is_finite_measure_on_compacts_of_is_locally_finite_measure
  [topological_space α] {m : measurable_space α} {μ : measure α}
  [is_locally_finite_measure μ] : is_finite_measure_on_compacts μ :=
⟨λ s hs, hs.measure_lt_top_of_nhds_within $ λ x hx, μ.finite_at_nhds_within _ _⟩

/-- Compact covering of a `σ`-compact topological space as
`measure_theory.measure.finite_spanning_sets_in`. -/
def measure_theory.measure.finite_spanning_sets_in_compact [topological_space α]
  [sigma_compact_space α] {m : measurable_space α} (μ : measure α) [is_locally_finite_measure μ] :
  μ.finite_spanning_sets_in {K | is_compact K} :=
{ set := compact_covering α,
  set_mem := is_compact_compact_covering α,
  finite := λ n, (is_compact_compact_covering α n).measure_lt_top,
  spanning := Union_compact_covering α }

/-- A locally finite measure on a `σ`-compact topological space admits a finite spanning sequence
of open sets. -/
def measure_theory.measure.finite_spanning_sets_in_open [topological_space α]
  [sigma_compact_space α] {m : measurable_space α} (μ : measure α) [is_locally_finite_measure μ] :
  μ.finite_spanning_sets_in {K | is_open K} :=
{ set := λ n, ((is_compact_compact_covering α n).exists_open_superset_measure_lt_top μ).some,
  set_mem := λ n,
    ((is_compact_compact_covering α n).exists_open_superset_measure_lt_top μ).some_spec.snd.1,
  finite := λ n,
    ((is_compact_compact_covering α n).exists_open_superset_measure_lt_top μ).some_spec.snd.2,
  spanning := eq_univ_of_subset (Union_mono $ λ n,
    ((is_compact_compact_covering α n).exists_open_superset_measure_lt_top μ).some_spec.fst)
    (Union_compact_covering α) }

section measure_Ixx

variables [preorder α] [topological_space α] [compact_Icc_space α]
  {m : measurable_space α} {μ : measure α} [is_locally_finite_measure μ] {a b : α}

lemma measure_Icc_lt_top : μ (Icc a b) < ∞ := is_compact_Icc.measure_lt_top

lemma measure_Ico_lt_top : μ (Ico a b) < ∞ :=
(measure_mono Ico_subset_Icc_self).trans_lt measure_Icc_lt_top

lemma measure_Ioc_lt_top : μ (Ioc a b) < ∞ :=
(measure_mono Ioc_subset_Icc_self).trans_lt measure_Icc_lt_top

lemma measure_Ioo_lt_top : μ (Ioo a b) < ∞ :=
(measure_mono Ioo_subset_Icc_self).trans_lt measure_Icc_lt_top

end measure_Ixx

section piecewise

variables [measurable_space α] {μ : measure α} {s t : set α} {f g : α → β}

lemma piecewise_ae_eq_restrict (hs : measurable_set s) : piecewise s f g =ᵐ[μ.restrict s] f :=
begin
  rw [ae_restrict_eq hs],
  exact (piecewise_eq_on s f g).eventually_eq.filter_mono inf_le_right
end

lemma piecewise_ae_eq_restrict_compl (hs : measurable_set s) :
  piecewise s f g =ᵐ[μ.restrict sᶜ] g :=
begin
  rw [ae_restrict_eq hs.compl],
  exact (piecewise_eq_on_compl s f g).eventually_eq.filter_mono inf_le_right
end

lemma piecewise_ae_eq_of_ae_eq_set (hst : s =ᵐ[μ] t) : s.piecewise f g =ᵐ[μ] t.piecewise f g :=
hst.mem_iff.mono $ λ x hx, by simp [piecewise, hx]

end piecewise

section indicator_function

variables [measurable_space α] {μ : measure α} {s t : set α} {f : α → β}

lemma mem_map_indicator_ae_iff_mem_map_restrict_ae_of_zero_mem [has_zero β] {t : set β}
  (ht : (0 : β) ∈ t) (hs : measurable_set s) :
  t ∈ filter.map (s.indicator f) μ.ae ↔ t ∈ filter.map f (μ.restrict s).ae :=
begin
  simp_rw [mem_map, mem_ae_iff],
  rw [measure.restrict_apply' hs, set.indicator_preimage, set.ite],
  simp_rw [set.compl_union, set.compl_inter],
  change μ (((f ⁻¹' t)ᶜ ∪ sᶜ) ∩ ((λ x, (0 : β)) ⁻¹' t \ s)ᶜ) = 0 ↔ μ ((f ⁻¹' t)ᶜ ∩ s) = 0,
  simp only [ht, ← set.compl_eq_univ_diff, compl_compl, set.compl_union, if_true,
    set.preimage_const],
  simp_rw [set.union_inter_distrib_right, set.compl_inter_self s, set.union_empty],
end

lemma mem_map_indicator_ae_iff_of_zero_nmem [has_zero β] {t : set β} (ht : (0 : β) ∉ t)  :
  t ∈ filter.map (s.indicator f) μ.ae ↔ μ ((f ⁻¹' t)ᶜ ∪ sᶜ) = 0 :=
begin
  rw [mem_map, mem_ae_iff, set.indicator_preimage, set.ite, set.compl_union, set.compl_inter],
  change μ (((f ⁻¹' t)ᶜ ∪ sᶜ) ∩ ((λ x, (0 : β)) ⁻¹' t \ s)ᶜ) = 0 ↔ μ ((f ⁻¹' t)ᶜ ∪ sᶜ) = 0,
  simp only [ht, if_false, set.compl_empty, set.empty_diff, set.inter_univ, set.preimage_const],
end

lemma map_restrict_ae_le_map_indicator_ae [has_zero β] (hs : measurable_set s) :
  filter.map f (μ.restrict s).ae ≤ filter.map (s.indicator f) μ.ae :=
begin
  intro t,
  by_cases ht : (0 : β) ∈ t,
  { rw mem_map_indicator_ae_iff_mem_map_restrict_ae_of_zero_mem ht hs, exact id, },
  rw [mem_map_indicator_ae_iff_of_zero_nmem ht, mem_map_restrict_ae_iff hs],
  exact λ h, measure_mono_null ((set.inter_subset_left _ _).trans (set.subset_union_left _ _)) h,
end

variables [has_zero β]

lemma indicator_ae_eq_restrict (hs : measurable_set s) : indicator s f =ᵐ[μ.restrict s] f :=
piecewise_ae_eq_restrict hs

lemma indicator_ae_eq_restrict_compl (hs : measurable_set s) : indicator s f =ᵐ[μ.restrict sᶜ] 0 :=
piecewise_ae_eq_restrict_compl hs

lemma indicator_ae_eq_of_ae_eq_set (hst : s =ᵐ[μ] t) : s.indicator f =ᵐ[μ] t.indicator f :=
piecewise_ae_eq_of_ae_eq_set hst

lemma indicator_meas_zero (hs : μ s = 0) : indicator s f =ᵐ[μ] 0 :=
(indicator_empty' f) ▸ indicator_ae_eq_of_ae_eq_set (ae_eq_empty.2 hs)

variables [measurable_space β]

end indicator_function
