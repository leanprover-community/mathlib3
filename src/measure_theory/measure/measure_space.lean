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

open classical set filter (hiding map) function measurable_space
open_locale classical topological_space big_operators filter ennreal nnreal

variables {α β γ δ ι : Type*}

namespace measure_theory

section

variables {m : measurable_space α} {μ μ₁ μ₂ : measure α} {s s₁ s₂ t : set α}

instance ae_is_measurably_generated : is_measurably_generated μ.ae :=
⟨λ s hs, let ⟨t, hst, htm, htμ⟩ := exists_measurable_superset_of_null hs in
  ⟨tᶜ, compl_mem_ae_iff.2 htμ, htm.compl, compl_subset_comm.1 hst⟩⟩

lemma measure_union (hd : disjoint s₁ s₂) (h₁ : measurable_set s₁) (h₂ : measurable_set s₂) :
  μ (s₁ ∪ s₂) = μ s₁ + μ s₂ :=
measure_union₀ h₁.null_measurable_set h₂.null_measurable_set hd

lemma measure_add_measure_compl (h : measurable_set s) :
  μ s + μ sᶜ = μ univ :=
by { rw [← union_compl_self s, measure_union _ h h.compl], exact disjoint_compl_right }

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

lemma measure_diff (h : s₂ ⊆ s₁) (h₁ : measurable_set s₁) (h₂ : measurable_set s₂)
  (h_fin : μ s₂ ≠ ∞) :
  μ (s₁ \ s₂) = μ s₁ - μ s₂ :=
begin
  refine (ennreal.add_sub_self' h_fin).symm.trans _,
  rw [← measure_union disjoint_diff h₂ (h₁.diff h₂), union_diff_cancel h]
end

lemma le_measure_diff : μ s₁ - μ s₂ ≤ μ (s₁ \ s₂) :=
tsub_le_iff_left.2 $
calc μ s₁ ≤ μ (s₂ ∪ s₁)        : measure_mono (subset_union_right _ _)
      ... = μ (s₂ ∪ s₁ \ s₂)   : congr_arg μ union_diff_self.symm
      ... ≤ μ s₂ + μ (s₁ \ s₂) : measure_union_le _ _

lemma measure_diff_lt_of_lt_add (hs : measurable_set s) (ht : measurable_set t) (hst : s ⊆ t)
  (hs' : μ s ≠ ∞) {ε : ℝ≥0∞} (h : μ t < μ s + ε) : μ (t \ s) < ε :=
begin
  rw [measure_diff hst ht hs hs'], rw add_comm at h,
  exact ennreal.sub_lt_of_lt_add (measure_mono hst) h
end

lemma measure_diff_le_iff_le_add (hs : measurable_set s) (ht : measurable_set t) (hst : s ⊆ t)
  (hs' : μ s ≠ ∞) {ε : ℝ≥0∞} : μ (t \ s) ≤ ε ↔ μ t ≤ μ s + ε :=
by rwa [measure_diff hst ht hs hs', tsub_le_iff_left]

lemma measure_eq_measure_of_null_diff {s t : set α}
  (hst : s ⊆ t) (h_nulldiff : μ (t.diff s) = 0) : μ s = μ t :=
by { rw [←diff_diff_cancel_left hst, ←@measure_diff_null _ _ _ t _ h_nulldiff], refl, }

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
  (h12 : s₁ ⊆ s₂) (h23 : s₂ ⊆ s₃) (h_nulldiff : μ (s₃.diff s₁) = 0) : μ s₁ = μ s₂ :=
(measure_eq_measure_of_between_null_diff h12 h23 h_nulldiff).1

lemma measure_eq_measure_larger_of_between_null_diff {s₁ s₂ s₃ : set α}
  (h12 : s₁ ⊆ s₂) (h23 : s₂ ⊆ s₃) (h_nulldiff : μ (s₃.diff s₁) = 0) : μ s₂ = μ s₃ :=
(measure_eq_measure_of_between_null_diff h12 h23 h_nulldiff).2

lemma measure_compl (h₁ : measurable_set s) (h_fin : μ s ≠ ∞) : μ (sᶜ) = μ univ - μ s :=
by { rw compl_eq_univ_diff, exact measure_diff (subset_univ s) measurable_set.univ h₁ h_fin }

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

/-- If `sᵢ` is a countable family of measurable sets such that all pairwise intersections have
measure `0`, then there exists a subordinate family `tᵢ ⊆ sᵢ` of measurable pairwise disjoint sets
such that `tᵢ =ᵐ[μ] sᵢ`. -/
lemma exists_subordinate_pairwise_disjoint [encodable ι] {s : ι → set α}
  (h : ∀ i, measurable_set (s i)) (hd : pairwise (λ i j, μ (s i ∩ s j) = 0)) :
  ∃ t : ι → set α, (∀ i, t i ⊆ s i) ∧ (∀ i, s i =ᵐ[μ] t i) ∧ (∀ i, measurable_set (t i)) ∧
    pairwise (disjoint on t) :=
begin
  set t : ι → set α := λ i, s i \ ⋃ j ∈ ({i}ᶜ : set ι), s j,
  refine ⟨t, λ i, diff_subset _ _, λ i, _, λ i, (h i).diff $
    measurable_set.bUnion (countable_encodable _) $ λ j hj, h j, _⟩,
  { refine eventually_le.antisymm _ (diff_subset _ _).eventually_le,
    rw [ae_le_set, sdiff_sdiff_right_self, inf_eq_inter],
    simp only [inter_Union, measure_bUnion_null_iff (countable_encodable _)],
    exact λ j hj, hd _ _ (ne.symm hj) },
  { rintros i j hne x ⟨⟨hsi, -⟩, -, Hj⟩,
    exact Hj (mem_bUnion hne hsi) }
end

lemma measure_Union_of_null_inter [encodable ι] {f : ι → set α} (h : ∀ i, measurable_set (f i))
  (hn : pairwise ((λ S T, μ (S ∩ T) = 0) on f)) : μ (⋃ i, f i) = ∑' i, μ (f i) :=
begin
  rcases exists_subordinate_pairwise_disjoint h hn with ⟨t, ht_sub, ht_eq, htm, htd⟩,
  calc μ (⋃ i, f i) = μ (⋃ i, t i)  : measure_congr (eventually_eq.countable_Union ht_eq)
                ... = ∑' i, μ (t i) : measure_Union htd htm
                ... = ∑' i, μ (f i) : tsum_congr (λ i, measure_congr (ht_eq i).symm)
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

/-- Continuity from below: the measure of the union of a directed sequence of measurable sets
is the supremum of the measures. -/
lemma measure_Union_eq_supr [encodable ι] {s : ι → set α} (h : ∀ i, measurable_set (s i))
  (hd : directed (⊆) s) : μ (⋃ i, s i) = ⨆ i, μ (s i) :=
begin
  casesI is_empty_or_nonempty ι,
  { simp only [supr_of_empty, Union], exact measure_empty },
  refine le_antisymm _ (supr_le $ λ i, measure_mono $ subset_Union _ _),
  have : ∀ n, measurable_set (disjointed (λ n, ⋃ b ∈ encodable.decode₂ ι n, s b) n) :=
    measurable_set.disjointed (measurable_set.bUnion_decode₂ h),
  have hn : pairwise (disjoint on
    λ (n : ℕ), disjointed (λ (n : ℕ), ⋃ (b : ι) (H : b ∈ encodable.decode₂ ι n), s b) n) :=
    disjoint_disjointed _,
  rw [← encodable.Union_decode₂, ← Union_disjointed, measure_Union hn this,
    ennreal.tsum_eq_supr_nat],
  simp only [← measure_bUnion_finset (hn.set_pairwise _) (λ n _, this n)],
  refine supr_le (λ n, _),
  refine le_trans (_ : _ ≤ μ (⋃ (k ∈ finset.range n) (i ∈ encodable.decode₂ ι k), s i)) _,
  exact measure_mono (bUnion_mono (λ k hk, disjointed_subset _ _)),
  simp only [← finset.set_bUnion_option_to_finset, ← finset.set_bUnion_bUnion],
  generalize : (finset.range n).bUnion (λ k, (encodable.decode₂ ι k).to_finset) = t,
  rcases hd.finset_le t with ⟨i, hi⟩,
  exact le_supr_of_le i (measure_mono $ bUnion_subset hi)
end

lemma measure_bUnion_eq_supr {s : ι → set α} {t : set ι} (ht : countable t)
  (h : ∀ i ∈ t, measurable_set (s i)) (hd : directed_on ((⊆) on s) t) :
  μ (⋃ i ∈ t, s i) = ⨆ i ∈ t, μ (s i) :=
begin
  haveI := ht.to_encodable,
  rw [bUnion_eq_Union, measure_Union_eq_supr (set_coe.forall'.1 h) hd.directed_coe,
    supr_subtype'],
  refl
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
    ← measure_diff (Inter_subset _ k) (h k) (measurable_set.Inter h) (this _ (Inter_subset _ k)),
    diff_Inter, measure_Union_eq_supr],
  { congr' 1,
    refine le_antisymm (supr_le_supr2 $ λ i, _) (supr_le_supr $ λ i, _),
    { rcases hd i k with ⟨j, hji, hjk⟩,
      use j,
      rw [← measure_diff hjk (h _) (h _) (this _ hjk)],
      exact measure_mono (diff_subset_diff_right hji) },
    { rw [tsub_le_iff_right, ← measure_union disjoint_diff.symm ((h k).diff (h i)) (h i),
        set.union_comm],
      exact measure_mono (diff_subset_iff.1 $ subset.refl _) } },
  { exact λ i, (h k).diff (h i) },
  { exact hd.mono_comp _ (λ _ _, diff_subset_diff_right) }
end

/-- Continuity from below: the measure of the union of an increasing sequence of measurable sets
is the limit of the measures. -/
lemma tendsto_measure_Union [semilattice_sup ι] [encodable ι] {s : ι → set α}
  (hs : ∀ n, measurable_set (s n)) (hm : monotone s) :
  tendsto (μ ∘ s) at_top (𝓝 (μ (⋃ n, s n))) :=
begin
  rw measure_Union_eq_supr hs (directed_of_sup hm),
  exact tendsto_at_top_supr (assume n m hnm, measure_mono $ hm hnm)
end

/-- Continuity from above: the measure of the intersection of a decreasing sequence of measurable
sets is the limit of the measures. -/
lemma tendsto_measure_Inter [encodable ι] [semilattice_sup ι] {s : ι → set α}
  (hs : ∀ n, measurable_set (s n)) (hm : antitone s) (hf : ∃ i, μ (s i) ≠ ∞) :
  tendsto (μ ∘ s) at_top (𝓝 (μ (⋂ n, s n))) :=
begin
  rw measure_Inter_eq_infi hs (directed_of_sup hm) hf,
  exact tendsto_at_top_infi (assume n m hnm, measure_mono $ hm hnm),
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
begin
  assume s hs,
  rw to_outer_measure_eq_induced_outer_measure,
  refine outer_measure.of_function_caratheodory (λ t, le_infi $ λ ht, _),
  rw [← measure_eq_extend (ht.inter hs),
    ← measure_eq_extend (ht.diff hs),
    ← measure_union _ (ht.inter hs) (ht.diff hs),
    inter_union_diff],
  exact le_refl _,
  exact λ x ⟨⟨_, h₁⟩, _, h₂⟩, h₂ h₁
end

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

lemma measure_inter_add_diff (s : set α) (ht : measurable_set t) :
  μ (s ∩ t) + μ (s \ t) = μ s :=
(le_to_outer_measure_caratheodory μ _ ht _).symm

lemma measure_union_add_inter (s : set α) (ht : measurable_set t) :
  μ (s ∪ t) + μ (s ∩ t) = μ s + μ t :=
by { rw [← measure_inter_add_diff (s ∪ t) ht, set.union_inter_cancel_right,
  union_diff_right, ← measure_inter_add_diff s ht], ac_refl }

lemma measure_union_add_inter' (hs : measurable_set s) (t : set α) :
  μ (s ∪ t) + μ (s ∩ t) = μ s + μ t :=
by rw [union_comm, inter_comm, measure_union_add_inter t hs, add_comm]
namespace measure

/-- If `u` is a superset of `t` with the same measure (both sets possibly non-measurable), then
for any measurable set `s` one also has `μ (t ∩ s) = μ (u ∩ s)`. -/
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

instance add_comm_monoid [measurable_space α] : add_comm_monoid (measure α) :=
to_outer_measure_injective.add_comm_monoid to_outer_measure zero_to_outer_measure
  add_to_outer_measure

instance [measurable_space α] : has_scalar ℝ≥0∞ (measure α) :=
⟨λ c μ,
  { to_outer_measure := c • μ.to_outer_measure,
    m_Union := λ s hs hd, by simp [measure_Union, *, ennreal.tsum_mul_left],
    trimmed := by rw [outer_measure.trim_smul, μ.trimmed] }⟩

@[simp] theorem smul_to_outer_measure {m : measurable_space α} (c : ℝ≥0∞) (μ : measure α) :
  (c • μ).to_outer_measure = c • μ.to_outer_measure :=
rfl

@[simp, norm_cast] theorem coe_smul {m : measurable_space α} (c : ℝ≥0∞) (μ : measure α) :
  ⇑(c • μ) = c • μ :=
rfl

@[simp] theorem smul_apply {m : measurable_space α} (c : ℝ≥0∞) (μ : measure α) (s : set α) :
  (c • μ) s = c * μ s :=
rfl

instance [measurable_space α] : module ℝ≥0∞ (measure α) :=
injective.module ℝ≥0∞ ⟨to_outer_measure, zero_to_outer_measure, add_to_outer_measure⟩
  to_outer_measure_injective smul_to_outer_measure

@[simp, norm_cast] theorem coe_nnreal_smul {m : measurable_space α} (c : ℝ≥0) (μ : measure α) :
  ⇑(c • μ) = c • μ :=
rfl

@[simp] theorem coe_nnreal_smul_apply {m : measurable_space α} (c : ℝ≥0) (μ : measure α)
  (s : set α) :
  (c • μ) s = c * μ s :=
rfl

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
  le_refl     := assume m s hs, le_refl _,
  le_trans    := assume m₁ m₂ m₃ h₁ h₂ s hs, le_trans (h₁ s hs) (h₂ s hs),
  le_antisymm := assume m₁ m₂ h₁ h₂, ext $
    assume s hs, le_antisymm (h₁ s hs) (h₂ s hs) }

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
assume s hs, by rw [Inf_apply hs, ← to_outer_measure_apply]; exact this s

private lemma measure_le_Inf (h : ∀ μ' ∈ m, μ ≤ μ') : μ ≤ Inf m :=
have μ.to_outer_measure ≤ Inf (to_outer_measure '' m) :=
  le_Inf $ ball_image_of_ball $ assume μ hμ, to_outer_measure_le.2 $ h _ hμ,
assume s hs, by rw [Inf_apply hs, ← to_outer_measure_apply]; exact this s

instance [measurable_space α] : complete_semilattice_Inf (measure α) :=
{ Inf_le := λ s a, measure_Inf_le,
  le_Inf := λ s a, measure_le_Inf,
  ..(by apply_instance : partial_order (measure α)),
  ..(by apply_instance : has_Inf (measure α)), }

instance [measurable_space α] : complete_lattice (measure α) :=
{ bot := 0,
  bot_le := assume a s hs, by exact bot_le,
/- Adding an explicit `top` makes `leanchecker` fail, see lean#364, disable for now

  top := (⊤ : outer_measure α).to_measure (by rw [outer_measure.top_caratheodory]; exact le_top),
  le_top := assume a s hs,
    by cases s.eq_empty_or_nonempty with h  h;
      simp [h, to_measure_apply ⊤ _ hs, outer_measure.top_apply],
-/
  .. complete_lattice_of_complete_semilattice_Inf (measure α) }

end Inf

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

/-- The pushforward of a measure. It is defined to be `0` if `f` is not a measurable function. -/
def map [measurable_space α] (f : α → β) : measure α →ₗ[ℝ≥0∞] measure β :=
if hf : measurable f then
  lift_linear (outer_measure.map f) $ λ μ s hs t,
    le_to_outer_measure_caratheodory μ _ (hf hs) (f ⁻¹' t)
else 0

/-- We can evaluate the pushforward on measurable sets. For non-measurable sets, see
  `measure_theory.measure.le_map_apply` and `measurable_equiv.map_apply`. -/
@[simp] theorem map_apply {f : α → β} (hf : measurable f) {s : set β} (hs : measurable_set s) :
  map f μ s = μ (f ⁻¹' s) :=
by simp [map, dif_pos hf, hs]

lemma map_to_outer_measure {f : α → β} (hf : measurable f) :
  (map f μ).to_outer_measure = (outer_measure.map f μ.to_outer_measure).trim :=
begin
  rw [← trimmed, outer_measure.trim_eq_trim_iff],
  intros s hs,
  rw [coe_to_outer_measure, map_apply hf hs, outer_measure.map_apply, coe_to_outer_measure]
end

theorem map_of_not_measurable {f : α → β} (hf : ¬measurable f) :
  map f μ = 0 :=
by rw [map, dif_neg hf, linear_map.zero_apply]

@[simp] lemma map_id : map id μ = μ :=
ext $ λ s, map_apply measurable_id

lemma map_map {g : β → γ} {f : α → β} (hg : measurable g) (hf : measurable f) :
  map g (map f μ) = map (g ∘ f) μ :=
ext $ λ s hs,
by simp [hf, hg, hs, hg hs, hg.comp hf, ← preimage_comp]

@[mono] lemma map_mono (f : α → β) (h : μ ≤ ν) : map f μ ≤ map f ν :=
if hf : measurable f then λ s hs, by simp only [map_apply hf hs, h _ (hf hs)]
else by simp only [map_of_not_measurable hf, le_rfl]

/-- Even if `s` is not measurable, we can bound `map f μ s` from below.
  See also `measurable_equiv.map_apply`. -/
theorem le_map_apply {f : α → β} (hf : measurable f) (s : set β) : μ (f ⁻¹' s) ≤ map f μ s :=
calc μ (f ⁻¹' s) ≤ μ (f ⁻¹' (to_measurable (map f μ) s)) :
  measure_mono $ preimage_mono $ subset_to_measurable _ _
... = map f μ (to_measurable (map f μ) s) : (map_apply hf $ measurable_set_to_measurable _ _).symm
... = map f μ s : measure_to_measurable _

/-- Even if `s` is not measurable, `map f μ s = 0` implies that `μ (f ⁻¹' s) = 0`. -/
lemma preimage_null_of_map_null {f : α → β} (hf : measurable f) {s : set β}
  (hs : map f μ s = 0) : μ (f ⁻¹' s) = 0 :=
nonpos_iff_eq_zero.mp $ (le_map_apply hf s).trans_eq hs

lemma tendsto_ae_map {f : α → β} (hf : measurable f) : tendsto f μ.ae (map f μ).ae :=
λ s hs, preimage_null_of_map_null hf hs

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

/-- If `s` is a measurable set, then the outer measure of `t` with respect to the restriction of
the measure to `s` equals the outer measure of `t ∩ s`. This is an alternate version of
`measure.restrict_apply`, requiring that `s` is measurable instead of `t`. -/
@[simp] lemma restrict_apply' (hs : measurable_set s) : μ.restrict s t = μ (t ∩ s) :=
by rw [← coe_to_outer_measure, measure.restrict_to_outer_measure_eq_to_outer_measure_restrict hs,
      outer_measure.restrict_apply s t _, coe_to_outer_measure]

lemma restrict_eq_self' (hs : measurable_set s) (t_subset : t ⊆ s) :
  μ.restrict s t = μ t :=
by rw [restrict_apply' hs, set.inter_eq_self_of_subset_left t_subset]

lemma restrict_eq_self (h_meas_t : measurable_set t) (h : t ⊆ s) : μ.restrict s t = μ t :=
by rw [restrict_apply h_meas_t, inter_eq_left_iff_subset.mpr h]

lemma restrict_apply_self {m0 : measurable_space α} (μ : measure α) (h_meas_s : measurable_set s) :
  (μ.restrict s) s = μ s := (restrict_eq_self h_meas_s (set.subset.refl _))

lemma restrict_apply_univ (s : set α) : μ.restrict s univ = μ s :=
by rw [restrict_apply measurable_set.univ, set.univ_inter]

lemma le_restrict_apply (s t : set α) :
  μ (t ∩ s) ≤ μ.restrict s t :=
by { rw [restrict, restrictₗ], convert le_lift_linear_apply _ t, simp }

@[simp] lemma restrict_add {m0 : measurable_space α} (μ ν : measure α) (s : set α) :
  (μ + ν).restrict s = μ.restrict s + ν.restrict s :=
(restrictₗ s).map_add μ ν

@[simp] lemma restrict_zero {m0 : measurable_space α} (s : set α) :
  (0 : measure α).restrict s = 0 :=
(restrictₗ s).map_zero

@[simp] lemma restrict_smul {m0 : measurable_space α} (c : ℝ≥0∞) (μ : measure α) (s : set α) :
  (c • μ).restrict s = c • μ.restrict s :=
(restrictₗ s).map_smul c μ

@[simp] lemma restrict_restrict (hs : measurable_set s) :
  (μ.restrict t).restrict s = μ.restrict (s ∩ t) :=
ext $ λ u hu, by simp [*, set.inter_assoc]

lemma restrict_comm (hs : measurable_set s) (ht : measurable_set t) :
  (μ.restrict t).restrict s = (μ.restrict s).restrict t :=
by rw [restrict_restrict hs, restrict_restrict ht, inter_comm]

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
by simp only [measure.restrict_eq_zero, h]

@[simp] lemma restrict_empty : μ.restrict ∅ = 0 := restrict_zero_set measure_empty

@[simp] lemma restrict_univ : μ.restrict univ = μ := ext $ λ s hs, by simp [hs]

lemma restrict_union_apply (h : disjoint (t ∩ s) (t ∩ s')) (hs : measurable_set s)
  (hs' : measurable_set s') (ht : measurable_set t) :
  μ.restrict (s ∪ s') t = μ.restrict s t + μ.restrict s' t :=
begin
  simp only [restrict_apply, ht, set.inter_union_distrib_left],
  exact measure_union h (ht.inter hs) (ht.inter hs'),
end

lemma restrict_union (h : disjoint s t) (hs : measurable_set s) (ht : measurable_set t) :
  μ.restrict (s ∪ t) = μ.restrict s + μ.restrict t :=
ext $ λ t' ht', restrict_union_apply (h.mono inf_le_right inf_le_right) hs ht ht'

lemma restrict_union_add_inter (s : set α) (ht : measurable_set t) :
  μ.restrict (s ∪ t) + μ.restrict (s ∩ t) = μ.restrict s + μ.restrict t :=
begin
  ext1 u hu,
  simp only [add_apply, restrict_apply hu, inter_union_distrib_left],
  convert measure_union_add_inter (u ∩ s) (hu.inter ht) using 3,
  rw [set.inter_left_comm (u ∩ s), set.inter_assoc, ← set.inter_assoc u u, set.inter_self]
end

@[simp] lemma restrict_add_restrict_compl (hs : measurable_set s) :
  μ.restrict s + μ.restrict sᶜ = μ :=
by rw [← restrict_union (@disjoint_compl_right (set α) _ _) hs hs.compl,
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
  (hd : pairwise (λ i j, μ (s i ∩ s j) = 0))
  (hm : ∀ i, measurable_set (s i)) {t : set α} (ht : measurable_set t) :
  μ.restrict (⋃ i, s i) t = ∑' i, μ.restrict (s i) t :=
begin
  simp only [restrict_apply, ht, inter_Union],
  exact measure_Union_of_null_inter (λ i, ht.inter (hm _)) (λ i j hne, measure_mono_null
    (inter_subset_inter (inter_subset_right _ _) (inter_subset_right _ _)) (hd i j hne))
end

lemma restrict_Union_apply [encodable ι] {s : ι → set α} (hd : pairwise (disjoint on s))
  (hm : ∀ i, measurable_set (s i)) {t : set α} (ht : measurable_set t) :
  μ.restrict (⋃ i, s i) t = ∑' i, μ.restrict (s i) t :=
restrict_Union_apply_ae (λ i j hij, by simp [set.disjoint_iff_inter_eq_empty.1 (hd i j hij)]) hm ht

lemma restrict_Union_apply_eq_supr [encodable ι] {s : ι → set α}
  (hm : ∀ i, measurable_set (s i)) (hd : directed (⊆) s) {t : set α} (ht : measurable_set t) :
  μ.restrict (⋃ i, s i) t = ⨆ i, μ.restrict (s i) t :=
begin
  simp only [restrict_apply ht, inter_Union],
  rw [measure_Union_eq_supr],
  exacts [λ i, ht.inter (hm i), hd.mono_comp _ (λ s₁ s₂, inter_subset_inter_right _)]
end

lemma restrict_map {f : α → β} (hf : measurable f) {s : set β} (hs : measurable_set s) :
  (map f μ).restrict s = map f (μ.restrict $ f ⁻¹' s) :=
ext $ λ t ht, by simp [*, hf ht]

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

lemma restrict_le_self : μ.restrict s ≤ μ :=
assume t ht,
calc μ.restrict s t = μ (t ∩ s) : restrict_apply ht
... ≤ μ t : measure_mono $ inter_subset_left t s

lemma restrict_mono_ae (h : s ≤ᵐ[μ] t) : μ.restrict s ≤ μ.restrict t :=
restrict_mono' h (le_refl μ)

lemma restrict_congr_set (h : s =ᵐ[μ] t) : μ.restrict s = μ.restrict t :=
le_antisymm (restrict_mono_ae h.le) (restrict_mono_ae h.symm.le)

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

lemma restrict_congr_mono (hs : s ⊆ t) (hm : measurable_set s) (h : μ.restrict t = ν.restrict t) :
  μ.restrict s = ν.restrict s :=
by rw [← inter_eq_self_of_subset_left hs, ← restrict_restrict hm, h, restrict_restrict hm]

/-- If two measures agree on all measurable subsets of `s` and `t`, then they agree on all
measurable subsets of `s ∪ t`. -/
lemma restrict_union_congr (hsm : measurable_set s) (htm : measurable_set t) :
  μ.restrict (s ∪ t) = ν.restrict (s ∪ t) ↔
    μ.restrict s = ν.restrict s ∧ μ.restrict t = ν.restrict t :=
begin
  refine ⟨λ h, ⟨restrict_congr_mono (subset_union_left _ _) hsm h,
    restrict_congr_mono (subset_union_right _ _) htm h⟩, _⟩,
  simp only [restrict_congr_meas, hsm, htm, hsm.union htm],
  rintros ⟨hs, ht⟩ u hu hum,
  rw [← measure_inter_add_diff u hsm, ← measure_inter_add_diff u hsm,
    hs _ (inter_subset_right _ _) (hum.inter hsm),
    ht _ (diff_subset_iff.2 hu) (hum.diff hsm)]
end

lemma restrict_finset_bUnion_congr {s : finset ι} {t : ι → set α}
  (htm : ∀ i ∈ s, measurable_set (t i)) :
  μ.restrict (⋃ i ∈ s, t i) = ν.restrict (⋃ i ∈ s, t i) ↔
    ∀ i ∈ s, μ.restrict (t i) = ν.restrict (t i) :=
begin
  induction s using finset.induction_on with i s hi hs, { simp },
  simp only [finset.mem_insert, or_imp_distrib, forall_and_distrib, forall_eq] at htm ⊢,
  simp only [finset.set_bUnion_insert, ← hs htm.2],
  exact restrict_union_congr htm.1 (s.measurable_set_bUnion htm.2)
end

lemma restrict_Union_congr [encodable ι] {s : ι → set α} (hm : ∀ i, measurable_set (s i)) :
  μ.restrict (⋃ i, s i) = ν.restrict (⋃ i, s i) ↔
    ∀ i, μ.restrict (s i) = ν.restrict (s i) :=
begin
  refine ⟨λ h i, restrict_congr_mono (subset_Union _ _) (hm i) h, λ h, _⟩,
  ext1 t ht,
  have M : ∀ t : finset ι, measurable_set (⋃ i ∈ t, s i) :=
    λ t, t.measurable_set_bUnion (λ i _, hm i),
  have D : directed (⊆) (λ t : finset ι, ⋃ i ∈ t, s i) :=
    directed_of_sup (λ t₁ t₂ ht, bUnion_subset_bUnion_left ht),
  rw [Union_eq_Union_finset],
  simp only [restrict_Union_apply_eq_supr M D ht,
    (restrict_finset_bUnion_congr (λ i hi, hm i)).2 (λ i hi, h i)],
end

lemma restrict_bUnion_congr {s : set ι} {t : ι → set α} (hc : countable s)
  (htm : ∀ i ∈ s, measurable_set (t i)) :
  μ.restrict (⋃ i ∈ s, t i) = ν.restrict (⋃ i ∈ s, t i) ↔
    ∀ i ∈ s, μ.restrict (t i) = ν.restrict (t i) :=
begin
  simp only [bUnion_eq_Union, set_coe.forall'] at htm ⊢,
  haveI := hc.to_encodable,
  exact restrict_Union_congr htm
end

lemma restrict_sUnion_congr {S : set (set α)} (hc : countable S) (hm : ∀ s ∈ S, measurable_set s) :
  μ.restrict (⋃₀ S) = ν.restrict (⋃₀ S) ↔ ∀ s ∈ S, μ.restrict s = ν.restrict s :=
by rw [sUnion_eq_bUnion, restrict_bUnion_congr hc hm]

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
lemma ext_iff_of_Union_eq_univ [encodable ι] {s : ι → set α}
  (hm : ∀ i, measurable_set (s i)) (hs : (⋃ i, s i) = univ) :
  μ = ν ↔ ∀ i, μ.restrict (s i) = ν.restrict (s i) :=
by rw [← restrict_Union_congr hm, hs, restrict_univ, restrict_univ]

alias ext_iff_of_Union_eq_univ ↔ _ measure_theory.measure.ext_of_Union_eq_univ

/-- Two measures are equal if they have equal restrictions on a spanning collection of sets
  (formulated using `bUnion`). -/
lemma ext_iff_of_bUnion_eq_univ {S : set ι} {s : ι → set α} (hc : countable S)
  (hm : ∀ i ∈ S, measurable_set (s i)) (hs : (⋃ i ∈ S, s i) = univ) :
  μ = ν ↔ ∀ i ∈ S, μ.restrict (s i) = ν.restrict (s i) :=
by rw [← restrict_bUnion_congr hc hm, hs, restrict_univ, restrict_univ]

alias ext_iff_of_bUnion_eq_univ ↔ _ measure_theory.measure.ext_of_bUnion_eq_univ

/-- Two measures are equal if they have equal restrictions on a spanning collection of sets
  (formulated using `sUnion`). -/
lemma ext_iff_of_sUnion_eq_univ {S : set (set α)} (hc : countable S)
  (hm : ∀ s ∈ S, measurable_set s) (hs : (⋃₀ S) = univ) :
  μ = ν ↔ ∀ s ∈ S, μ.restrict s = ν.restrict s :=
ext_iff_of_bUnion_eq_univ hc hm $ by rwa ← sUnion_eq_bUnion

alias ext_iff_of_sUnion_eq_univ ↔ _ measure_theory.measure.ext_of_sUnion_eq_univ

lemma ext_of_generate_from_of_cover {S T : set (set α)}
  (h_gen : ‹_› = generate_from S) (hc : countable T)
  (h_inter : is_pi_system S)
  (hm : ∀ t ∈ T, measurable_set t) (hU : ⋃₀ T = univ) (htop : ∀ t ∈ T, μ t ≠ ∞)
  (ST_eq : ∀ (t ∈ T) (s ∈ S), μ (s ∩ t) = ν (s ∩ t)) (T_eq : ∀ t ∈ T, μ t = ν t) :
  μ = ν :=
begin
  refine ext_of_sUnion_eq_univ hc hm hU (λ t ht, _),
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
    have : pairwise (disjoint on λ n, f n ∩ t) :=
      λ m n hmn, (hfd m n hmn).mono (inter_subset_left _ _) (inter_subset_left _ _),
    simp only [Union_inter, measure_Union this (λ n, (hfm n).inter (hm t ht)), h_eq] }
end

/-- Two measures are equal if they are equal on the π-system generating the σ-algebra,
  and they are both finite on a increasing spanning sequence of sets in the π-system.
  This lemma is formulated using `sUnion`. -/
lemma ext_of_generate_from_of_cover_subset {S T : set (set α)}
  (h_gen : ‹_› = generate_from S)
  (h_inter : is_pi_system S)
  (h_sub : T ⊆ S) (hc : countable T) (hU : ⋃₀ T = univ) (htop : ∀ s ∈ T, μ s ≠ ∞)
  (h_eq : ∀ s ∈ S, μ s = ν s) :
  μ = ν :=
begin
  refine ext_of_generate_from_of_cover h_gen hc h_inter _ hU htop _ (λ t ht, h_eq t (h_sub ht)),
  { intros t ht, rw [h_gen], exact generate_measurable.basic _ (h_sub ht) },
  { intros t ht s hs, cases (s ∩ t).eq_empty_or_nonempty with H H,
    { simp only [H, measure_empty] },
    { exact h_eq _ (h_inter _ _ hs (h_sub ht) H) } }
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
  map f (dirac a) = dirac (f a) :=
ext $ assume s hs, by simp [hs, map_apply hf hs, hf hs, indicator_apply]

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

@[simp] lemma ae_sum_eq [encodable ι] (μ : ι → measure α) : (sum μ).ae = ⨆ i, (μ i).ae :=
filter.ext $ λ s, ae_sum_iff.trans mem_supr.symm

@[simp] lemma sum_bool (f : bool → measure α) : sum f = f tt + f ff :=
ext $ λ s hs, by simp [hs, tsum_fintype]

@[simp] lemma sum_cond (μ ν : measure α) : sum (λ b, cond b μ ν) = μ + ν := sum_bool _

@[simp] lemma restrict_sum (μ : ι → measure α) {s : set α} (hs : measurable_set s) :
  (sum μ).restrict s = sum (λ i, (μ i).restrict s) :=
ext $ λ t ht, by simp only [sum_apply, restrict_apply, ht, ht.inter hs]

@[simp] lemma sum_of_empty [is_empty ι] (μ : ι → measure α) : sum μ = 0 :=
by rw [← measure_univ_eq_zero, sum_apply _ measurable_set.univ, tsum_empty]

lemma sum_congr {μ ν : ℕ → measure α} (h : ∀ n, μ n = ν n) : sum μ = sum ν :=
by { congr, ext1 n, exact h n }

lemma sum_add_sum (μ ν : ℕ → measure α) : sum μ + sum ν = sum (λ n, μ n + ν n) :=
begin
  ext1 s hs,
  simp only [add_apply, sum_apply _ hs, pi.add_apply, coe_add,
             tsum_add ennreal.summable ennreal.summable],
end

/-- If `f` is a map with encodable codomain, then `map f μ` is the sum of Dirac measures -/
lemma map_eq_sum [encodable β] [measurable_singleton_class β]
  (μ : measure α) (f : α → β) (hf : measurable f) :
  map f μ = sum (λ b : β, μ (f ⁻¹' {b}) • dirac b) :=
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

lemma restrict_Union_ae [encodable ι] {s : ι → set α} (hd : pairwise (λ i j, μ (s i ∩ s j) = 0))
  (hm : ∀ i, measurable_set (s i)) :
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

@[simp] lemma count_apply_eq_top [measurable_singleton_class α] : count s = ∞ ↔ s.infinite :=
begin
  by_cases hs : s.finite,
  { simp [set.infinite, hs, count_apply_finite] },
  { change s.infinite at hs,
    simp [hs, count_apply_infinite] }
end

@[simp] lemma count_apply_lt_top [measurable_singleton_class α] : count s < ∞ ↔ s.finite :=
calc count s < ∞ ↔ count s ≠ ∞ : lt_top_iff_ne_top
             ... ↔ ¬s.infinite : not_congr count_apply_eq_top
             ... ↔ s.finite    : not_not

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

@[mono] protected lemma map (h : μ ≪ ν) (f : α → β) : map f μ ≪ map f ν :=
if hf : measurable f then absolutely_continuous.mk $ λ s hs, by simpa [hf, hs] using @h _
else by simp only [map_of_not_measurable hf]

protected lemma smul (h : μ ≪ ν) (c : ℝ≥0∞) : c • μ ≪ ν :=
mk (λ s hs hνs, by simp only [h hνs, algebra.id.smul_eq_mul, coe_smul, pi.smul_apply, mul_zero])

protected lemma coe_nnreal_smul (h : μ ≪ ν) (c : ℝ≥0) : c • μ ≪ ν :=
h.smul c

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
(absolutely_continuous : map f μa ≪ μb)

namespace quasi_measure_preserving

protected lemma id {m0 : measurable_space α} (μ : measure α) : quasi_measure_preserving id μ μ :=
⟨measurable_id, map_id.absolutely_continuous⟩

variables {μa μa' : measure α} {μb μb' : measure β} {μc : measure γ} {f : α → β}

lemma mono_left (h : quasi_measure_preserving f μa μb)
  (ha : μa' ≪ μa) : quasi_measure_preserving f μa' μb :=
⟨h.1, (ha.map f).trans h.2⟩

lemma mono_right (h : quasi_measure_preserving f μa μb)
  (ha : μb ≪ μb') : quasi_measure_preserving f μa μb' :=
⟨h.1, h.2.trans ha⟩

@[mono] lemma mono (ha : μa' ≪ μa) (hb : μb ≪ μb') (h : quasi_measure_preserving f μa μb) :
  quasi_measure_preserving f μa' μb' :=
(h.mono_left ha).mono_right hb

protected lemma comp {g : β → γ} {f : α → β} (hg : quasi_measure_preserving g μb μc)
  (hf : quasi_measure_preserving f μa μb) :
  quasi_measure_preserving (g ∘ f) μa μc :=
⟨hg.measurable.comp hf.measurable, by { rw ← map_map hg.1 hf.1, exact (hf.2.map g).trans hg.2 }⟩

protected lemma iterate {f : α → α} (hf : quasi_measure_preserving f μa μa) :
  ∀ n, quasi_measure_preserving (f^[n]) μa μa
| 0 := quasi_measure_preserving.id μa
| (n + 1) := (iterate n).comp hf

lemma ae_map_le (h : quasi_measure_preserving f μa μb) : (map f μa).ae ≤ μb.ae :=
h.2.ae_le

lemma tendsto_ae (h : quasi_measure_preserving f μa μb) : tendsto f μa.ae μb.ae :=
(tendsto_ae_map h.1).mono_right h.ae_map_le

lemma ae (h : quasi_measure_preserving f μa μb) {p : β → Prop} (hg : ∀ᵐ x ∂μb, p x) :
  ∀ᵐ x ∂μa, p (f x) :=
h.tendsto_ae hg

lemma ae_eq (h : quasi_measure_preserving f μa μb) {g₁ g₂ : β → δ} (hg : g₁ =ᵐ[μb] g₂) :
  g₁ ∘ f =ᵐ[μa] g₂ ∘ f :=
h.ae hg

lemma preimage_null (h : quasi_measure_preserving f μa μb) {s : set β} (hs : μb s = 0) :
  μa (f ⁻¹' s) = 0 :=
preimage_null_of_map_null h.1 (h.2 hs)

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

lemma null_measurable_set.mono_ac (h : null_measurable_set s μ) (hle : ν ≪ μ) :
  null_measurable_set s ν :=
⟨to_measurable μ s, measurable_set_to_measurable _ _, hle.ae_eq h.to_measurable_ae_eq.symm⟩

lemma null_measurable_set.mono (h : null_measurable_set s μ) (hle : ν ≤ μ) :
  null_measurable_set s ν :=
h.mono_ac hle.absolutely_continuous

@[simp] lemma ae_eq_bot : μ.ae = ⊥ ↔ μ = 0 :=
by rw [← empty_mem_iff_bot, mem_ae_iff, compl_empty, measure_univ_eq_zero]

@[simp] lemma ae_ne_bot : μ.ae.ne_bot ↔ μ ≠ 0 :=
ne_bot_iff.trans (not_congr ae_eq_bot)

@[simp] lemma ae_zero {m0 : measurable_space α} : (0 : measure α).ae = ⊥ := ae_eq_bot.2 rfl

@[mono] lemma ae_mono (h : μ ≤ ν) : μ.ae ≤ ν.ae := h.absolutely_continuous.ae_le

lemma mem_ae_map_iff {f : α → β} (hf : measurable f) {s : set β} (hs : measurable_set s) :
  s ∈ (map f μ).ae ↔ (f ⁻¹' s) ∈ μ.ae :=
by simp only [mem_ae_iff, map_apply hf hs.compl, preimage_compl]

lemma mem_ae_of_mem_ae_map {f : α → β} (hf : measurable f) {s : set β} (hs : s ∈ (map f μ).ae) :
  f ⁻¹' s ∈ μ.ae :=
(tendsto_ae_map hf).eventually hs

lemma ae_map_iff {f : α → β} (hf : measurable f) {p : β → Prop} (hp : measurable_set {x | p x}) :
  (∀ᵐ y ∂ (map f μ), p y) ↔ ∀ᵐ x ∂ μ, p (f x) :=
mem_ae_map_iff hf hp

lemma ae_of_ae_map {f : α → β} (hf : measurable f) {p : β → Prop} (h : ∀ᵐ y ∂ (map f μ), p y) :
  ∀ᵐ x ∂ μ, p (f x) :=
mem_ae_of_mem_ae_map hf h

lemma ae_map_mem_range {m0 : measurable_space α} (f : α → β) (hf : measurable_set (range f))
  (μ : measure α) :
  ∀ᵐ x ∂(map f μ), x ∈ range f :=
begin
  by_cases h : measurable f,
  { change range f ∈ (map f μ).ae,
    rw mem_ae_map_iff h hf,
    apply eventually_of_forall,
    exact mem_range_self },
  { simp [map_of_not_measurable h] }
end

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

lemma ae_restrict_iff' {s : set α} {p : α → Prop} (hs : measurable_set s) :
  (∀ᵐ x ∂(μ.restrict s), p x) ↔ ∀ᵐ x ∂μ, x ∈ s → p x :=
begin
  simp only [ae_iff, ← compl_set_of, restrict_apply_eq_zero' hs],
  congr' with x, simp [and_comm]
end

lemma ae_restrict_mem {s : set α} (hs : measurable_set s) :
  ∀ᵐ x ∂(μ.restrict s), x ∈ s :=
(ae_restrict_iff' hs).2 (filter.eventually_of_forall (λ x, id))

lemma ae_restrict_of_ae {s : set α} {p : α → Prop} (h : ∀ᵐ x ∂μ, p x) :
  (∀ᵐ x ∂(μ.restrict s), p x) :=
eventually.filter_mono (ae_mono measure.restrict_le_self) h

lemma ae_restrict_of_ae_restrict_of_subset {s t : set α} {p : α → Prop} (hst : s ⊆ t)
  (h : ∀ᵐ x ∂(μ.restrict t), p x) :
  (∀ᵐ x ∂(μ.restrict s), p x) :=
h.filter_mono (ae_mono $ measure.restrict_mono hst (le_refl μ))

lemma ae_of_ae_restrict_of_ae_restrict_compl {t : set α} {p : α → Prop}
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

lemma ae_smul_measure {p : α → Prop} (h : ∀ᵐ x ∂μ, p x) (c : ℝ≥0∞) : ∀ᵐ x ∂(c • μ), p x :=
ae_iff.2 $ by rw [smul_apply, ae_iff.1 h, mul_zero]

lemma ae_smul_measure_iff {p : α → Prop} {c : ℝ≥0∞} (hc : c ≠ 0) :
  (∀ᵐ x ∂(c • μ), p x) ↔ ∀ᵐ x ∂μ, p x :=
by simp [ae_iff, hc]

lemma ae_add_measure_iff {p : α → Prop} {ν} : (∀ᵐ x ∂μ + ν, p x) ↔ (∀ᵐ x ∂μ, p x) ∧ ∀ᵐ x ∂ν, p x :=
add_eq_zero_iff

lemma ae_eq_comp' {ν : measure β} {f : α → β} {g g' : β → δ} (hf : measurable f)
  (h : g =ᵐ[ν] g') (h2 : map f μ ≪ ν) : g ∘ f =ᵐ[μ] g' ∘ f :=
(quasi_measure_preserving.mk hf h2).ae_eq h

lemma ae_eq_comp {f : α → β} {g g' : β → δ} (hf : measurable f)
  (h : g =ᵐ[measure.map f μ] g') : g ∘ f =ᵐ[μ] g' ∘ f :=
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

lemma is_finite_measure_of_le (μ : measure α) [is_finite_measure μ] (h : ν ≤ μ) :
  is_finite_measure ν :=
{ measure_univ_lt_top := lt_of_le_of_lt (h set.univ measurable_set.univ) (measure_lt_top _ _) }

@[instance] lemma measure.is_finite_measure_map {m : measurable_space α}
  (μ : measure α) [is_finite_measure μ] (f : α → β) :
  is_finite_measure (map f μ) :=
begin
  by_cases hf : measurable f,
  { constructor, rw map_apply hf measurable_set.univ, exact measure_lt_top μ _ },
  { rw map_of_not_measurable hf, exact measure_theory.is_finite_measure_zero }
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

@[priority 100]
instance is_probability_measure.to_is_finite_measure (μ : measure α) [is_probability_measure μ] :
  is_finite_measure μ :=
⟨by simp only [measure_univ, ennreal.one_lt_top]⟩

lemma is_probability_measure.ne_zero (μ : measure α) [is_probability_measure μ] : μ ≠ 0 :=
mt measure_univ_eq_zero.2 $ by simp [measure_univ]

omit m0

instance measure.dirac.is_probability_measure [measurable_space α] {x : α} :
  is_probability_measure (dirac x) :=
⟨dirac_apply_of_mem $ mem_univ x⟩

lemma prob_add_prob_compl [is_probability_measure μ]
  (h : measurable_set s) : μ s + μ sᶜ = 1 :=
(measure_add_measure_compl h).trans measure_univ

lemma prob_le_one [is_probability_measure μ] : μ s ≤ 1 :=
(measure_mono $ set.subset_univ _).trans_eq measure_univ

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
by simp only [← Iic_diff_right, diff_ae_eq_self,
  measure_mono_null (set.inter_subset_right _ _) (measure_singleton a)]

lemma Ioi_ae_eq_Ici : Ioi a =ᵐ[μ] Ici a :=
@Iio_ae_eq_Iic (order_dual α) ‹_› ‹_› _ _ _

lemma Ioo_ae_eq_Ioc : Ioo a b =ᵐ[μ] Ioc a b :=
(ae_eq_refl _).inter Iio_ae_eq_Iic

lemma Ioc_ae_eq_Icc : Ioc a b =ᵐ[μ] Icc a b :=
Ioi_ae_eq_Ici.inter (ae_eq_refl _)

lemma Ioo_ae_eq_Ico : Ioo a b =ᵐ[μ] Ico a b :=
Ioi_ae_eq_Ici.inter (ae_eq_refl _)

lemma Ioo_ae_eq_Icc : Ioo a b =ᵐ[μ] Icc a b :=
Ioi_ae_eq_Ici.inter Iio_ae_eq_Iic

lemma Ico_ae_eq_Icc : Ico a b =ᵐ[μ] Icc a b :=
(ae_eq_refl _).inter Iio_ae_eq_Iic

lemma Ico_ae_eq_Ioc : Ico a b =ᵐ[μ] Ioc a b :=
Ioo_ae_eq_Ico.symm.trans Ioo_ae_eq_Ioc

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
Equivalently, it is eventually finite at `s` in `f.lift' powerset`. -/
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
  spanning := eq_univ_of_subset (Union_subset_Union $ λ n, subset_to_measurable _ _)
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

lemma ae_of_forall_measure_lt_top_ae_restrict {μ : measure α} [sigma_finite μ] (P : α → Prop)
  (h : ∀ s, measurable_set s → μ s < ∞ → ∀ᵐ x ∂(μ.restrict s), P x) :
  ∀ᵐ x ∂μ, P x :=
begin
  have : ∀ n, ∀ᵐ x ∂μ, x ∈ spanning_sets μ n → P x,
  { assume n,
    have := h (spanning_sets μ n) (measurable_spanning_sets _ _) (measure_spanning_sets_lt_top _ _),
    rwa ae_restrict_iff' (measurable_spanning_sets _ _) at this },
  filter_upwards [ae_all_iff.2 this],
  assume x hx,
  exact hx _ (mem_spanning_sets_index _ _),
end

omit m0

namespace measure

lemma supr_restrict_spanning_sets [sigma_finite μ] (hs : measurable_set s) :
  (⨆ i, μ.restrict (spanning_sets μ i) s) = μ s :=
begin
  convert (restrict_Union_apply_eq_supr (measurable_spanning_sets μ) _ hs).symm,
  { simp [Union_spanning_sets] },
  { exact directed_of_sup (monotone_spanning_sets μ) }
end

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
  haveI : encodable ι := fintype.encodable ι,
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

lemma sigma_finite.of_map (μ : measure α) {f : α → β} (hf : measurable f)
  (h : sigma_finite (map f μ)) :
  sigma_finite μ :=
⟨⟨⟨λ n, f ⁻¹' (spanning_sets (map f μ) n),
   λ n, trivial,
   λ n, by simp only [← map_apply hf, measurable_spanning_sets, measure_spanning_sets_lt_top],
   by rw [← preimage_Union, Union_spanning_sets, preimage_univ]⟩⟩⟩

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
  simp only [ennreal.coe_ne_top, ennreal.coe_of_nnreal_hom, ne.def, not_false_iff],
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
  [topological_space.second_countable_topology α] [is_locally_finite_measure μ] :
  sigma_finite μ :=
begin
  choose s hsx hsμ using μ.finite_at_nhds,
  rcases topological_space.countable_cover_nhds hsx with ⟨t, htc, htU⟩,
  refine measure.sigma_finite_of_countable (htc.image s) (ball_image_iff.2 $ λ x hx, hsμ x) _,
  rwa sUnion_image
end

/-- If a set has zero measure in a neighborhood of each of its points, then it has zero measure
in a second-countable space. -/
lemma null_of_locally_null [topological_space α] [topological_space.second_countable_topology α]
  (s : set α) (hs : ∀ x ∈ s, ∃ u ∈ 𝓝[s] x, μ (s ∩ u) = 0) :
  μ s = 0 :=
begin
  choose! u hu using hs,
  obtain ⟨t, ts, t_count, ht⟩ : ∃ t ⊆ s, t.countable ∧ s ⊆ ⋃ x ∈ t, u x :=
    topological_space.countable_cover_nhds_within (λ x hx, (hu x hx).1),
  replace ht : s ⊆ ⋃ x ∈ t, s ∩ u x,
    by { rw ← inter_bUnion, exact subset_inter (subset.refl _) ht },
  apply measure_mono_null ht,
  exact (measure_bUnion_null_iff t_count).2 (λ x hx, (hu x (ts hx)).2),
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

protected lemma eventually (h : μ.finite_at_filter f) : ∀ᶠ s in f.lift' powerset, μ s < ∞ :=
(eventually_lift'_powerset' $ λ s t hst ht, (measure_mono hst).trans_lt ht).2 h

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

/-! ### Subtraction of measures -/

/-- The measure `μ - ν` is defined to be the least measure `τ` such that `μ ≤ τ + ν`.
It is the equivalent of `(μ - ν) ⊔ 0` if `μ` and `ν` were signed measures.
Compare with `ennreal.has_sub`.
Specifically, note that if you have `α = {1,2}`, and  `μ {1} = 2`, `μ {2} = 0`, and
`ν {2} = 2`, `ν {1} = 0`, then `(μ - ν) {1, 2} = 2`. However, if `μ ≤ ν`, and
`ν univ ≠ ∞`, then `(μ - ν) + ν = μ`. -/
noncomputable instance has_sub {α : Type*} [measurable_space α] : has_sub (measure α) :=
⟨λ μ ν, Inf {τ | μ ≤ τ + ν} ⟩

section measure_sub

lemma sub_def : μ - ν = Inf {d | μ ≤ d + ν} := rfl

lemma sub_eq_zero_of_le (h : μ ≤ ν) : μ - ν = 0 :=
begin
  rw [← nonpos_iff_eq_zero', measure.sub_def],
  apply @Inf_le (measure α) _ _,
  simp [h],
end

/-- This application lemma only works in special circumstances. Given knowledge of
when `μ ≤ ν` and `ν ≤ μ`, a more general application lemma can be written. -/
lemma sub_apply [is_finite_measure ν] (h₁ : measurable_set s) (h₂ : ν ≤ μ) :
  (μ - ν) s = μ s - ν s :=
begin
  -- We begin by defining `measure_sub`, which will be equal to `(μ - ν)`.
  let measure_sub : measure α := @measure_theory.measure.of_measurable α _
    (λ (t : set α) (h_t_measurable_set : measurable_set t), (μ t - ν t))
    begin
      simp
    end
    begin
      intros g h_meas h_disj, simp only, rw ennreal.tsum_sub,
      repeat { rw ← measure_theory.measure_Union h_disj h_meas },
      exacts [measure_theory.measure_ne_top _ _, λ i, h₂ _ (h_meas _)]
    end,
  -- Now, we demonstrate `μ - ν = measure_sub`, and apply it.
  begin
    have h_measure_sub_add : (ν + measure_sub = μ),
    { ext t h_t_measurable_set,
      simp only [pi.add_apply, coe_add],
      rw [measure_theory.measure.of_measurable_apply _ h_t_measurable_set, add_comm,
        tsub_add_cancel_of_le (h₂ t h_t_measurable_set)] },
    have h_measure_sub_eq : (μ - ν) = measure_sub,
    { rw measure_theory.measure.sub_def, apply le_antisymm,
      { apply @Inf_le (measure α) measure.complete_semilattice_Inf,
        simp [le_refl, add_comm, h_measure_sub_add] },
      apply @le_Inf (measure α) measure.complete_semilattice_Inf,
      intros d h_d, rw [← h_measure_sub_add, mem_set_of_eq, add_comm d] at h_d,
      apply measure.le_of_add_le_add_left h_d },
    rw h_measure_sub_eq,
    apply measure.of_measurable_apply _ h₁,
  end
end

lemma sub_add_cancel_of_le [is_finite_measure ν] (h₁ : ν ≤ μ) : μ - ν + ν = μ :=
begin
  ext s h_s_meas,
  rw [add_apply, sub_apply h_s_meas h₁, tsub_add_cancel_of_le (h₁ s h_s_meas)],
end

lemma sub_le : μ - ν ≤ μ :=
Inf_le (measure.le_add_right (le_refl _))

end measure_sub

lemma restrict_sub_eq_restrict_sub_restrict (h_meas_s : measurable_set s) :
  (μ - ν).restrict s = (μ.restrict s) - (ν.restrict s) :=
begin
  repeat {rw sub_def},
  have h_nonempty : {d | μ ≤ d + ν}.nonempty,
  { apply @set.nonempty_of_mem _ _ μ, rw mem_set_of_eq, intros t h_meas,
    exact le_self_add },
  rw restrict_Inf_eq_Inf_restrict h_nonempty h_meas_s,
  apply le_antisymm,
  { apply @Inf_le_Inf_of_forall_exists_le (measure α) _,
    intros ν' h_ν'_in, rw mem_set_of_eq at h_ν'_in, apply exists.intro (ν'.restrict s),
    split,
    { rw mem_image, apply exists.intro (ν' + (⊤ : measure_theory.measure α).restrict sᶜ),
      rw mem_set_of_eq,
      split,
      { rw [add_assoc, add_comm _ ν, ← add_assoc, measure_theory.measure.le_iff],
        intros t h_meas_t,
        have h_inter_inter_eq_inter : ∀ t' : set α , t ∩ t' ∩ t' = t ∩ t',
        { intro t', rw set.inter_eq_self_of_subset_left, apply set.inter_subset_right t t' },
        have h_meas_t_inter_s : measurable_set (t ∩ s) :=
           h_meas_t.inter h_meas_s,
        repeat { rw ← measure_inter_add_diff t h_meas_s, rw set.diff_eq },
        refine add_le_add _ _,
        { rw add_apply,
          apply le_add_right _,
          rw add_apply,
          rw ← @restrict_eq_self _ _ μ s _ h_meas_t_inter_s (set.inter_subset_right _ _),
          rw ← @restrict_eq_self _ _ ν s _ h_meas_t_inter_s (set.inter_subset_right _ _),
          apply h_ν'_in _ h_meas_t_inter_s },
        { rw add_apply,
          have h_meas_inter_compl :=
            h_meas_t.inter (measurable_set.compl h_meas_s),
          rw [restrict_apply h_meas_inter_compl, h_inter_inter_eq_inter sᶜ],
          have h_mu_le_add_top : μ ≤ ν' + ν + ⊤,
          { rw add_comm,
            have h_le_top : μ ≤ ⊤ := le_top,
            apply (λ t₂ h_meas, le_add_right (h_le_top t₂ h_meas)) },
          apply h_mu_le_add_top _ h_meas_inter_compl } },
      { ext1 t h_meas_t,
        simp [restrict_apply h_meas_t,
              restrict_apply (h_meas_t.inter h_meas_s),
              set.inter_assoc] } },
    { apply restrict_le_self } },
  { apply @Inf_le_Inf_of_forall_exists_le (measure α) _,
    intros s h_s_in, cases h_s_in with t h_t, cases h_t with h_t_in h_t_eq, subst s,
    apply exists.intro (t.restrict s), split,
    { rw [set.mem_set_of_eq, ← restrict_add],
      apply restrict_mono (set.subset.refl _) h_t_in },
    { apply le_refl _ } },
end

lemma sub_apply_eq_zero_of_restrict_le_restrict
  (h_le : μ.restrict s ≤ ν.restrict s) (h_meas_s : measurable_set s) :
  (μ - ν) s = 0 :=
begin
  rw [← restrict_apply_self _ h_meas_s, restrict_sub_eq_restrict_sub_restrict,
      sub_eq_zero_of_le],
  repeat {simp [*]},
end

instance is_finite_measure_sub [is_finite_measure μ] : is_finite_measure (μ - ν) :=
{ measure_univ_lt_top := lt_of_le_of_lt
    (measure.sub_le set.univ measurable_set.univ) (measure_lt_top _ _) }

end measure

end measure_theory

open measure_theory measure_theory.measure

namespace measurable_embedding

variables {m0 : measurable_space α} {m1 : measurable_space β} {f : α → β}
  (hf : measurable_embedding f)
include hf

theorem map_apply (μ : measure α) (s : set β) : map f μ s = μ (f ⁻¹' s) :=
begin
  refine le_antisymm _ (le_map_apply hf.measurable s),
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
  calc map f μ s ≤ map f μ t : measure_mono hst
            ... = μ (f ⁻¹' s) :
    by rw [map_apply hf.measurable htm, hft, measure_to_measurable]
end

lemma map_comap (μ : measure β) : map f (comap f μ) = μ.restrict (range f) :=
begin
  ext1 t ht,
  rw [hf.map_apply, comap_apply f hf.injective hf.measurable_set_image' _ (hf.measurable ht),
    image_preimage_eq_inter_range, restrict_apply ht]
end

lemma comap_apply (μ : measure β) (s : set α) : comap f μ s = μ (f '' s) :=
calc comap f μ s = comap f μ (f ⁻¹' (f '' s)) : by rw hf.injective.preimage_image
... = map f (comap f μ) (f '' s) : (hf.map_apply _ _).symm
... = μ (f '' s) : by rw [hf.map_comap, restrict_apply' hf.measurable_set_range,
  inter_eq_self_of_subset_left (image_subset_range _ _)]

lemma ae_map_iff {p : β → Prop} {μ : measure α} : (∀ᵐ x ∂(map f μ), p x) ↔ ∀ᵐ x ∂μ, p (f x) :=
by simp only [ae_iff, hf.map_apply, preimage_set_of_eq]

lemma restrict_map (μ : measure α) (s : set β) :
  (map f μ).restrict s = map f (μ.restrict $ f ⁻¹' s) :=
measure.ext $ λ t ht, by simp [hf.map_apply, ht, hf.measurable ht]

end measurable_embedding

section subtype

lemma comap_subtype_coe_apply {m0 : measurable_space α} {s : set α} (hs : measurable_set s)
  (μ : measure α) (t : set s) :
  comap coe μ t = μ (coe '' t) :=
(measurable_embedding.subtype_coe hs).comap_apply _ _

lemma map_comap_subtype_coe {m0 : measurable_space α} {s : set α} (hs : measurable_set s)
  (μ : measure α) : map (coe : s → α) (comap coe μ) = μ.restrict s :=
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
  map (coe : s → α) volume = restrict volume s :=
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
protected theorem map_apply (f : α ≃ᵐ β) (s : set β) : map f μ s = μ (f ⁻¹' s) :=
f.measurable_embedding.map_apply _ _

@[simp] lemma map_symm_map (e : α ≃ᵐ β) : map e.symm (map e μ) = μ :=
by simp [map_map e.symm.measurable e.measurable]

@[simp] lemma map_map_symm (e : α ≃ᵐ β) : map e (map e.symm ν) = ν :=
by simp [map_map e.measurable e.symm.measurable]

lemma map_measurable_equiv_injective (e : α ≃ᵐ β) : injective (map e) :=
by { intros μ₁ μ₂ hμ, apply_fun map e.symm at hμ, simpa [map_symm_map e] using hμ }

lemma map_apply_eq_iff_map_symm_apply_eq (e : α ≃ᵐ β) : map e μ = ν ↔ map e.symm ν = μ :=
by rw [← (map_measurable_equiv_injective e).eq_iff, map_map_symm, eq_comm]

lemma restrict_map (e : α ≃ᵐ β) (s : set β) : (map e μ).restrict s = map e (μ.restrict $ e ⁻¹' s) :=
e.measurable_embedding.restrict_map _ _

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

lemma ae_eq_of_ae_eq_trim {E} {hm : m ≤ m0} {f₁ f₂ : α → E}
  (h12 : f₁ =ᶠ[@measure.ae α m (μ.trim hm)] f₂) :
  f₁ =ᵐ[μ] f₂ :=
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

open_locale measure_theory

/-!
# Almost everywhere measurable functions

A function is almost everywhere measurable if it coincides almost everywhere with a measurable
function. This property, called `ae_measurable f μ`, is defined in the file `measure_space_def`.
We discuss several of its properties that are analogous to properties of measurable functions.
-/

section
open measure_theory

variables [measurable_space α] [measurable_space β]
{f g : α → β} {μ ν : measure α}

@[nontriviality, measurability]
lemma subsingleton.ae_measurable [subsingleton α] : ae_measurable f μ :=
subsingleton.measurable.ae_measurable

@[nontriviality, measurability]
lemma ae_measurable_of_subsingleton_codomain [subsingleton β] : ae_measurable f μ :=
(measurable_of_subsingleton_codomain f).ae_measurable

@[simp, measurability] lemma ae_measurable_zero_measure : ae_measurable f (0 : measure α) :=
begin
  nontriviality α, inhabit α,
  exact ⟨λ x, f (default α), measurable_const, rfl⟩
end

namespace ae_measurable

lemma mono_measure (h : ae_measurable f μ) (h' : ν ≤ μ) : ae_measurable f ν :=
⟨h.mk f, h.measurable_mk, eventually.filter_mono (ae_mono h') h.ae_eq_mk⟩

lemma mono_set {s t} (h : s ⊆ t) (ht : ae_measurable f (μ.restrict t)) :
  ae_measurable f (μ.restrict s) :=
ht.mono_measure (restrict_mono h le_rfl)

protected lemma mono' (h : ae_measurable f μ) (h' : ν ≪ μ) : ae_measurable f ν :=
⟨h.mk f, h.measurable_mk, h' h.ae_eq_mk⟩

lemma ae_mem_imp_eq_mk {s} (h : ae_measurable f (μ.restrict s)) :
  ∀ᵐ x ∂μ, x ∈ s → f x = h.mk f x :=
ae_imp_of_ae_restrict h.ae_eq_mk

lemma ae_inf_principal_eq_mk {s} (h : ae_measurable f (μ.restrict s)) :
  f =ᶠ[μ.ae ⊓ 𝓟 s] h.mk f :=
le_ae_restrict h.ae_eq_mk

@[measurability]
lemma sum_measure [encodable ι] {μ : ι → measure α} (h : ∀ i, ae_measurable f (μ i)) :
  ae_measurable f (sum μ) :=
begin
  nontriviality β, inhabit β,
  set s : ι → set α := λ i, to_measurable (μ i) {x | f x ≠ (h i).mk f x},
  have hsμ : ∀ i, μ i (s i) = 0,
  { intro i, rw measure_to_measurable, exact (h i).ae_eq_mk },
  have hsm : measurable_set (⋂ i, s i),
    from measurable_set.Inter (λ i, measurable_set_to_measurable _ _),
  have hs : ∀ i x, x ∉ s i → f x = (h i).mk f x,
  { intros i x hx, contrapose! hx, exact subset_to_measurable _ _ hx },
  set g : α → β := (⋂ i, s i).piecewise (const α (default β)) f,
  refine ⟨g, measurable_of_restrict_of_restrict_compl hsm _ _, ae_sum_iff.mpr $ λ i, _⟩,
  { rw [restrict_piecewise], simp only [set.restrict, const], exact measurable_const },
  { rw [restrict_piecewise_compl, compl_Inter],
    intros t ht,
    refine ⟨⋃ i, ((h i).mk f ⁻¹' t) ∩ (s i)ᶜ, measurable_set.Union $
      λ i, (measurable_mk _ ht).inter (measurable_set_to_measurable _ _).compl, _⟩,
    ext ⟨x, hx⟩,
    simp only [mem_preimage, mem_Union, subtype.coe_mk, set.restrict, mem_inter_eq,
      mem_compl_iff] at hx ⊢,
    split,
    { rintro ⟨i, hxt, hxs⟩, rwa hs _ _ hxs },
    { rcases hx with ⟨i, hi⟩, rw hs _ _ hi, exact λ h, ⟨i, h, hi⟩ } },
  { refine measure_mono_null (λ x (hx : f x ≠ g x), _) (hsμ i),
    contrapose! hx, refine (piecewise_eq_of_not_mem _ _ _ _).symm,
    exact λ h, hx (mem_Inter.1 h i) }
end

@[simp] lemma _root_.ae_measurable_sum_measure_iff [encodable ι] {μ : ι → measure α} :
  ae_measurable f (sum μ) ↔ ∀ i, ae_measurable f (μ i) :=
⟨λ h i, h.mono_measure (le_sum _ _), sum_measure⟩

@[simp] lemma _root_.ae_measurable_add_measure_iff :
  ae_measurable f (μ + ν) ↔ ae_measurable f μ ∧ ae_measurable f ν :=
by { rw [← sum_cond, ae_measurable_sum_measure_iff, bool.forall_bool, and.comm], refl }

@[measurability]
lemma add_measure {f : α → β} (hμ : ae_measurable f μ) (hν : ae_measurable f ν) :
  ae_measurable f (μ + ν) :=
ae_measurable_add_measure_iff.2 ⟨hμ, hν⟩

@[measurability]
protected lemma Union [encodable ι] {s : ι → set α} (h : ∀ i, ae_measurable f (μ.restrict (s i))) :
  ae_measurable f (μ.restrict (⋃ i, s i)) :=
(sum_measure h).mono_measure $ restrict_Union_le

@[simp] lemma _root_.ae_measurable_Union_iff [encodable ι] {s : ι → set α} :
  ae_measurable f (μ.restrict (⋃ i, s i)) ↔ ∀ i, ae_measurable f (μ.restrict (s i)) :=
⟨λ h i, h.mono_measure $ restrict_mono (subset_Union _ _) le_rfl, ae_measurable.Union⟩

@[measurability]
lemma smul_measure (h : ae_measurable f μ) (c : ℝ≥0∞) :
  ae_measurable f (c • μ) :=
⟨h.mk f, h.measurable_mk, ae_smul_measure h.ae_eq_mk c⟩

lemma comp_measurable [measurable_space δ] {f : α → δ} {g : δ → β}
  (hg : ae_measurable g (map f μ)) (hf : measurable f) : ae_measurable (g ∘ f) μ :=
⟨hg.mk g ∘ f, hg.measurable_mk.comp hf, ae_eq_comp hf hg.ae_eq_mk⟩

lemma comp_measurable' {δ} [measurable_space δ] {ν : measure δ} {f : α → δ} {g : δ → β}
  (hg : ae_measurable g ν) (hf : measurable f) (h : map f μ ≪ ν) : ae_measurable (g ∘ f) μ :=
(hg.mono' h).comp_measurable hf

@[measurability]
lemma prod_mk {γ : Type*} [measurable_space γ] {f : α → β} {g : α → γ}
  (hf : ae_measurable f μ) (hg : ae_measurable g μ) : ae_measurable (λ x, (f x, g x)) μ :=
⟨λ a, (hf.mk f a, hg.mk g a), hf.measurable_mk.prod_mk hg.measurable_mk,
  eventually_eq.prod_mk hf.ae_eq_mk hg.ae_eq_mk⟩

lemma subtype_mk (h : ae_measurable f μ) {s : set β} {hfs : ∀ x, f x ∈ s} (hs : measurable_set s) :
  ae_measurable (cod_restrict f s hfs) μ :=
begin
  nontriviality α, inhabit α,
  rcases h with ⟨g, hgm, hg⟩,
  rcases hs.exists_measurable_proj ⟨f (default α), hfs _⟩ with ⟨π, hπm, hπ⟩,
  refine ⟨π ∘ g, hπm.comp hgm, hg.mono $ λ x hx, _⟩,
  rw [comp_apply, ← hx, ← coe_cod_restrict_apply f s hfs, hπ]
end

protected lemma null_measurable (h : ae_measurable f μ) : null_measurable f μ :=
let ⟨g, hgm, hg⟩ := h in hgm.null_measurable.congr hg.symm

end ae_measurable

lemma ae_measurable_iff_measurable [μ.is_complete] :
  ae_measurable f μ ↔ measurable f :=
⟨λ h, h.null_measurable.measurable_of_complete, λ h, h.ae_measurable⟩

lemma measurable_embedding.ae_measurable_map_iff [measurable_space γ] {f : α → β}
  (hf : measurable_embedding f) {μ : measure α} {g : β → γ} :
  ae_measurable g (map f μ) ↔ ae_measurable (g ∘ f) μ :=
begin
  refine ⟨λ H, H.comp_measurable hf.measurable, _⟩,
  rintro ⟨g₁, hgm₁, heq⟩,
  rcases hf.exists_measurable_extend hgm₁ (λ x, ⟨g x⟩) with ⟨g₂, hgm₂, rfl⟩,
  exact ⟨g₂, hgm₂, hf.ae_map_iff.2 heq⟩
end

lemma measurable_embedding.ae_measurable_comp_iff [measurable_space γ] {g : β → γ}
  (hg : measurable_embedding g) {μ : measure α} {f : α → β} :
  ae_measurable (g ∘ f) μ ↔ ae_measurable f μ :=
begin
  refine ⟨λ H, _, hg.measurable.comp_ae_measurable⟩,
  suffices : ae_measurable ((range_splitting g ∘ range_factorization g) ∘ f) μ,
    by rwa [(right_inverse_range_splitting hg.injective).comp_eq_id] at this,
  exact hg.measurable_range_splitting.comp_ae_measurable (H.subtype_mk hg.measurable_set_range)
end

lemma ae_measurable_restrict_iff_comap_subtype {s : set α} (hs : measurable_set s)
  {μ : measure α} {f : α → β} :
  ae_measurable f (μ.restrict s) ↔ ae_measurable (f ∘ coe : s → β) (comap coe μ) :=
by rw [← map_comap_subtype_coe hs, (measurable_embedding.subtype_coe hs).ae_measurable_map_iff]

@[simp, to_additive] lemma ae_measurable_one [has_one β] : ae_measurable (λ a : α, (1 : β)) μ :=
measurable_one.ae_measurable

@[simp] lemma ae_measurable_smul_measure_iff {c : ℝ≥0∞} (hc : c ≠ 0) :
  ae_measurable f (c • μ) ↔ ae_measurable f μ :=
⟨λ h, ⟨h.mk f, h.measurable_mk, (ae_smul_measure_iff hc).1 h.ae_eq_mk⟩,
  λ h, ⟨h.mk f, h.measurable_mk, (ae_smul_measure_iff hc).2 h.ae_eq_mk⟩⟩

lemma ae_measurable_of_ae_measurable_trim {α} {m m0 : measurable_space α}
  {μ : measure α} (hm : m ≤ m0) {f : α → β} (hf : ae_measurable f (μ.trim hm)) :
  ae_measurable f μ :=
⟨hf.mk f, measurable.mono hf.measurable_mk hm le_rfl, ae_eq_of_ae_eq_trim hf.ae_eq_mk⟩

lemma ae_measurable_restrict_of_measurable_subtype {s : set α}
  (hs : measurable_set s) (hf : measurable (λ x : s, f x)) : ae_measurable f (μ.restrict s) :=
(ae_measurable_restrict_iff_comap_subtype hs).2 hf.ae_measurable

lemma ae_measurable_map_equiv_iff [measurable_space γ] (e : α ≃ᵐ β) {f : β → γ} :
  ae_measurable f (map e μ) ↔ ae_measurable (f ∘ e) μ :=
e.measurable_embedding.ae_measurable_map_iff

end

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

@[priority 100] -- see Note [lower instance priority]
instance {μ : measure α} [is_locally_finite_measure μ] : is_finite_measure_on_compacts μ :=
⟨λ s hs, hs.measure_lt_top_of_nhds_within $ λ x hx, μ.finite_at_nhds_within _ _⟩

lemma measure_zero_of_nhds_within (hs : is_compact s) :
  (∀ a ∈ s, ∃ t ∈ 𝓝[s] a, μ t = 0) → μ s = 0 :=
by simpa only [← compl_mem_ae_iff] using hs.compl_mem_sets_of_nhds_within

end is_compact

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
  spanning := eq_univ_of_subset (Union_subset_Union $ λ n,
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

lemma ae_measurable.restrict [measurable_space β] (hfm : ae_measurable f μ) {s} :
  ae_measurable f (μ.restrict s) :=
⟨ae_measurable.mk f hfm, hfm.measurable_mk, ae_restrict_of_ae hfm.ae_eq_mk⟩

variables [has_zero β]

lemma indicator_ae_eq_restrict (hs : measurable_set s) : indicator s f =ᵐ[μ.restrict s] f :=
piecewise_ae_eq_restrict hs

lemma indicator_ae_eq_restrict_compl (hs : measurable_set s) : indicator s f =ᵐ[μ.restrict sᶜ] 0 :=
piecewise_ae_eq_restrict_compl hs

lemma indicator_ae_eq_of_ae_eq_set (hst : s =ᵐ[μ] t) : s.indicator f =ᵐ[μ] t.indicator f :=
piecewise_ae_eq_of_ae_eq_set hst

variables [measurable_space β]

lemma ae_measurable_indicator_iff {s} (hs : measurable_set s) :
  ae_measurable (indicator s f) μ ↔ ae_measurable f (μ.restrict s)  :=
begin
  split,
  { assume h,
    exact (h.mono_measure measure.restrict_le_self).congr (indicator_ae_eq_restrict hs) },
  { assume h,
    refine ⟨indicator s (h.mk f), h.measurable_mk.indicator hs, _⟩,
    have A : s.indicator f =ᵐ[μ.restrict s] s.indicator (ae_measurable.mk f h) :=
      (indicator_ae_eq_restrict hs).trans (h.ae_eq_mk.trans $ (indicator_ae_eq_restrict hs).symm),
    have B : s.indicator f =ᵐ[μ.restrict sᶜ] s.indicator (ae_measurable.mk f h) :=
      (indicator_ae_eq_restrict_compl hs).trans (indicator_ae_eq_restrict_compl hs).symm,
    exact ae_of_ae_restrict_of_ae_restrict_compl A B },
end

@[measurability]
lemma ae_measurable.indicator (hfm : ae_measurable f μ) {s} (hs : measurable_set s) :
  ae_measurable (s.indicator f) μ :=
(ae_measurable_indicator_iff hs).mpr hfm.restrict

end indicator_function
