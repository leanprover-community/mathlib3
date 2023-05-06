/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import probability.independence.independence

/-!
# Zero One Law

## Main definitions

* `foo_bar`

## Main statements

* `measure_zero_or_one_of_measurable_set_limsup_at_top`: Kolmogorov's 0-1 law. Any set which is
  measurable with respect to the tail σ-algebra `limsup s at_top` of an independent sequence of
  σ-algebras `s` has probability 0 or 1.

-/


open measure_theory measurable_space
open_locale big_operators measure_theory ennreal

namespace probability_theory



/-! ### Kolmogorov's 0-1 law

Let `s : ι → measurable_space Ω` be an independent sequence of sub-σ-algebras. Then any set which
is measurable with respect to the tail σ-algebra `limsup s at_top` has probability 0 or 1.
-/

variables {Ω α ι : Type*} [measurable_space α]
  {m m0 : measurable_space Ω} {ν : kernel α Ω} {μ : measure α} {μ' : measure Ω}

lemma measure_eq_zero_or_one_or_top_of_indep_setₖ_self {t : set Ω} (h_indep : indep_setₖ t t ν μ) :
  ∀ᵐ a ∂μ, ν a t = 0 ∨ ν a t = 1 ∨ ν a t = ∞ :=
begin
  specialize h_indep t t (measurable_set_generate_from (set.mem_singleton t))
    (measurable_set_generate_from (set.mem_singleton t)),
  filter_upwards [h_indep] with a ha,
  by_cases h0 : ν a t = 0,
  { exact or.inl h0, },
  by_cases h_top : ν a t = ∞,
  { exact or.inr (or.inr h_top), },
  rw [← one_mul (ν a (t ∩ t)), set.inter_self, ennreal.mul_eq_mul_right h0 h_top] at ha,
  exact or.inr (or.inl ha.symm),
end

lemma measure_eq_zero_or_one_or_top_of_indep_set_self {t : set Ω} (h_indep : indep_set t t μ') :
  μ' t = 0 ∨ μ' t = 1 ∨ μ' t = ∞ :=
by simpa only [ae_dirac_eq, filter.eventually_pure]
  using measure_eq_zero_or_one_or_top_of_indep_setₖ_self h_indep

lemma measure_eq_zero_or_one_of_indep_setₖ_self [∀ a, is_finite_measure (ν a)] {t : set Ω}
  (h_indep : indep_setₖ t t ν μ) :
  ∀ᵐ a ∂μ, ν a t = 0 ∨ ν a t = 1 :=
begin
  filter_upwards [measure_eq_zero_or_one_or_top_of_indep_setₖ_self h_indep] with a h_0_1_top,
  simpa [measure_ne_top (ν a)] using h_0_1_top,
end

lemma measure_eq_zero_or_one_of_indep_set_self [is_finite_measure μ'] {t : set Ω}
  (h_indep : indep_set t t μ') :
  μ' t = 0 ∨ μ' t = 1 :=
by simpa only [ae_dirac_eq, filter.eventually_pure]
  using measure_eq_zero_or_one_of_indep_setₖ_self h_indep

variables [∀ a, is_probability_measure (ν a)] {s : ι → measurable_space Ω}
  [is_probability_measure μ']

open filter

lemma indepₖ_bsupr_compl (h_le : ∀ n, s n ≤ m0) (h_indep : Indepₖ s ν μ) (t : set ι) :
  indepₖ (⨆ n ∈ t, s n) (⨆ n ∈ tᶜ, s n) ν μ :=
indepₖ_supr_of_disjoint h_le h_indep disjoint_compl_right

lemma indep_bsupr_compl (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ') (t : set ι) :
  indep (⨆ n ∈ t, s n) (⨆ n ∈ tᶜ, s n) μ' :=
indepₖ_bsupr_compl h_le h_indep t

section abstract
variables {β : Type*} {p : set ι → Prop} {f : filter ι} {ns : β → set ι}

/-! We prove a version of Kolmogorov's 0-1 law for the σ-algebra `limsup s f` where `f` is a filter
for which we can define the following two functions:
* `p : set ι → Prop` such that for a set `t`, `p t → tᶜ ∈ f`,
* `ns : α → set ι` a directed sequence of sets which all verify `p` and such that
  `⋃ a, ns a = set.univ`.

For the example of `f = at_top`, we can take `p = bdd_above` and `ns : ι → set ι := λ i, set.Iic i`.
-/

lemma indepₖ_bsupr_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : Indepₖ s ν μ)
  (hf : ∀ t, p t → tᶜ ∈ f) {t : set ι} (ht : p t) :
  indepₖ (⨆ n ∈ t, s n) (limsup s f) ν μ :=
begin
  refine indepₖ_of_indepₖ_of_le_right (indepₖ_bsupr_compl h_le h_indep t) _,
  refine Limsup_le_of_le (by is_bounded_default) _,
  simp only [set.mem_compl_iff, eventually_map],
  exact eventually_of_mem (hf t ht) le_supr₂,
end

lemma indep_bsupr_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ')
  (hf : ∀ t, p t → tᶜ ∈ f) {t : set ι} (ht : p t) :
  indep (⨆ n ∈ t, s n) (limsup s f) μ' :=
indepₖ_bsupr_limsup h_le h_indep hf ht

lemma indepₖ_supr_directed_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : Indepₖ s ν μ)
  (hf : ∀ t, p t → tᶜ ∈ f) (hns : directed (≤) ns) (hnsp : ∀ a, p (ns a)) :
  indepₖ (⨆ a, ⨆ n ∈ (ns a), s n) (limsup s f) ν μ :=
begin
  refine indepₖ_supr_of_directed_le _ _ _ _,
  { exact λ a, indepₖ_bsupr_limsup h_le h_indep hf (hnsp a), },
  { exact λ a, supr₂_le (λ n hn, h_le n), },
  { exact limsup_le_supr.trans (supr_le h_le), },
  { intros a b,
    obtain ⟨c, hc⟩ := hns a b,
    refine ⟨c, _, _⟩; refine supr_mono (λ n, supr_mono' (λ hn, ⟨_, le_rfl⟩)),
    { exact hc.1 hn, },
    { exact hc.2 hn, }, },
end

lemma indep_supr_directed_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ')
  (hf : ∀ t, p t → tᶜ ∈ f) (hns : directed (≤) ns) (hnsp : ∀ a, p (ns a)) :
  indep (⨆ a, ⨆ n ∈ (ns a), s n) (limsup s f) μ' :=
indepₖ_supr_directed_limsup h_le h_indep hf hns hnsp

lemma indepₖ_supr_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : Indepₖ s ν μ) (hf : ∀ t, p t → tᶜ ∈ f)
  (hns : directed (≤) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
  indepₖ (⨆ n, s n) (limsup s f) ν μ :=
begin
  suffices : (⨆ a, ⨆ n ∈ (ns a), s n) = ⨆ n, s n,
  { rw ← this,
    exact indepₖ_supr_directed_limsup h_le h_indep hf hns hnsp, },
  rw supr_comm,
  refine supr_congr (λ n, _),
  have : (⨆ i (H : n ∈ ns i), s n) = (⨆ (h : ∃ i, n ∈ ns i), s n), by rw supr_exists,
  haveI : nonempty (∃ i, n ∈ ns i) := ⟨hns_univ n⟩,
  rw [this, supr_const],
end

lemma indep_supr_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ') (hf : ∀ t, p t → tᶜ ∈ f)
  (hns : directed (≤) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
  indep (⨆ n, s n) (limsup s f) μ' :=
indepₖ_supr_limsup h_le h_indep hf hns hnsp hns_univ

lemma indepₖ_limsup_self (h_le : ∀ n, s n ≤ m0) (h_indep : Indepₖ s ν μ) (hf : ∀ t, p t → tᶜ ∈ f)
  (hns : directed (≤) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
  indepₖ (limsup s f) (limsup s f) ν μ :=
indepₖ_of_indepₖ_of_le_left (indepₖ_supr_limsup h_le h_indep hf hns hnsp hns_univ) limsup_le_supr

lemma indep_limsup_self (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ') (hf : ∀ t, p t → tᶜ ∈ f)
  (hns : directed (≤) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
  indep (limsup s f) (limsup s f) μ' :=
indepₖ_limsup_self h_le h_indep hf hns hnsp hns_univ

theorem measure_zero_or_one_of_measurable_set_limsup' (h_le : ∀ n, s n ≤ m0) (h_indep : Indepₖ s ν μ)
  (hf : ∀ t, p t → tᶜ ∈ f) (hns : directed (≤) ns) (hnsp : ∀ a, p (ns a))
  (hns_univ : ∀ n, ∃ a, n ∈ ns a) {t : set Ω} (ht_tail : measurable_set[limsup s f] t) :
  ∀ᵐ a ∂μ, ν a t = 0 ∨ ν a t = 1 :=
measure_eq_zero_or_one_of_indep_setₖ_self
  ((indepₖ_limsup_self h_le h_indep hf hns hnsp hns_univ).indep_setₖ_of_measurable_set
    ht_tail ht_tail)

theorem measure_zero_or_one_of_measurable_set_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ')
  (hf : ∀ t, p t → tᶜ ∈ f) (hns : directed (≤) ns) (hnsp : ∀ a, p (ns a))
  (hns_univ : ∀ n, ∃ a, n ∈ ns a) {t : set Ω} (ht_tail : measurable_set[limsup s f] t) :
  μ' t = 0 ∨ μ' t = 1 :=
by simpa only [ae_dirac_eq, filter.eventually_pure]
  using measure_zero_or_one_of_measurable_set_limsup' h_le h_indep hf hns hnsp hns_univ ht_tail

end abstract

section at_top
variables [semilattice_sup ι] [no_max_order ι] [nonempty ι]

lemma indepₖ_limsup_at_top_self (h_le : ∀ n, s n ≤ m0) (h_indep : Indepₖ s ν μ) :
  indepₖ (limsup s at_top) (limsup s at_top) ν μ :=
begin
  let ns : ι → set ι := set.Iic,
  have hnsp : ∀ i, bdd_above (ns i) := λ i, bdd_above_Iic,
  refine indepₖ_limsup_self h_le h_indep _ _ hnsp _,
  { simp only [mem_at_top_sets, ge_iff_le, set.mem_compl_iff, bdd_above, upper_bounds,
      set.nonempty],
    rintros t ⟨a, ha⟩,
    obtain ⟨b, hb⟩ : ∃ b, a < b := exists_gt a,
    refine ⟨b, λ c hc hct, _⟩,
    suffices : ∀ i ∈ t, i < c, from lt_irrefl c (this c hct),
    exact λ i hi, (ha hi).trans_lt (hb.trans_le hc), },
  { exact monotone.directed_le (λ i j hij k hki, le_trans hki hij), },
  { exact λ n, ⟨n, le_rfl⟩, },
end

lemma indep_limsup_at_top_self (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ') :
  indep (limsup s at_top) (limsup s at_top) μ' :=
indepₖ_limsup_at_top_self h_le h_indep

/-- **Kolmogorov's 0-1 law** : any event in the tail σ-algebra of an independent sequence of
sub-σ-algebras has probability 0 or 1.
The tail σ-algebra `limsup s at_top` is the same as `⋂ n, ⋃ i ≥ n, s i`. -/
theorem measure_zero_or_one_of_measurable_set_limsup_at_top' (h_le : ∀ n, s n ≤ m0)
  (h_indep : Indepₖ s ν μ) {t : set Ω} (ht_tail : measurable_set[limsup s at_top] t) :
  ∀ᵐ a ∂μ, ν a t = 0 ∨ ν a t = 1 :=
measure_eq_zero_or_one_of_indep_setₖ_self
  ((indepₖ_limsup_at_top_self h_le h_indep).indep_setₖ_of_measurable_set ht_tail ht_tail)

theorem measure_zero_or_one_of_measurable_set_limsup_at_top (h_le : ∀ n, s n ≤ m0)
  (h_indep : Indep s μ') {t : set Ω} (ht_tail : measurable_set[limsup s at_top] t) :
  μ' t = 0 ∨ μ' t = 1 :=
by simpa only [ae_dirac_eq, filter.eventually_pure]
  using measure_zero_or_one_of_measurable_set_limsup_at_top' h_le h_indep ht_tail

end at_top

section at_bot
variables [semilattice_inf ι] [no_min_order ι] [nonempty ι]

lemma indepₖ_limsup_at_bot_self (h_le : ∀ n, s n ≤ m0) (h_indep : Indepₖ s ν μ) :
  indepₖ (limsup s at_bot) (limsup s at_bot) ν μ :=
begin
  let ns : ι → set ι := set.Ici,
  have hnsp : ∀ i, bdd_below (ns i) := λ i, bdd_below_Ici,
  refine indepₖ_limsup_self h_le h_indep _ _ hnsp _,
  { simp only [mem_at_bot_sets, ge_iff_le, set.mem_compl_iff, bdd_below, lower_bounds,
      set.nonempty],
    rintros t ⟨a, ha⟩,
    obtain ⟨b, hb⟩ : ∃ b, b < a := exists_lt a,
    refine ⟨b, λ c hc hct, _⟩,
    suffices : ∀ i ∈ t, c < i, from lt_irrefl c (this c hct),
    exact λ i hi, hc.trans_lt (hb.trans_le (ha hi)), },
  { exact directed_of_inf (λ i j hij k hki, hij.trans hki), },
  { exact λ n, ⟨n, le_rfl⟩, },
end

lemma indep_limsup_at_bot_self (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ') :
  indep (limsup s at_bot) (limsup s at_bot) μ' :=
indepₖ_limsup_at_bot_self h_le h_indep

/-- **Kolmogorov's 0-1 law** : any event in the tail σ-algebra of an independent sequence of
sub-σ-algebras has probability 0 or 1. -/
theorem measure_zero_or_one_of_measurable_set_limsup_at_bot' (h_le : ∀ n, s n ≤ m0)
  (h_indep : Indepₖ s ν μ) {t : set Ω} (ht_tail : measurable_set[limsup s at_bot] t) :
  ∀ᵐ a ∂μ, ν a t = 0 ∨ ν a t = 1 :=
measure_eq_zero_or_one_of_indep_setₖ_self
  ((indepₖ_limsup_at_bot_self h_le h_indep).indep_setₖ_of_measurable_set ht_tail ht_tail)

theorem measure_zero_or_one_of_measurable_set_limsup_at_bot (h_le : ∀ n, s n ≤ m0)
  (h_indep : Indep s μ') {t : set Ω} (ht_tail : measurable_set[limsup s at_bot] t) :
  μ' t = 0 ∨ μ' t = 1 :=
by simpa only [ae_dirac_eq, filter.eventually_pure]
  using measure_zero_or_one_of_measurable_set_limsup_at_bot' h_le h_indep ht_tail

end at_bot

end probability_theory
