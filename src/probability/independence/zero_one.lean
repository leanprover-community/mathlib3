/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import probability.independence.basic

/-!
# Kolmogorov's 0-1 law

Let `s : ι → measurable_space Ω` be an independent sequence of sub-σ-algebras. Then any set which
is measurable with respect to the tail σ-algebra `limsup s at_top` has probability 0 or 1.

## Main statements

* `measure_zero_or_one_of_measurable_set_limsup_at_top`: Kolmogorov's 0-1 law. Any set which is
  measurable with respect to the tail σ-algebra `limsup s at_top` of an independent sequence of
  σ-algebras `s` has probability 0 or 1.
-/

open measure_theory measurable_space
open_locale measure_theory ennreal

namespace probability_theory

variables {Ω ι : Type*} {m m0 : measurable_space Ω} {μ : measure Ω}

lemma measure_eq_zero_or_one_or_top_of_indep_set_self {t : set Ω} (h_indep : indep_set t t μ) :
  μ t = 0 ∨ μ t = 1 ∨ μ t = ∞ :=
begin
  specialize h_indep t t (measurable_set_generate_from (set.mem_singleton t))
    (measurable_set_generate_from (set.mem_singleton t)),
  by_cases h0 : μ t = 0,
  { exact or.inl h0, },
  by_cases h_top : μ t = ∞,
  { exact or.inr (or.inr h_top), },
  rw [← one_mul (μ (t ∩ t)), set.inter_self, ennreal.mul_eq_mul_right h0 h_top] at h_indep,
  exact or.inr (or.inl h_indep.symm),
end

lemma measure_eq_zero_or_one_of_indep_set_self [is_finite_measure μ] {t : set Ω}
  (h_indep : indep_set t t μ) :
  μ t = 0 ∨ μ t = 1 :=
begin
  have h_0_1_top := measure_eq_zero_or_one_or_top_of_indep_set_self h_indep,
  simpa [measure_ne_top μ] using h_0_1_top,
end

variables [is_probability_measure μ] {s : ι → measurable_space Ω}

open filter

lemma indep_bsupr_compl (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ) (t : set ι) :
  indep (⨆ n ∈ t, s n) (⨆ n ∈ tᶜ, s n) μ :=
indep_supr_of_disjoint h_le h_indep disjoint_compl_right

section abstract
variables {α : Type*} {p : set ι → Prop} {f : filter ι} {ns : α → set ι}

/-! We prove a version of Kolmogorov's 0-1 law for the σ-algebra `limsup s f` where `f` is a filter
for which we can define the following two functions:
* `p : set ι → Prop` such that for a set `t`, `p t → tᶜ ∈ f`,
* `ns : α → set ι` a directed sequence of sets which all verify `p` and such that
  `⋃ a, ns a = set.univ`.

For the example of `f = at_top`, we can take `p = bdd_above` and `ns : ι → set ι := λ i, set.Iic i`.
-/

lemma indep_bsupr_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ)
  (hf : ∀ t, p t → tᶜ ∈ f) {t : set ι} (ht : p t) :
  indep (⨆ n ∈ t, s n) (limsup s f) μ :=
begin
  refine indep_of_indep_of_le_right (indep_bsupr_compl h_le h_indep t) _,
  refine Limsup_le_of_le (by is_bounded_default) _,
  simp only [set.mem_compl_iff, eventually_map],
  exact eventually_of_mem (hf t ht) le_supr₂,
end

lemma indep_supr_directed_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ)
  (hf : ∀ t, p t → tᶜ ∈ f) (hns : directed (≤) ns) (hnsp : ∀ a, p (ns a)) :
  indep (⨆ a, ⨆ n ∈ (ns a), s n) (limsup s f) μ :=
begin
  refine indep_supr_of_directed_le _ _ _ _,
  { exact λ a, indep_bsupr_limsup h_le h_indep hf (hnsp a), },
  { exact λ a, supr₂_le (λ n hn, h_le n), },
  { exact limsup_le_supr.trans (supr_le h_le), },
  { intros a b,
    obtain ⟨c, hc⟩ := hns a b,
    refine ⟨c, _, _⟩; refine supr_mono (λ n, supr_mono' (λ hn, ⟨_, le_rfl⟩)),
    { exact hc.1 hn, },
    { exact hc.2 hn, }, },
end

lemma indep_supr_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ) (hf : ∀ t, p t → tᶜ ∈ f)
  (hns : directed (≤) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
  indep (⨆ n, s n) (limsup s f) μ :=
begin
  suffices : (⨆ a, ⨆ n ∈ (ns a), s n) = ⨆ n, s n,
  { rw ← this,
    exact indep_supr_directed_limsup h_le h_indep hf hns hnsp, },
  rw supr_comm,
  refine supr_congr (λ n, _),
  have : (⨆ (i : α) (H : n ∈ ns i), s n) = (⨆ (h : ∃ i, n ∈ ns i), s n), by rw supr_exists,
  haveI : nonempty (∃ (i : α), n ∈ ns i) := ⟨hns_univ n⟩,
  rw [this, supr_const],
end

lemma indep_limsup_self (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ) (hf : ∀ t, p t → tᶜ ∈ f)
  (hns : directed (≤) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
  indep (limsup s f) (limsup s f) μ :=
indep_of_indep_of_le_left (indep_supr_limsup h_le h_indep hf hns hnsp hns_univ) limsup_le_supr

theorem measure_zero_or_one_of_measurable_set_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ)
  (hf : ∀ t, p t → tᶜ ∈ f) (hns : directed (≤) ns) (hnsp : ∀ a, p (ns a))
  (hns_univ : ∀ n, ∃ a, n ∈ ns a) {t : set Ω} (ht_tail : measurable_set[limsup s f] t) :
  μ t = 0 ∨ μ t = 1 :=
measure_eq_zero_or_one_of_indep_set_self
  ((indep_limsup_self h_le h_indep hf hns hnsp hns_univ).indep_set_of_measurable_set
    ht_tail ht_tail)

end abstract

section at_top
variables [semilattice_sup ι] [no_max_order ι] [nonempty ι]

lemma indep_limsup_at_top_self (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ) :
  indep (limsup s at_top) (limsup s at_top) μ :=
begin
  let ns : ι → set ι := set.Iic,
  have hnsp : ∀ i, bdd_above (ns i) := λ i, bdd_above_Iic,
  refine indep_limsup_self h_le h_indep _ _ hnsp _,
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

/-- **Kolmogorov's 0-1 law** : any event in the tail σ-algebra of an independent sequence of
sub-σ-algebras has probability 0 or 1.
The tail σ-algebra `limsup s at_top` is the same as `⋂ n, ⋃ i ≥ n, s i`. -/
theorem measure_zero_or_one_of_measurable_set_limsup_at_top (h_le : ∀ n, s n ≤ m0)
  (h_indep : Indep s μ) {t : set Ω} (ht_tail : measurable_set[limsup s at_top] t) :
  μ t = 0 ∨ μ t = 1 :=
measure_eq_zero_or_one_of_indep_set_self
  ((indep_limsup_at_top_self h_le h_indep).indep_set_of_measurable_set ht_tail ht_tail)

end at_top

section at_bot
variables [semilattice_inf ι] [no_min_order ι] [nonempty ι]

lemma indep_limsup_at_bot_self (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ) :
  indep (limsup s at_bot) (limsup s at_bot) μ :=
begin
  let ns : ι → set ι := set.Ici,
  have hnsp : ∀ i, bdd_below (ns i) := λ i, bdd_below_Ici,
  refine indep_limsup_self h_le h_indep _ _ hnsp _,
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

/-- **Kolmogorov's 0-1 law** : any event in the tail σ-algebra of an independent sequence of
sub-σ-algebras has probability 0 or 1. -/
theorem measure_zero_or_one_of_measurable_set_limsup_at_bot (h_le : ∀ n, s n ≤ m0)
  (h_indep : Indep s μ) {t : set Ω} (ht_tail : measurable_set[limsup s at_bot] t) :
  μ t = 0 ∨ μ t = 1 :=
measure_eq_zero_or_one_of_indep_set_self
  ((indep_limsup_at_bot_self h_le h_indep).indep_set_of_measurable_set ht_tail ht_tail)

end at_bot

end probability_theory
