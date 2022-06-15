/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import probability.martingale

/-!
# Draft
-/

open_locale measure_theory big_operators ennreal
open topological_space

namespace measure_theory

section stopping

variables {α ι E : Type*} {m : measurable_space α} {μ : measure α}

section not_nat

lemma ae_restrict_Union_finset_eq (s : ι → set α) (t : finset ι) :
  (μ.restrict (⋃ i ∈ t, s i)).ae = ⨆ i ∈ t, (μ.restrict (s i)).ae :=
begin
  have : (⋃ i ∈ t, s i) = ⋃ i : t, s i,
  { ext1 x, simp only [set.mem_Union, exists_prop],
    split,
    { rintros ⟨i, hit, hixs⟩,
      exact ⟨⟨i, hit⟩, hixs⟩, },
    { rintros ⟨i, hixs⟩,
      refine ⟨i, i.prop, hixs⟩, }, },
  rw this,
  haveI : encodable t := fintype.to_encodable ↥t,
  rw ae_restrict_Union_eq,
  ext1 u,
  simp only [filter.mem_supr],
  split; intros h i,
  { exact λ hit, h ⟨i, hit⟩, },
  { exact h i i.prop, },
end

lemma ae_restrict_Union_countable_eq (s : ι → set α) {t : set ι} (ht : t.countable) :
  (μ.restrict (⋃ i ∈ t, s i)).ae = ⨆ i ∈ t, (μ.restrict (s i)).ae :=
begin
  have : (⋃ i ∈ t, s i) = ⋃ i : t, s i,
  { ext1 x, simp only [set.mem_Union, exists_prop],
    split,
    { rintros ⟨i, hit, hixs⟩,
      exact ⟨⟨i, hit⟩, hixs⟩, },
    { rintros ⟨i, hixs⟩,
      refine ⟨i, i.prop, hixs⟩, }, },
  rw this,
  haveI : encodable t := ht.to_encodable,
  rw ae_restrict_Union_eq,
  ext1 u,
  simp only [filter.mem_supr],
  split; intros h i,
  { exact λ hit, h ⟨i, hit⟩, },
  { exact h i i.prop, },
end

lemma ae_restrict_Union_iff [encodable ι] (s : ι → set α) {f g : α → E} :
  f =ᵐ[μ.restrict (⋃ i, s i)] g ↔ ∀ i, f =ᵐ[μ.restrict (s i)] g :=
by simp_rw [filter.eventually_eq, filter.eventually, ae_restrict_Union_eq, filter.mem_supr]

lemma ae_restrict_Union_finset_iff (s : ι → set α) (t : finset ι) {f g : α → E} :
  f =ᵐ[μ.restrict (⋃ i ∈ t, s i)] g ↔ ∀ i ∈ t, f =ᵐ[μ.restrict (s i)] g :=
by simp_rw [filter.eventually_eq, filter.eventually, ae_restrict_Union_finset_eq, filter.mem_supr]

lemma ae_restrict_Union_countable_iff (s : ι → set α) {t : set ι} (ht : t.countable) {f g : α → E} :
  f =ᵐ[μ.restrict (⋃ i ∈ t, s i)] g ↔ ∀ i ∈ t, f =ᵐ[μ.restrict (s i)] g :=
by simp_rw [filter.eventually_eq, filter.eventually, ae_restrict_Union_countable_eq s ht,
  filter.mem_supr]

variables [linear_order ι] {ℱ : filtration ι m} {τ σ : α → ι}

lemma sigma_finite_trim_mono {m m₂ m0 : measurable_space α} {μ : measure α} (hm : m ≤ m0)
  (hm₂ : m₂ ≤ m)
  [sigma_finite (μ.trim (hm₂.trans hm))] :
  sigma_finite (μ.trim hm) :=
begin
  have h := measure.finite_spanning_sets_in (μ.trim (hm₂.trans hm)) set.univ,
  refine measure.finite_spanning_sets_in.sigma_finite _,
  { use set.univ, },
  { refine
    { set := spanning_sets (μ.trim (hm₂.trans hm)),
      set_mem := λ _, set.mem_univ _,
      finite := λ i, _, -- This is the only one left to prove
      spanning := Union_spanning_sets _, },
    calc (μ.trim hm) (spanning_sets (μ.trim (hm₂.trans hm)) i)
        = ((μ.trim hm).trim hm₂) (spanning_sets (μ.trim (hm₂.trans hm)) i) :
      by rw @trim_measurable_set_eq α m₂ m (μ.trim hm) _ hm₂ (measurable_spanning_sets _ _)
    ... = (μ.trim (hm₂.trans hm)) (spanning_sets (μ.trim (hm₂.trans hm)) i) :
      by rw @trim_trim _ _ μ _ _ hm₂ hm
    ... < ⊤ : measure_spanning_sets_lt_top _ _, },
end

instance sigma_finite_stopping_time [order_bot ι]
  [(filter.at_top : filter ι).is_countably_generated]
  [sigma_finite_filtration μ ℱ] (hτ : is_stopping_time ℱ τ) :
  sigma_finite (μ.trim hτ.measurable_space_le) :=
begin
  refine sigma_finite_trim_mono hτ.measurable_space_le _,
  { exact ℱ ⊥, },
  { exact hτ.le_measurable_space_of_const_le (λ _, bot_le), },
  { apply_instance, },
end

lemma _root_.measure_theory.is_stopping_time.measurable_space_le_of_le {ι} [semilattice_sup ι]
  {f : filtration ι m} {τ : α → ι} (hτ : is_stopping_time f τ) {n : ι} (hτ_le : ∀ x, τ x ≤ n) :
  hτ.measurable_space ≤ m :=
(hτ.measurable_space_le_of_le_const hτ_le).trans (f.le n)

instance sigma_finite_stopping_time_of_le [order_bot ι]
  [sigma_finite_filtration μ ℱ] (hτ : is_stopping_time ℱ τ) {n : ι} (hτ_le : ∀ x, τ x ≤ n) :
  sigma_finite (μ.trim (hτ.measurable_space_le_of_le hτ_le)) :=
begin
  refine sigma_finite_trim_mono (hτ.measurable_space_le_of_le hτ_le) _,
  { exact ℱ ⊥, },
  { exact hτ.le_measurable_space_of_const_le (λ _, bot_le), },
  { apply_instance, },
end

lemma measurable_set_inter_le_const_iff (hτ : is_stopping_time ℱ τ) (s : set α) (i : ι) :
  measurable_set[hτ.measurable_space] (s ∩ {x | τ x ≤ i})
    ↔ measurable_set[(hτ.min_const i).measurable_space] (s ∩ {x | τ x ≤ i}) :=
begin
  rw [is_stopping_time.measurable_set_min_iff hτ (is_stopping_time_const _ i),
    is_stopping_time.measurable_space_const, is_stopping_time.measurable_set],
  refine ⟨λ h, ⟨h, _⟩, λ h j, h.1 j⟩,
  specialize h i,
  rwa [set.inter_assoc, set.inter_self] at h,
end

section normed_group

variables [normed_group E] {p : ℝ≥0∞} {u : ι → α → E}

lemma stopped_value_eq' {s : finset ι} (hbdd : ∀ x, τ x ∈ s) :
  stopped_value u τ = ∑ i in s, set.indicator {x | τ x = i} (u i) :=
begin
  ext y,
  rw [stopped_value, finset.sum_apply, finset.sum_indicator_eq_sum_filter],
  suffices : finset.filter (λ i, y ∈ {x : α | τ x = i}) s = ({τ y} : finset ι),
    by rw [this, finset.sum_singleton],
  ext1 x,
  simp only [set.mem_set_of_eq, finset.mem_filter, finset.mem_singleton],
  split; intro h,
  { exact h.2.symm, },
  { refine ⟨_, h.symm⟩, rw h, exact hbdd y, },
end

lemma mem_ℒp_stopped_value' (hτ : is_stopping_time ℱ τ) (hu : ∀ n, mem_ℒp (u n) p μ)
  {s : finset ι} (hbdd : ∀ x, τ x ∈ s)  :
  mem_ℒp (stopped_value u τ) p μ :=
begin
  rw stopped_value_eq' hbdd,
  swap, apply_instance,
  refine mem_ℒp_finset_sum' _ (λ i hi, mem_ℒp.indicator _ (hu i)),
  refine ℱ.le i {a : α | τ a = i} (hτ.measurable_set_eq_of_countable _ i),
  refine ((finset.finite_to_set s).subset (λ x hx, _)).countable,
  obtain ⟨y, rfl⟩ := hx,
  exact hbdd y,
end

lemma integrable_stopped_value' (hτ : is_stopping_time ℱ τ)
  (hu : ∀ n, integrable (u n) μ) {s : finset ι} (hbdd : ∀ x, τ x ∈ s) :
  integrable (stopped_value u τ) μ :=
by { simp_rw ← mem_ℒp_one_iff_integrable at hu ⊢, exact mem_ℒp_stopped_value' hτ hu hbdd, }

end normed_group

section condexp
variables [normed_group E] [normed_space ℝ E] [complete_space E]

lemma condexp_stopping_time_restrict_eq_of_countable [sigma_finite_filtration μ ℱ] {f : α → E}
  (hτ : is_stopping_time ℱ τ) (h_countable : (set.range τ).countable)
  [sigma_finite (μ.trim (hτ.measurable_space_le_of_countable h_countable))] {i : ι} :
  μ[f | hτ.measurable_space] =ᵐ[μ.restrict {x | τ x = i}] μ[f | ℱ i] :=
begin
  refine condexp_ae_eq_restrict_of_measurable_space_eq_on
    (hτ.measurable_space_le_of_countable h_countable) (ℱ.le i)
    (hτ.measurable_set_eq_of_countable' h_countable i) (λ t, _),
  rw [set.inter_comm _ t, is_stopping_time.measurable_set_inter_eq_iff],
end

lemma condexp_stopping_time_restrict_eq_of_encodable [encodable ι] [sigma_finite_filtration μ ℱ]
  {f : α → E} (hτ : is_stopping_time ℱ τ)
  [sigma_finite (μ.trim hτ.measurable_space_le_of_encodable)] {i : ι} :
  μ[f | hτ.measurable_space] =ᵐ[μ.restrict {x | τ x = i}] μ[f | ℱ i] :=
condexp_stopping_time_restrict_eq_of_countable hτ (set.countable_encodable _)

lemma condexp_stopping_time_restrict_eq [(filter.at_top : filter ι).is_countably_generated]
  [topological_space ι] [order_topology ι] [first_countable_topology ι]
  [sigma_finite_filtration μ ℱ] {f : α → E}
  (hτ : is_stopping_time ℱ τ) [sigma_finite (μ.trim hτ.measurable_space_le)] {i : ι} :
  μ[f | hτ.measurable_space] =ᵐ[μ.restrict {x | τ x = i}] μ[f | ℱ i] :=
begin
  refine condexp_ae_eq_restrict_of_measurable_space_eq_on
    hτ.measurable_space_le (ℱ.le i) (hτ.measurable_set_eq' i) (λ t, _),
  rw [set.inter_comm _ t, is_stopping_time.measurable_set_inter_eq_iff],
end

lemma condexp_min_stopping_time_restrict_le [(filter.at_top : filter ι).is_countably_generated]
  [topological_space ι] [measurable_space ι]
  [order_topology ι] [second_countable_topology ι] [borel_space ι] {f : α → E}
  (hτ : is_stopping_time ℱ τ) (hσ : is_stopping_time ℱ σ)
  [sigma_finite (μ.trim hτ.measurable_space_le)]
  [sigma_finite (μ.trim (hτ.min hσ).measurable_space_le)] :
  μ[f | (hτ.min hσ).measurable_space] =ᵐ[μ.restrict {x | τ x ≤ σ x}] μ[f | hτ.measurable_space] :=
begin
  refine (condexp_ae_eq_restrict_of_measurable_space_eq_on hτ.measurable_space_le
    (hτ.min hσ).measurable_space_le (hτ.measurable_set_le_stopping_time hσ) (λ t, _)).symm,
  rw [set.inter_comm _ t, is_stopping_time.measurable_set_inter_le_iff],
end

lemma condexp_min_stopping_time_restrict_le_const
  [(filter.at_top : filter ι).is_countably_generated] {f : α → E}
  (hτ : is_stopping_time ℱ τ) [sigma_finite (μ.trim hτ.measurable_space_le)]
  [∀ i, sigma_finite (μ.trim (hτ.min_const i).measurable_space_le)] {i : ι} :
  μ[f | (hτ.min_const i).measurable_space]
    =ᵐ[μ.restrict {x | τ x ≤ i}] μ[f | hτ.measurable_space] :=
begin
  refine (condexp_ae_eq_restrict_of_measurable_space_eq_on hτ.measurable_space_le
    (hτ.min_const i).measurable_space_le (hτ.measurable_set_le' i) (λ t, _)).symm,
  rw [set.inter_comm _ t, measurable_set_inter_le_const_iff],
end

lemma condexp_stopping_time_restrict_eq_const [(filter.at_top : filter ι).is_countably_generated]
  [topological_space ι] [order_topology ι] [first_countable_topology ι]
  [sigma_finite_filtration μ ℱ] {f : ι → α → E} (h : martingale f ℱ μ)
  (hτ : is_stopping_time ℱ τ) [sigma_finite (μ.trim hτ.measurable_space_le)]
  {i n : ι} (hin : i ≤ n) :
  μ[f n | hτ.measurable_space] =ᵐ[μ.restrict {x | τ x = i}] f i :=
begin
  refine filter.eventually_eq.trans _ (ae_restrict_of_ae (h.condexp_ae_eq hin)),
  refine condexp_ae_eq_restrict_of_measurable_space_eq_on hτ.measurable_space_le (ℱ.le i)
    (hτ.measurable_set_eq' i) (λ t, _),
  rw [set.inter_comm _ t, is_stopping_time.measurable_set_inter_eq_iff],
end

lemma condexp_stopping_time_restrict_eq_const_of_le_const
  [topological_space ι] [order_topology ι] [first_countable_topology ι]
  [sigma_finite_filtration μ ℱ] {f : ι → α → E} (h : martingale f ℱ μ)
  (hτ : is_stopping_time ℱ τ) {i n : ι} (hτ_le : ∀ x, τ x ≤ n)
  [sigma_finite (μ.trim (hτ.measurable_space_le_of_le hτ_le))] :
  μ[f n | hτ.measurable_space] =ᵐ[μ.restrict {x | τ x = i}] f i :=
begin
  by_cases hin : i ≤ n,
  { refine filter.eventually_eq.trans _ (ae_restrict_of_ae (h.condexp_ae_eq hin)),
    refine condexp_ae_eq_restrict_of_measurable_space_eq_on (hτ.measurable_space_le_of_le hτ_le)
      (ℱ.le i) (hτ.measurable_set_eq' i) (λ t, _),
    rw [set.inter_comm _ t, is_stopping_time.measurable_set_inter_eq_iff], },
  { suffices : {x : α | τ x = i} = ∅, by simp [this],
    ext1 x,
    simp only [set.mem_set_of_eq, set.mem_empty_eq, iff_false],
    rintro rfl,
    exact hin (hτ_le x), },
end

lemma stopped_value_ae_eq_restrict_eq [topological_space ι] [order_topology ι]
  [first_countable_topology ι] [sigma_finite_filtration μ ℱ] {f : ι → α → E}
  (h : martingale f ℱ μ) (hτ : is_stopping_time ℱ τ) {i n : ι} (hτ_le : ∀ x, τ x ≤ n)
  [sigma_finite (μ.trim ((hτ.measurable_space_le_of_le hτ_le)))] :
  stopped_value f τ =ᵐ[μ.restrict {x | τ x = i}] μ[f n | hτ.measurable_space] :=
begin
  refine filter.eventually_eq.trans _
    (condexp_stopping_time_restrict_eq_const_of_le_const h hτ hτ_le).symm,
  rw [filter.eventually_eq, ae_restrict_iff' (ℱ.le _ _ (hτ.measurable_set_eq i))],
  refine filter.eventually_of_forall (λ x hx, _),
  rw set.mem_set_of_eq at hx,
  simp_rw [stopped_value, hx],
end

lemma martingale.stopped_value_ae_eq_condexp_of_le_const_of_countable_range [topological_space ι]
  [order_topology ι] [first_countable_topology ι] [sigma_finite_filtration μ ℱ]
  {f : ι → α → E} (h : martingale f ℱ μ) (hτ : is_stopping_time ℱ τ) {n : ι}
  (hτ_le : ∀ x, τ x ≤ n) (h_countable_range : (set.range τ).countable)
  [sigma_finite (μ.trim (hτ.measurable_space_le_of_le hτ_le))] :
  stopped_value f τ =ᵐ[μ] μ[f n | hτ.measurable_space] :=
begin
  have : set.univ = ⋃ i ∈ (set.range τ), {x | τ x = i},
  { ext1 x,
    simp only [set.mem_univ, set.mem_range, true_and, set.Union_exists, set.Union_Union_eq',
      set.mem_Union, set.mem_set_of_eq, exists_apply_eq_apply'], },
  nth_rewrite 0 ← @measure.restrict_univ α _ μ,
  rw [this, ae_restrict_Union_countable_iff _ h_countable_range],
  exact λ i hi, stopped_value_ae_eq_restrict_eq h _ hτ_le,
end

lemma martingale.stopped_value_ae_eq_condexp_of_le_const' [order_bot ι]
  [locally_finite_order ι] [topological_space ι]
  [order_topology ι] [first_countable_topology ι] [sigma_finite_filtration μ ℱ]
  {f : ι → α → E} (h : martingale f ℱ μ) (hτ : is_stopping_time ℱ τ) {n : ι}
  (hτ_le : ∀ x, τ x ≤ n)
  [sigma_finite (μ.trim (hτ.measurable_space_le_of_le hτ_le))] :
  stopped_value f τ =ᵐ[μ] μ[f n | hτ.measurable_space] :=
begin
  refine h.stopped_value_ae_eq_condexp_of_le_const_of_countable_range hτ hτ_le
    (set.finite.countable _),
  refine set.finite.subset (set.finite_Iic n) (λ x hx, _),
  obtain ⟨y, rfl⟩ := hx,
  exact hτ_le y,
end

lemma martingale.stopped_value_ae_eq_condexp_of_le_const [encodable ι] [topological_space ι]
  [order_topology ι] [first_countable_topology ι] [sigma_finite_filtration μ ℱ]
  {f : ι → α → E} (h : martingale f ℱ μ) (hτ : is_stopping_time ℱ τ) {n : ι}
  (hτ_le : ∀ x, τ x ≤ n)
  [sigma_finite (μ.trim (hτ.measurable_space_le_of_le hτ_le))] :
  stopped_value f τ =ᵐ[μ] μ[f n | hτ.measurable_space] :=
h.stopped_value_ae_eq_condexp_of_le_const_of_countable_range hτ hτ_le (set.countable_encodable _)

lemma martingale.stopped_value_ae_eq_condexp_of_le_of_countable_range
  [(filter.at_top : filter ι).is_countably_generated] [topological_space ι]
  [order_topology ι] [first_countable_topology ι] [sigma_finite_filtration μ ℱ] {f : ι → α → E}
  (h : martingale f ℱ μ)
  (hτ : is_stopping_time ℱ τ) (hσ : is_stopping_time ℱ σ) {n : ι}
  (hσ_le_τ : σ ≤ τ) (hτ_le : ∀ x, τ x ≤ n)
  (hτ_countable_range : (set.range τ).countable)
  (hσ_countable_range : (set.range σ).countable)
  [sigma_finite (μ.trim hτ.measurable_space_le)] [sigma_finite (μ.trim hσ.measurable_space_le)] :
  stopped_value f σ =ᵐ[μ] μ[stopped_value f τ | hσ.measurable_space] :=
begin
  have : μ[stopped_value f τ|hσ.measurable_space]
      =ᵐ[μ] μ[μ[f n|hτ.measurable_space] | hσ.measurable_space],
    from condexp_congr_ae (h.stopped_value_ae_eq_condexp_of_le_const_of_countable_range hτ hτ_le
      hτ_countable_range),
  refine (filter.eventually_eq.trans _ (condexp_condexp_of_le _ hτ.measurable_space_le).symm).trans
    this.symm,
  { exact h.stopped_value_ae_eq_condexp_of_le_const_of_countable_range hσ
      (λ x, (hσ_le_τ x).trans (hτ_le x)) hσ_countable_range, },
  { exact hσ.measurable_space_mono hτ hσ_le_τ, },
end

lemma martingale.stopped_value_ae_eq_condexp_of_le'
  [(filter.at_top : filter ι).is_countably_generated] [order_bot ι] [locally_finite_order ι]
  [topological_space ι] [order_topology ι] [first_countable_topology ι]
  [sigma_finite_filtration μ ℱ] {f : ι → α → E} (h : martingale f ℱ μ)
  (hτ : is_stopping_time ℱ τ) (hσ : is_stopping_time ℱ σ) {n : ι}
  (hσ_le_τ : σ ≤ τ) (hτ_le : ∀ x, τ x ≤ n)
  [sigma_finite (μ.trim hτ.measurable_space_le)] [sigma_finite (μ.trim hσ.measurable_space_le)] :
  stopped_value f σ =ᵐ[μ] μ[stopped_value f τ | hσ.measurable_space] :=
begin
  refine h.stopped_value_ae_eq_condexp_of_le_of_countable_range hτ hσ hσ_le_τ hτ_le
    (set.finite.subset (set.finite_Iic n) (λ x hx, _)).countable
    (set.finite.subset (set.finite_Iic n) (λ x hx, _)).countable,
  { obtain ⟨y, rfl⟩ := hx,
    exact hτ_le y, },
  { obtain ⟨y, rfl⟩ := hx,
    exact (hσ_le_τ y).trans (hτ_le y), },
end

lemma martingale.stopped_value_ae_eq_condexp_of_le [encodable ι] [topological_space ι]
  [order_topology ι] [first_countable_topology ι] [sigma_finite_filtration μ ℱ] {f : ι → α → E}
  (h : martingale f ℱ μ)
  (hτ : is_stopping_time ℱ τ) (hσ : is_stopping_time ℱ σ) {n : ι}
  (hσ_le_τ : σ ≤ τ) (hτ_le : ∀ x, τ x ≤ n)
  [sigma_finite (μ.trim hτ.measurable_space_le)] [sigma_finite (μ.trim hσ.measurable_space_le)] :
  stopped_value f σ =ᵐ[μ] μ[stopped_value f τ | hσ.measurable_space] :=
h.stopped_value_ae_eq_condexp_of_le_of_countable_range hτ hσ hσ_le_τ hτ_le
  (set.countable_encodable _) (set.countable_encodable _)

lemma aux' [encodable ι] [order_bot ι] [locally_finite_order ι] [topological_space ι]
  [order_topology ι] [measurable_space ι] [borel_space ι] [second_countable_topology ι]
  {f : ι → α → E} [measurable_space E] [borel_space E] [second_countable_topology E]
  (h : martingale f ℱ μ) (hf_prog : prog_measurable ℱ f)
  (hτ : is_stopping_time ℱ τ) (hσ : is_stopping_time ℱ σ)
  [sigma_finite (μ.trim hσ.measurable_space_le)] {n : ι} (hτ_le : ∀ x, τ x ≤ n) :
  μ[stopped_value f τ|hσ.measurable_space] =ᵐ[μ.restrict {x : α | τ x ≤ σ x}] stopped_value f τ :=
begin
  have hτ_mem_finset : ∀ x, τ x ∈ (set.finite_Iic n).to_finset,
  { intro x,
    rw set.finite.mem_to_finset,
    exact hτ_le x, },
  rw ae_eq_restrict_iff_indicator_ae_eq
    (hτ.measurable_space_le _ (hτ.measurable_set_le_stopping_time hσ)),
  swap, apply_instance,
  refine (condexp_indicator _ _).symm.trans _,
  { exact integrable_stopped_value' hτ h.integrable hτ_mem_finset, },
  { exact hτ.measurable_set_stopping_time_le hσ, },
  refine condexp_of_ae_strongly_measurable' hσ.measurable_space_le _ _,
  { refine strongly_measurable.ae_strongly_measurable' _,
    refine strongly_measurable.strongly_measurable_of_measurable_space_le_on
      (hτ.measurable_set_le_stopping_time hσ) _ _ _,
    { intros t ht,
      rw set.inter_comm _ t at ht ⊢,
      rw [hτ.measurable_set_inter_le_iff, is_stopping_time.measurable_set_min_iff hτ hσ] at ht,
      exact ht.2, },
    { refine strongly_measurable.indicator _ (hτ.measurable_set_le_stopping_time hσ),
      refine measurable.strongly_measurable _,
      exact measurable_stopped_value hf_prog hτ, },
    { intros x hx,
      simp only [hx, set.indicator_of_not_mem, not_false_iff], }, },
  { refine (integrable_stopped_value' hτ h.integrable hτ_mem_finset).indicator _,
    exact hτ.measurable_space_le _ (hτ.measurable_set_le_stopping_time hσ), },
end

end condexp

end not_nat

section nat

variables {𝒢 : filtration ℕ m} {τ σ : α → ℕ}
  [normed_group E] [normed_space ℝ E] [complete_space E]

/-- **Optional Sampling** -/
lemma martingale.stopped_value_min_ae_eq_condexp
  [measurable_space E] [borel_space E] [second_countable_topology E]
  [sigma_finite_filtration μ 𝒢] {f : ℕ → α → E} (h : martingale f 𝒢 μ)
  (hτ : is_stopping_time 𝒢 τ) (hσ : is_stopping_time 𝒢 σ) {n : ℕ}
  (hτ_le : ∀ x, τ x ≤ n)
  [h_sf_min : sigma_finite (μ.trim (hτ.min hσ).measurable_space_le)] :
  stopped_value f (λ x, min (σ x) (τ x)) =ᵐ[μ] μ[stopped_value f τ | hσ.measurable_space] :=
begin
  have h_min_comm : (hτ.min hσ).measurable_space = (hσ.min hτ).measurable_space,
    by rw [is_stopping_time.measurable_space_min, is_stopping_time.measurable_space_min, inf_comm],
  haveI : sigma_finite (μ.trim (hσ.min hτ).measurable_space_le),
  { convert h_sf_min; { ext1 x, rw min_comm, }, },
  refine (h.stopped_value_ae_eq_condexp_of_le hτ (hσ.min hτ) (λ x, min_le_right _ _) hτ_le).trans _,
  refine ae_of_ae_restrict_of_ae_restrict_compl {x | σ x ≤ τ x} _ _,
  { exact condexp_min_stopping_time_restrict_le hσ hτ, },
  { suffices : μ[stopped_value f τ|(hσ.min hτ).measurable_space]
      =ᵐ[μ.restrict {x | τ x ≤ σ x}] μ[stopped_value f τ|hσ.measurable_space],
    { rw ae_restrict_iff' (hσ.measurable_space_le _ (hσ.measurable_set_le_stopping_time hτ).compl),
      rw [filter.eventually_eq, ae_restrict_iff'] at this,
      swap, { exact hτ.measurable_space_le _ (hτ.measurable_set_le_stopping_time hσ), },
      filter_upwards [this] with x hx hx_mem,
      simp only [set.mem_compl_eq, set.mem_set_of_eq, not_le] at hx_mem,
      exact hx hx_mem.le, },
    refine filter.eventually_eq.trans _ ((condexp_min_stopping_time_restrict_le hτ hσ).trans _),
    { exact stopped_value f τ, },
    { rw h_min_comm, },
    { have h1 : μ[stopped_value f τ|hτ.measurable_space] = stopped_value f τ,
      { refine condexp_of_strongly_measurable hτ.measurable_space_le _ _,
        { refine measurable.strongly_measurable _,
          exact measurable_stopped_value h.adapted.prog_measurable_of_nat hτ, },
        { exact integrable_stopped_value hτ h.integrable hτ_le, }, },
      rw h1,
      exact (aux' h h.adapted.prog_measurable_of_nat hτ hσ hτ_le).symm, }, },
end

end nat

end stopping

end measure_theory
