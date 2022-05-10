/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import probability.martingale

/-!
# Draft
-/

open_locale measure_theory
open topological_space

namespace measure_theory

section stopping

variables {α ι : Type*} {m : measurable_space α} {μ : measure α}

section not_nat

variables [linear_order ι] {ℱ : filtration ι m} {τ σ : α → ι}

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

variables {E : Type*}


section condexp
variables [normed_group E] [normed_space ℝ E] [complete_space E]

lemma condexp_indicator_stopping_time_eq [(filter.at_top : filter ι).is_countably_generated]
  [topological_space ι] [order_topology ι] [first_countable_topology ι]
  [sigma_finite_filtration μ ℱ] {f : α → E}
  (hτ : is_stopping_time ℱ τ) [sigma_finite (μ.trim hτ.measurable_space_le)]
  {i : ι} (hf : integrable f μ) :
  μ[f | hτ.measurable_space] =ᵐ[μ.restrict {x | τ x = i}] μ[f | ℱ i] :=
begin
  refine condexp_ae_eq_restrict_of_measurable_space_eq_on
    hτ.measurable_space_le (ℱ.le i) hf (hτ.measurable_set_eq' i) (λ t, _),
  rw [set.inter_comm _ t, is_stopping_time.measurable_set_inter_eq_iff],
end

lemma condexp_indicator_stopping_time_le [(filter.at_top : filter ι).is_countably_generated]
  [topological_space ι] [measurable_space ι]
  [order_topology ι] [second_countable_topology ι] [borel_space ι] {f : α → E}
  (hτ : is_stopping_time ℱ τ) (hσ : is_stopping_time ℱ σ)
  [sigma_finite (μ.trim hτ.measurable_space_le)]
  [sigma_finite (μ.trim (hτ.min hσ).measurable_space_le)]
  (hf : integrable f μ) :
  μ[f | hτ.measurable_space] =ᵐ[μ.restrict {x | τ x ≤ σ x}] μ[f | (hτ.min hσ).measurable_space] :=
begin
  refine condexp_ae_eq_restrict_of_measurable_space_eq_on hτ.measurable_space_le
    (hτ.min hσ).measurable_space_le hf (hτ.measurable_set_le_stopping_time hσ) (λ t, _),
  rw [set.inter_comm _ t, is_stopping_time.measurable_set_inter_le_iff],
end

lemma condexp_indicator_stopping_time_le_const [(filter.at_top : filter ι).is_countably_generated]
  {f : α → E}
  (hτ : is_stopping_time ℱ τ) [sigma_finite (μ.trim hτ.measurable_space_le)]
  [∀ i, sigma_finite (μ.trim (hτ.min_const i).measurable_space_le)]
  {i : ι} (hf : integrable f μ) :
  μ[f | hτ.measurable_space]
    =ᵐ[μ.restrict {x | τ x ≤ i}] μ[f | (hτ.min_const i).measurable_space] :=
begin
  refine condexp_ae_eq_restrict_of_measurable_space_eq_on hτ.measurable_space_le
    (hτ.min_const i).measurable_space_le hf (hτ.measurable_set_le' i) (λ t, _),
  rw [set.inter_comm _ t, measurable_set_inter_le_const_iff],
end

lemma condexp_indicator_todo [(filter.at_top : filter ι).is_countably_generated]
  [topological_space ι] [order_topology ι] [first_countable_topology ι]
  [sigma_finite_filtration μ ℱ] {f : ι → α → E} (h : martingale f ℱ μ)
  (hτ : is_stopping_time ℱ τ) [sigma_finite (μ.trim hτ.measurable_space_le)]
  {i n : ι} (hin : i ≤ n) :
  f i =ᵐ[μ.restrict {x | τ x = i}] μ[f n | hτ.measurable_space] :=
begin
  have hfi_eq_restrict : f i =ᵐ[μ.restrict {x | τ x = i}] μ[f n | ℱ i],
    from ae_restrict_of_ae (h.condexp_ae_eq hin).symm,
  refine hfi_eq_restrict.trans _,
  refine condexp_ae_eq_restrict_of_measurable_space_eq_on (ℱ.le i) hτ.measurable_space_le
    (h.integrable n) (hτ.measurable_set_eq i) (λ t, _),
  rw [set.inter_comm _ t, is_stopping_time.measurable_set_inter_eq_iff],
end

end condexp

end not_nat

section nat

variables {E : Type*} {𝒢 : filtration ℕ m} {τ σ : α → ℕ}
  [normed_group E] [normed_space ℝ E] [complete_space E]

lemma martingale.stopped_value_eq_of_le_const [sigma_finite_filtration μ 𝒢] {f : ℕ → α → E}
  (h : martingale f 𝒢 μ) (hτ : is_stopping_time 𝒢 τ) {n : ℕ}
  (hτ_le : ∀ x, τ x ≤ n)
  [sigma_finite (μ.trim hτ.measurable_space_le)] :
  stopped_value f τ =ᵐ[μ] μ[f n | hτ.measurable_space] :=
begin
  rw [stopped_value_eq hτ_le],
  swap, apply_instance,
  simp only [finset.sum_apply],
  have h_fi_eq_condexp : ∀ i, i ∈ {j | j ≤ n} → {x | τ x = i}.indicator (f i)
    =ᵐ[μ] {x | τ x = i}.indicator (μ[f n | hτ.measurable_space]),
  { intros i hin,
    rw ← ae_eq_restrict_iff_indicator_ae_eq (𝒢.le i _ (hτ.measurable_set_eq i)),
    exact condexp_indicator_todo h hτ hin, },
  have : (λ x, (finset.range (n + 1)).sum (λ i, {x : α | τ x = i}.indicator (f i) x))
    =ᵐ[μ] (λ x, (finset.range (n + 1)).sum (λ i, {x : α | τ x = i}.indicator
      (μ[f n | hτ.measurable_space]) x)),
  { simp_rw filter.eventually_eq at h_fi_eq_condexp,
    rw ← filter.eventually_all_finite (set.finite_le_nat n) at h_fi_eq_condexp,
    filter_upwards [h_fi_eq_condexp] with x hx,
    refine finset.sum_congr rfl (λ i hi, _),
    rw [finset.mem_range, nat.lt_succ_iff] at hi,
    exact hx i hi, },
  refine this.trans (filter.eventually_of_forall (λ x, _)),
  rw [finset.sum_indicator_eq_sum_filter, finset.sum_const],
  suffices : (finset.filter (λ (i : ℕ), x ∈ {x : α | τ x = i}) (finset.range (n + 1))).card = 1,
    by rw [this, one_nsmul],
  simp_rw [set.mem_set_of_eq, finset.filter_eq, finset.mem_range, nat.lt_succ_iff,
    if_pos (hτ_le x), finset.card_singleton],
end

lemma martingale.stopped_value_eq_of_le [sigma_finite_filtration μ 𝒢] {f : ℕ → α → E}
  (h : martingale f 𝒢 μ)
  (hτ : is_stopping_time 𝒢 τ) (hσ : is_stopping_time 𝒢 σ) {n : ℕ}
  (hσ_le_τ : σ ≤ τ) (hτ_le : ∀ x, τ x ≤ n)
  [sigma_finite (μ.trim hτ.measurable_space_le)] [sigma_finite (μ.trim hσ.measurable_space_le)] :
  stopped_value f σ =ᵐ[μ] μ[stopped_value f τ | hσ.measurable_space] :=
begin
  have : μ[stopped_value f τ|hσ.measurable_space]
      =ᵐ[μ] μ[μ[f n|hτ.measurable_space] | hσ.measurable_space],
    from condexp_congr_ae (h.stopped_value_eq_of_le_const hτ hτ_le),
  refine (filter.eventually_eq.trans _ (condexp_condexp_of_le _ _).symm).trans this.symm,
  { exact h.stopped_value_eq_of_le_const hσ (λ x, (hσ_le_τ x).trans (hτ_le x)), },
  { exact is_stopping_time.measurable_space_mono _ _ hσ_le_τ, },
  { exact hτ.measurable_space_le, },
  { apply_instance, },
end

lemma condexp_of_ae_strongly_measurable' {α} {m m0 : measurable_space α} {μ : measure α}
  (hm : m ≤ m0) [hμm : sigma_finite (μ.trim hm)]
  {f : α → E} (hf : ae_strongly_measurable' m f μ) (hfi : integrable f μ) :
  μ[f|m] =ᵐ[μ] f :=
begin
  refine ((condexp_congr_ae hf.ae_eq_mk).trans _).trans hf.ae_eq_mk.symm,
  rw condexp_of_strongly_measurable hm hf.strongly_measurable_mk
    ((integrable_congr hf.ae_eq_mk).mp hfi),
end

lemma aux {f : ℕ → α → E} [measurable_space E] [borel_space E] [second_countable_topology E]
  (h : martingale f 𝒢 μ) (hf_prog : prog_measurable 𝒢 f)
  (hτ : is_stopping_time 𝒢 τ) (hσ : is_stopping_time 𝒢 σ)
  [sigma_finite (μ.trim hσ.measurable_space_le)] {n : ℕ} (hτ_le : ∀ x, τ x ≤ n) :
  μ[stopped_value f τ|hσ.measurable_space] =ᵐ[μ.restrict {x : α | τ x ≤ σ x}] stopped_value f τ :=
begin
  rw ae_eq_restrict_iff_indicator_ae_eq
    (hτ.measurable_space_le _ (hτ.measurable_set_le_stopping_time hσ)),
  swap, apply_instance,
  refine (condexp_indicator _ _).symm.trans _,
  { exact integrable_stopped_value hτ h.integrable hτ_le, },
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
  { refine (integrable_stopped_value hτ h.integrable hτ_le).indicator _,
    exact hτ.measurable_space_le _ (hτ.measurable_set_le_stopping_time hσ), },
end

/-- **Optional Sampling** -/
lemma martingale.stopped_value_min_eq
  [measurable_space E] [borel_space E] [second_countable_topology E]
  [sigma_finite_filtration μ 𝒢] {f : ℕ → α → E} (h : martingale f 𝒢 μ)
  (hτ : is_stopping_time 𝒢 τ) (hσ : is_stopping_time 𝒢 σ) {n : ℕ}
  (hτ_le : ∀ x, τ x ≤ n)
  [sigma_finite (μ.trim hτ.measurable_space_le)] [sigma_finite (μ.trim hσ.measurable_space_le)]
  [h_sf_min : sigma_finite (μ.trim (hτ.min hσ).measurable_space_le)] :
  stopped_value f (λ x, min (σ x) (τ x)) =ᵐ[μ] μ[stopped_value f τ | hσ.measurable_space] :=
begin
  have h_min_comm : (hτ.min hσ).measurable_space = (hσ.min hτ).measurable_space,
    by rw [is_stopping_time.measurable_space_min, is_stopping_time.measurable_space_min, inf_comm],
  haveI : sigma_finite (μ.trim (hσ.min hτ).measurable_space_le),
  { convert h_sf_min; { ext1 x, rw min_comm, }, },
  refine (h.stopped_value_eq_of_le hτ (hσ.min hτ) (λ x, min_le_right _ _) hτ_le).trans _,
  refine ae_of_ae_restrict_of_ae_restrict_compl {x | σ x ≤ τ x} _ _,
  { refine (condexp_indicator_stopping_time_le hσ hτ _).symm,
    exact integrable_stopped_value hτ h.integrable hτ_le, },
  { suffices : μ[stopped_value f τ|(hσ.min hτ).measurable_space]
      =ᵐ[μ.restrict {x | τ x ≤ σ x}] μ[stopped_value f τ|hσ.measurable_space],
    { rw ae_restrict_iff' (hσ.measurable_space_le _ (hσ.measurable_set_le_stopping_time hτ).compl),
      rw [filter.eventually_eq, ae_restrict_iff'] at this,
      swap, { exact hτ.measurable_space_le _ (hτ.measurable_set_le_stopping_time hσ), },
      filter_upwards [this] with x hx hx_mem,
      simp only [set.mem_compl_eq, set.mem_set_of_eq, not_le] at hx_mem,
      exact hx hx_mem.le, },
    refine filter.eventually_eq.trans _ ((condexp_indicator_stopping_time_le hτ hσ _).symm.trans _),
    { exact stopped_value f τ, },
    { rw h_min_comm, },
    { exact integrable_stopped_value hτ h.integrable hτ_le, },
    { have h1 : μ[stopped_value f τ|hτ.measurable_space] = stopped_value f τ,
      { refine condexp_of_strongly_measurable hτ.measurable_space_le _ _,
        { refine measurable.strongly_measurable _,
          exact measurable_stopped_value h.adapted.prog_measurable_of_nat hτ, },
        { exact integrable_stopped_value hτ h.integrable hτ_le, }, },
      rw h1,
      exact (aux h h.adapted.prog_measurable_of_nat hτ hσ hτ_le).symm, }, },
end

end nat

end stopping

end measure_theory
