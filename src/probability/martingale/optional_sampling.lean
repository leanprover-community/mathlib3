/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import probability.martingale.basic

/-!
# Optional sampling theorem

If `τ` is a bounded stopping time and `σ` is another stopping
time, then the stopped value of a martingale `f` with respect to `min τ σ` is almost everywhere
equal to `μ[stopped_value f τ | hσ.measurable_space]`.

## Main results

* `stopped_value_min_ae_eq_condexp` : the optional sampling theorem. TODO

-/

open_locale measure_theory big_operators ennreal
open topological_space

namespace measure_theory

namespace martingale

variables {Ω ι E : Type*} {m : measurable_space Ω} {μ : measure Ω}
  [linear_order ι] [topological_space ι] [order_topology ι]
  [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]
  {ℱ : filtration ι m} {τ σ : Ω → ι} {f : ι → Ω → E}  {i n : ι}

section first_countable_topology

variables [first_countable_topology ι] [sigma_finite_filtration μ ℱ]

lemma condexp_stopping_time_ae_eq_restrict_eq_const
  [(filter.at_top : filter ι).is_countably_generated]
  (h : martingale f ℱ μ) (hτ : is_stopping_time ℱ τ) [sigma_finite (μ.trim hτ.measurable_space_le)]
  (hin : i ≤ n) :
  μ[f n | hτ.measurable_space] =ᵐ[μ.restrict {x | τ x = i}] f i :=
begin
  refine filter.eventually_eq.trans _ (ae_restrict_of_ae (h.condexp_ae_eq hin)),
  refine condexp_ae_eq_restrict_of_measurable_space_eq_on hτ.measurable_space_le (ℱ.le i)
    (hτ.measurable_set_eq' i) (λ t, _),
  rw [set.inter_comm _ t, is_stopping_time.measurable_set_inter_eq_iff],
end

lemma condexp_stopping_time_ae_eq_restrict_eq_const_of_le_const
  (h : martingale f ℱ μ) (hτ : is_stopping_time ℱ τ) (hτ_le : ∀ x, τ x ≤ n)
  [sigma_finite (μ.trim (hτ.measurable_space_le_of_le hτ_le))] (i : ι) :
  μ[f n | hτ.measurable_space] =ᵐ[μ.restrict {x | τ x = i}] f i :=
begin
  by_cases hin : i ≤ n,
  { refine filter.eventually_eq.trans _ (ae_restrict_of_ae (h.condexp_ae_eq hin)),
    refine condexp_ae_eq_restrict_of_measurable_space_eq_on (hτ.measurable_space_le_of_le hτ_le)
      (ℱ.le i) (hτ.measurable_set_eq' i) (λ t, _),
    rw [set.inter_comm _ t, is_stopping_time.measurable_set_inter_eq_iff], },
  { suffices : {x : Ω | τ x = i} = ∅, by simp [this],
    ext1 x,
    simp only [set.mem_set_of_eq, set.mem_empty_eq, iff_false],
    rintro rfl,
    exact hin (hτ_le x), },
end

lemma stopped_value_ae_eq_restrict_eq
  (h : martingale f ℱ μ) (hτ : is_stopping_time ℱ τ) (hτ_le : ∀ x, τ x ≤ n)
  [sigma_finite (μ.trim ((hτ.measurable_space_le_of_le hτ_le)))] (i : ι) :
  stopped_value f τ =ᵐ[μ.restrict {x | τ x = i}] μ[f n | hτ.measurable_space] :=
begin
  refine filter.eventually_eq.trans _
    (condexp_stopping_time_ae_eq_restrict_eq_const_of_le_const h hτ hτ_le i).symm,
  rw [filter.eventually_eq, ae_restrict_iff' (ℱ.le _ _ (hτ.measurable_set_eq i))],
  refine filter.eventually_of_forall (λ x hx, _),
  rw set.mem_set_of_eq at hx,
  simp_rw [stopped_value, hx],
end

lemma stopped_value_ae_eq_condexp_of_le_const_of_countable_range
  (h : martingale f ℱ μ) (hτ : is_stopping_time ℱ τ)
  (hτ_le : ∀ x, τ x ≤ n) (h_countable_range : (set.range τ).countable)
  [sigma_finite (μ.trim (hτ.measurable_space_le_of_le hτ_le))] :
  stopped_value f τ =ᵐ[μ] μ[f n | hτ.measurable_space] :=
begin
  have : set.univ = ⋃ i ∈ (set.range τ), {x | τ x = i},
  { ext1 x,
    simp only [set.mem_univ, set.mem_range, true_and, set.Union_exists, set.Union_Union_eq',
      set.mem_Union, set.mem_set_of_eq, exists_apply_eq_apply'], },
  nth_rewrite 0 ← @measure.restrict_univ Ω _ μ,
  rw [this, ae_eq_restrict_bUnion_iff _ h_countable_range],
  exact λ i hi, stopped_value_ae_eq_restrict_eq h _ hτ_le i,
end

lemma stopped_value_ae_eq_condexp_of_le_const' [locally_finite_order_bot ι]
  (h : martingale f ℱ μ) (hτ : is_stopping_time ℱ τ) (hτ_le : ∀ x, τ x ≤ n)
  [sigma_finite (μ.trim (hτ.measurable_space_le_of_le hτ_le))] :
  stopped_value f τ =ᵐ[μ] μ[f n | hτ.measurable_space] :=
begin
  refine h.stopped_value_ae_eq_condexp_of_le_const_of_countable_range hτ hτ_le
    (set.finite.countable _),
  refine set.finite.subset (set.finite_Iic n) (λ x hx, _),
  obtain ⟨y, rfl⟩ := hx,
  exact hτ_le y,
end

lemma stopped_value_ae_eq_condexp_of_le_const [countable ι]
  (h : martingale f ℱ μ) (hτ : is_stopping_time ℱ τ) (hτ_le : ∀ x, τ x ≤ n)
  [sigma_finite (μ.trim (hτ.measurable_space_le_of_le hτ_le))] :
  stopped_value f τ =ᵐ[μ] μ[f n | hτ.measurable_space] :=
h.stopped_value_ae_eq_condexp_of_le_const_of_countable_range hτ hτ_le (set.to_countable _)

lemma stopped_value_ae_eq_condexp_of_le_of_countable_range
  [(filter.at_top : filter ι).is_countably_generated]
  (h : martingale f ℱ μ) (hτ : is_stopping_time ℱ τ) (hσ : is_stopping_time ℱ σ)
  (hσ_le_τ : σ ≤ τ) (hτ_le : ∀ x, τ x ≤ n)
  (hτ_countable_range : (set.range τ).countable) (hσ_countable_range : (set.range σ).countable)
  [sigma_finite (μ.trim hσ.measurable_space_le)] :
  stopped_value f σ =ᵐ[μ] μ[stopped_value f τ | hσ.measurable_space] :=
begin
  haveI : sigma_finite (μ.trim hτ.measurable_space_le),
  { exact sigma_finite_trim_mono _ (is_stopping_time.measurable_space_mono hσ hτ hσ_le_τ), },
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

lemma stopped_value_ae_eq_condexp_of_le'
  [(filter.at_top : filter ι).is_countably_generated] [locally_finite_order_bot ι]
  (h : martingale f ℱ μ) (hτ : is_stopping_time ℱ τ) (hσ : is_stopping_time ℱ σ) (hσ_le_τ : σ ≤ τ)
  (hτ_le : ∀ x, τ x ≤ n) [sigma_finite (μ.trim hσ.measurable_space_le)] :
  stopped_value f σ =ᵐ[μ] μ[stopped_value f τ | hσ.measurable_space] :=
begin
  haveI : sigma_finite (μ.trim hτ.measurable_space_le),
  { exact sigma_finite_trim_mono _ (is_stopping_time.measurable_space_mono hσ hτ hσ_le_τ), },
  refine h.stopped_value_ae_eq_condexp_of_le_of_countable_range hτ hσ hσ_le_τ hτ_le
    (set.finite.subset (set.finite_Iic n) (λ x hx, _)).countable
    (set.finite.subset (set.finite_Iic n) (λ x hx, _)).countable,
  { obtain ⟨y, rfl⟩ := hx,
    exact hτ_le y, },
  { obtain ⟨y, rfl⟩ := hx,
    exact (hσ_le_τ y).trans (hτ_le y), },
end

lemma stopped_value_ae_eq_condexp_of_le [countable ι]
  (h : martingale f ℱ μ) (hτ : is_stopping_time ℱ τ) (hσ : is_stopping_time ℱ σ)
  (hσ_le_τ : σ ≤ τ) (hτ_le : ∀ x, τ x ≤ n) [sigma_finite (μ.trim hσ.measurable_space_le)] :
  stopped_value f σ =ᵐ[μ] μ[stopped_value f τ | hσ.measurable_space] :=
begin
  haveI : sigma_finite (μ.trim hτ.measurable_space_le),
  { exact sigma_finite_trim_mono _ (is_stopping_time.measurable_space_mono hσ hτ hσ_le_τ), },
  exact h.stopped_value_ae_eq_condexp_of_le_of_countable_range hτ hσ hσ_le_τ hτ_le
    (set.to_countable _) (set.to_countable _),
end

end first_countable_topology

lemma condexp_stopped_value_stopping_time_ae_eq_restrict_le [countable ι]
  [locally_finite_order_bot ι] [measurable_space ι] [borel_space ι] [second_countable_topology ι]
  [measurable_space E] [borel_space E] [second_countable_topology E]
  (h : martingale f ℱ μ) (hf_prog : prog_measurable ℱ f)
  (hτ : is_stopping_time ℱ τ) (hσ : is_stopping_time ℱ σ)
  [sigma_finite (μ.trim hσ.measurable_space_le)] (hτ_le : ∀ x, τ x ≤ n) :
  μ[stopped_value f τ | hσ.measurable_space] =ᵐ[μ.restrict {x : Ω | τ x ≤ σ x}] stopped_value f τ :=
begin
  rw ae_eq_restrict_iff_indicator_ae_eq
    (hτ.measurable_space_le _ (hτ.measurable_set_le_stopping_time hσ)),
  swap, apply_instance,
  refine (condexp_indicator (integrable_stopped_value ι hτ h.integrable hτ_le)
    (hτ.measurable_set_stopping_time_le hσ)).symm.trans _,
  have h_int : integrable ({ω : Ω | τ ω ≤ σ ω}.indicator (stopped_value (λ (n : ι), f n) τ)) μ,
  { refine (integrable_stopped_value ι hτ h.integrable hτ_le).indicator _,
    exact hτ.measurable_space_le _ (hτ.measurable_set_le_stopping_time hσ), },
  have h_meas : ae_strongly_measurable' hσ.measurable_space
    ({ω : Ω | τ ω ≤ σ ω}.indicator (stopped_value (λ (n : ι), f n) τ)) μ,
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
  exact condexp_of_ae_strongly_measurable' hσ.measurable_space_le h_meas h_int,
end

/-- **Optional Sampling** theorem. If `τ` is a bounded stopping time and `σ` is another stopping
time, then the stopped value of a martingale `f` with respect to `min τ σ` is almost everywhere
equal to `μ[stopped_value f τ | hσ.measurable_space]`. -/
lemma stopped_value_min_ae_eq_condexp [countable ι] [locally_finite_order_bot ι]
  [measurable_space ι] [borel_space ι] [second_countable_topology ι]
  [measurable_space E] [borel_space E] [second_countable_topology E]
  [sigma_finite_filtration μ ℱ] (h : martingale f ℱ μ) (h_prog : prog_measurable ℱ f)
  (hτ : is_stopping_time ℱ τ) (hσ : is_stopping_time ℱ σ) {n : ι} (hτ_le : ∀ x, τ x ≤ n)
  [h_sf_min : sigma_finite (μ.trim (hτ.min hσ).measurable_space_le)] :
  stopped_value f (λ x, min (σ x) (τ x)) =ᵐ[μ] μ[stopped_value f τ | hσ.measurable_space] :=
begin
  have h_min_comm : (hτ.min hσ).measurable_space = (hσ.min hτ).measurable_space,
    by rw [is_stopping_time.measurable_space_min, is_stopping_time.measurable_space_min, inf_comm],
  haveI : sigma_finite (μ.trim (hσ.min hτ).measurable_space_le),
  { convert h_sf_min; { ext1 x, rw min_comm, }, },
  haveI : sigma_finite (μ.trim hτ.measurable_space_le),
  { have h_le : (hτ.min hσ).measurable_space ≤ hτ.measurable_space,
    { rw is_stopping_time.measurable_space_min,
      exact inf_le_left, },
    exact sigma_finite_trim_mono _ h_le, },
  haveI : sigma_finite (μ.trim hσ.measurable_space_le),
  { have h_le : (hτ.min hσ).measurable_space ≤ hσ.measurable_space,
    { rw is_stopping_time.measurable_space_min,
      exact inf_le_right, },
    exact sigma_finite_trim_mono _ h_le, },
  refine (h.stopped_value_ae_eq_condexp_of_le hτ (hσ.min hτ) (λ x, min_le_right _ _) hτ_le).trans _,
  refine ae_of_ae_restrict_of_ae_restrict_compl {x | σ x ≤ τ x} _ _,
  { exact condexp_min_stopping_time_ae_eq_restrict_le hσ hτ, },
  { suffices : μ[stopped_value f τ|(hσ.min hτ).measurable_space]
      =ᵐ[μ.restrict {x | τ x ≤ σ x}] μ[stopped_value f τ|hσ.measurable_space],
    { rw ae_restrict_iff' (hσ.measurable_space_le _ (hσ.measurable_set_le_stopping_time hτ).compl),
      rw [filter.eventually_eq, ae_restrict_iff'] at this,
      swap, { exact hτ.measurable_space_le _ (hτ.measurable_set_le_stopping_time hσ), },
      filter_upwards [this] with x hx hx_mem,
      simp only [set.mem_compl_eq, set.mem_set_of_eq, not_le] at hx_mem,
      exact hx hx_mem.le, },
    refine filter.eventually_eq.trans _
      ((condexp_min_stopping_time_ae_eq_restrict_le hτ hσ).trans _),
    { exact stopped_value f τ, },
    { rw h_min_comm, },
    { have h1 : μ[stopped_value f τ|hτ.measurable_space] = stopped_value f τ,
      { refine condexp_of_strongly_measurable hτ.measurable_space_le _ _,
        { refine measurable.strongly_measurable _,
          exact measurable_stopped_value h_prog hτ, },
        { exact integrable_stopped_value ι hτ h.integrable hτ_le, }, },
      rw h1,
      exact (condexp_stopped_value_stopping_time_ae_eq_restrict_le h h_prog hτ hσ hτ_le).symm, }, },
end

variables
/-- **Optional Sampling** theorem for martingales indexed by `ℕ`. If `τ` is a bounded stopping time
and `σ` is another stopping time, then the stopped value of a martingale `f` with respect to
`min τ σ` is almost everywhere equal to `μ[stopped_value f τ | hσ.measurable_space]`. -/
lemma stopped_value_min_ae_eq_condexp_nat {E}
  {𝒢 : filtration ℕ m} [sigma_finite_filtration μ 𝒢] {τ σ : Ω → ℕ}
  [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]
  [measurable_space E] [borel_space E] [second_countable_topology E]
  {f : ℕ → Ω → E} (h : martingale f 𝒢 μ) (hτ : is_stopping_time 𝒢 τ) (hσ : is_stopping_time 𝒢 σ)
  {n : ℕ} (hτ_le : ∀ x, τ x ≤ n)
  [h_sf_min : sigma_finite (μ.trim (hτ.min hσ).measurable_space_le)] :
  stopped_value f (λ x, min (σ x) (τ x)) =ᵐ[μ] μ[stopped_value f τ | hσ.measurable_space] :=
h.stopped_value_min_ae_eq_condexp h.adapted.prog_measurable_of_nat hτ hσ hτ_le

end martingale

end measure_theory
