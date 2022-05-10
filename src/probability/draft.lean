/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import probability.stopping

/-!
# Draft
-/

open_locale measure_theory
open topological_space

namespace measure_theory

section stopping

variables {α ι : Type*} {m : measurable_space α} {μ : measure α}
  [linear_order ι] {ℱ : filtration ι m} {τ σ : α → ι}

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

lemma strongly_measurable_stopped_value_of_le [topological_space E] {f : ι → α → E}
  [topological_space ι] [measurable_space ι] [borel_space ι] [order_topology ι]
  [second_countable_topology ι]
  (h : prog_measurable ℱ f) (hτ : is_stopping_time ℱ τ) {n : ι} (hτ_le : ∀ x, τ x ≤ n) :
  strongly_measurable[ℱ n] (stopped_value f τ) :=
begin
  have : stopped_value f τ = (λ (p : set.Iic n × α), f ↑(p.fst) p.snd) ∘ (λ x, (⟨τ x, hτ_le x⟩, x)),
  { ext1 x, simp only [stopped_value, function.comp_app, subtype.coe_mk], },
  rw this,
  refine strongly_measurable.comp_measurable (h n) _,
  exact (hτ.measurable_of_le hτ_le).subtype_mk.prod_mk measurable_id,
end

lemma measurable_stopped_value {f : ι → α → E}
  [topological_space ι] [measurable_space ι] [borel_space ι] [order_topology ι]
  [second_countable_topology ι]
  [topological_space E] [metrizable_space E] [measurable_space E] [borel_space E]
  (hf_prog : prog_measurable ℱ f) (hτ : is_stopping_time ℱ τ) :
  measurable[hτ.measurable_space] (stopped_value f τ) :=
begin
  have h_str_meas : ∀ i, strongly_measurable[ℱ i] (stopped_value f (λ x, min (τ x) i)),
    from λ i, strongly_measurable_stopped_value_of_le hf_prog (hτ.min_const i)
      (λ _, min_le_right _ _),
  intros t ht i,
  suffices : stopped_value f τ ⁻¹' t ∩ {x : α | τ x ≤ i}
      = stopped_value f (λ x, min (τ x) i) ⁻¹' t ∩ {x : α | τ x ≤ i},
    by { rw this, exact ((h_str_meas i).measurable ht).inter (hτ.measurable_set_le i), },
  ext1 x,
  simp only [stopped_value, set.mem_inter_eq, set.mem_preimage, set.mem_set_of_eq,
    and.congr_left_iff],
  intro h,
  rw min_eq_left h,
end

end stopping

end measure_theory
