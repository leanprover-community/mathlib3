/-
Copyright (c) 2022 Alex Kontorovich and Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/

import algebra.group.opposite
import analysis.normed_space.lp_space
import measure_theory.group.fundamental_domain
import measure_theory.integral.integral_eq_improper
import measure_theory.measure.haar
import topology.compact_open

/-!

-/

open measure_theory
open_locale measure_theory

@[to_additive ae_strongly_measurable_of_absolutely_continuous_add]
lemma ae_strongly_measurable_of_absolutely_continuous {α β : Type*} [measurable_space α]
  [topological_space β] {μ ν : measure α} (h : ν ≪ μ) (g : α → β)
  (hμ : ae_strongly_measurable g μ) : ae_strongly_measurable g ν :=
begin
  obtain ⟨g₁, hg₁, hg₁'⟩ := hμ,
  refine ⟨g₁, hg₁, h.ae_eq hg₁'⟩,
end

open_locale big_operators nnreal

noncomputable theory

open_locale topological_space


--- *** ADD to data.real.ennreal *** USELESS HERE
theorem ennreal.coe_le_of_le_to_nnreal {r : nnreal} {a : ennreal} (h : r ≤ a.to_nnreal) :
  (r : ennreal) ≤ a :=
begin
  by_cases ha : a = ⊤,
  { simp [ha], },
  rw ← ennreal.coe_to_nnreal ha,
  exact_mod_cast h,
end

--- *** ADD to data.real.ennreal *** USELESS HERE
theorem ennreal.le_to_nnreal_of_coe_le {r : nnreal} {a : ennreal} (h : (r : ennreal) ≤ a)
  (ha : a ≠ ⊤) : r ≤ a.to_nnreal := by rwa [← ennreal.coe_le_coe, ennreal.coe_to_nnreal ha]

--- *** ADD to data.real.ennreal *** USELESS HERE
theorem ennreal.eq_to_nnreal_of_coe_eq {a : nnreal} {b : ennreal} (h : (a : ennreal) = b) :
  a = b.to_nnreal := by convert congr_arg ennreal.to_nnreal h

-- *** ADD to analysis.normed.group.basic *** USELESS HERE
theorem nnnorm_sub_rev {E : Type*} [seminormed_add_comm_group E] (g h : E) :
∥g - h∥₊ = ∥h - g∥₊ :=
begin
  rw ← nnnorm_neg,
  congr,
  abel,
end

--- *** ADD measure_theory.integral.lebesgue *** USELESS HERE
theorem measure_theory.lintegral_sub_compl {α : Type*} {m : measurable_space α} {μ : measure α}
  {f : α → ennreal} {A : set α}  (hA : measurable_set A) (hf : ∫⁻ x in A, f x ∂μ < ⊤) :
  ∫⁻ (x : α) in Aᶜ, f x ∂μ = ∫⁻ (x : α), f x ∂μ - ∫⁻ (x : α) in A, f x ∂μ :=
begin
  nth_rewrite 1 ← measure_theory.lintegral_add_compl f hA,
  rw ennreal.add_sub_cancel_left hf.ne,
end

-- USELESS HERE, add elsewhere?
theorem ae_cover_finset (α : Type*) [measurable_space α] [measurable_singleton_class α] :
  measure_theory.ae_cover measure.count filter.at_top (coe : finset α → set α) :=
begin
  classical,
  refine ⟨ _, λ s, s.measurable_set⟩,
  filter_upwards,
  intros a,
  rw filter.eventually_at_top,
  use {a},
  intros b hb,
  apply hb,
  simp,
end

-- *** NOT USED move to measure_theory.measurable_space_def, after `measurable_singleton_class`
theorem measurable_set_of_countable {α : Type*} [measurable_space α]
  [measurable_singleton_class α] {A : set α} (hA : set.countable A) : measurable_set A :=
begin
  convert @measurable_set.bUnion _ _ _ has_singleton.singleton _ hA
    (λ b _,  measurable_singleton_class.measurable_set_singleton _),
  simp,
end

-- *** NOT USED move to measure_theory.measurable_space_def, after `measurable_singleton_class`
theorem measurable_set_of_encodable_singleton_class {α : Type*} [measurable_space α]
  [measurable_singleton_class α] [encodable α] (A : set α) : measurable_set A :=
 measurable_set_of_countable A.to_countable

--- *** NOT USED
theorem measurable_of_encodable_singleton_class {α : Type*} [measurable_space α]
  [measurable_singleton_class α] [encodable α] (f : α → ennreal) : measurable f :=
λ s hs, measurable_set_of_encodable_singleton_class _

-- NEVER USED PRed and reogranized maybe? 1/9/23
-- ** Make this like `lintegral_tendsto_of_countably_generated`, generalize to arbitrary `ae_cover`
theorem extracted_goal_from_extracted_goal {α : Type*} [measurable_space α]
  [measurable_singleton_class α] [encodable α] {f : α → ennreal}
  (hf : ∫⁻ (x : α), (f x) ∂measure.count < ⊤) : filter.tendsto (λ (s : finset α),
  ∫⁻ (x : α) in (s : set α)ᶜ, f x ∂measure.count) filter.at_top (𝓝 0) :=
begin
  have : filter.tendsto (λ (s : finset α),
    ∫⁻ (x : α), f x ∂measure.count - ∫⁻ (x : α) in (s : set α), f x ∂measure.count)
    filter.at_top (𝓝 0),
  { have hh := @tendsto_const_nhds ennreal (finset α) _ (∫⁻ (x : α), (f x) ∂measure.count)
      filter.at_top,
    have := (ae_cover_finset α).lintegral_tendsto_of_countably_generated
      (measurable_of_encodable_singleton_class _).ae_measurable,
    convert ennreal.tendsto.sub hh this (or.inl (hf.ne)),
    simp, },
  convert this,
  funext s,
  refine measure_theory.lintegral_sub_compl s.measurable_set _,
  refine lt_of_le_of_lt _ hf,
  convert measure_theory.lintegral_mono_set (_ : (s : set α) ⊆ set.univ); simp,
end
