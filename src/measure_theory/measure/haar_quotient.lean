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
# Haar quotient measure

In this file, we consider properties of fundamental domains and measures for the action of a
subgroup of a group `G` on `G` itself.

## Main results

* `measure_theory.is_fundamental_domain.smul_invariant_measure_map `: given a subgroup `Γ` of a
  topological group `G`, the pushforward to the coset space `G ⧸ Γ` of the restriction of a both
  left- and right-invariant measure on `G` to a fundamental domain `𝓕` is a `G`-invariant measure
  on `G ⧸ Γ`.

* `measure_theory.is_fundamental_domain.is_mul_left_invariant_map `: given a normal subgroup `Γ` of
  a topological group `G`, the pushforward to the quotient group `G ⧸ Γ` of the restriction of
  a both left- and right-invariant measure on `G` to a fundamental domain `𝓕` is a left-invariant
  measure on `G ⧸ Γ`.

Note that a group `G` with Haar measure that is both left and right invariant is called
**unimodular**.
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


theorem measure_theory.L1.tsum_eq_set_to_L1 {α : Type*} {E : Type*} [normed_add_comm_group E]
  {m : measurable_space α} [normed_space ℝ E] [complete_space E]
  (f : (Lp E 1 measure.count)) :
∑' (a : α), f a = (L1.set_to_L1 (dominated_fin_meas_additive_weighted_smul measure.count)) f :=
begin
  dsimp,

  sorry,
end



open_locale big_operators nnreal

noncomputable theory

def foo (f : ℝ → ℝ) (s : finset ℝ) : simple_func ℝ ℝ :=
  ∑ i in s, (simple_func.const ℝ (f i)).piecewise
  {i} (measurable_set_singleton i) (simple_func.const ℝ 0)


-- if
lemma something' {β : Type*} [partial_order β] {C : nnreal} (F : β → ℝ≥0) (hF₁ : monotone F)
(hF₂ : filter.tendsto F filter.at_top (nhds C))
  :
  filter.tendsto (λ (s : β), C- F s)
  (filter.at_top : filter (β)) (nhds (0))
 :=
begin

  sorry
end


open_locale topological_space

lemma tendsto_lintegral_count_compl_at_top_zero {α : Type*} [measurable_space α]
  [measurable_singleton_class α] {f : α → ℝ≥0} (hf : ∫⁻ a, f a ∂measure.count < ⊤) :
  filter.tendsto (λ (s : finset α), ∫⁻ a in (sᶜ : set α), f a ∂measure.count) filter.at_top (𝓝 0)
:=
begin
  rw measure_theory.lintegral_count at hf,
  convert ennreal.tendsto_tsum_compl_at_top_zero hf.ne using 1,
  ext1 s,
  rw [←lintegral_indicator _ s.measurable_set.compl, measure_theory.lintegral_count,
    ← tsum_subtype],
  refl,
end

--  *** Not needed???
-- theorem tendsto_zero_iff_nnnorm_tendsto_zero {α : Type*} {E : Type*} [semi_normed_add_comm_group E]
-- {f : α → E} {a : filter α} :
-- filter.tendsto f a (nhds 0) ↔ filter.tendsto (λ (e : α), ∥f e∥₊) a (nhds 0) :=
-- sorry

-- prove and add to mathlib analysis.normed.group.basic
theorem tendsto_iff_nnnorm_tendsto_zero {α : Type*} {E : Type*} [seminormed_add_comm_group E]
{f : α → E} {a : filter α} {b : E} :
filter.tendsto f a (nhds b) ↔ filter.tendsto (λ (e : α), ∥f e - b∥₊) a (nhds 0) :=
begin
  sorry,
end

-- lemma tendsto_Lp_count_compl_at_top_zero {α : Type*} [measurable_space α]
--   [measurable_singleton_class α] [encodable α]
--   {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [measurable_space E] [borel_space E]
--   [complete_space E] {p : ennreal} (f : Lp E p (measure.count : measure α)) :
--   --filter.tendsto  (filter.at_top : filter (finset α)) (nhds f)
--   -----***** FIX **** Or drop!? :)
--   filter.tendsto (λ (s : finset α), measure_theory.indicator_const_Lp p (s.measurable_set) )
--   filter.at_top (𝓝 0)
-- :=
-- begin
--   rw tendsto_zero_iff_nnnorm_tendsto_zero,
--   rw measure_theory.lintegral_count at hf,
--   convert ennreal.tendsto_tsum_compl_at_top_zero hf.ne using 1,
--   ext1 s,
--   rw [←lintegral_indicator _ s.measurable_set.compl, measure_theory.lintegral_count,
--     ← tsum_subtype],
--   refl,
-- end

-- map ennreal → real continuous at zero

-- *** ADD to measure_theory.function.l1_space
theorem measure_theory.L1.nnnorm_def {α : Type*} {β : Type*} {m : measurable_space α}
{μ : measure_theory.measure α} [normed_add_comm_group β] (f : ↥(measure_theory.Lp β 1 μ)) :
(∥f∥₊ : ennreal) = ∫⁻ (a : α), ∥f a∥₊ ∂μ := sorry


--- *** ADD to data.real.ennreal
theorem ennreal.coe_le_of_le_to_nnreal {r : nnreal} {a : ennreal} (h : r ≤ a.to_nnreal) :
  (r : ennreal) ≤ a :=
begin
  by_cases ha : a = ⊤,
  { simp [ha], },
  rw ← ennreal.coe_to_nnreal ha,
  exact_mod_cast h,
end


--- *** ADD to data.real.ennreal
theorem ennreal.le_to_nnreal_of_coe_le {r : nnreal} {a : ennreal} (h : (r : ennreal) ≤ a)
  (ha : a ≠ ⊤) : r ≤ a.to_nnreal := by rwa [← ennreal.coe_le_coe, ennreal.coe_to_nnreal ha]

example (x y : ℝ) (f : ℝ → ℝ ) : x = y → f x = f y :=
begin
  exact congr_arg (λ (x : ℝ), f x),
end

--- *** ADD to data.real.ennreal
theorem ennreal.eq_to_nnreal_of_coe_eq {a : nnreal} {b : ennreal} (h : (a : ennreal) = b) :
  a = b.to_nnreal := by convert congr_arg ennreal.to_nnreal h

-- *** ADD to analysis.normed.group.basic
theorem nnnorm_sub_rev {E : Type*} [seminormed_add_comm_group E] (g h : E) :
∥g - h∥₊ = ∥h - g∥₊ :=
begin
  rw ← nnnorm_neg,
  congr,
  abel,
end

-- exists in mathlib
-- theorem ennreal.add_sub_cancel_left {a b : ennreal} (ha : a ≠ ⊤) :
-- a + b - a = b := sorry

--- *** ADD measure_theory.integral.lebesgue
theorem measure_theory.lintegral_sub_compl {α : Type*} {m : measurable_space α} {μ : measure α}
  {f : α → ennreal} {A : set α}  (hA : measurable_set A) (hf : ∫⁻ x in A, f x ∂μ < ⊤) :
  ∫⁻ (x : α) in Aᶜ, f x ∂μ = ∫⁻ (x : α), f x ∂μ - ∫⁻ (x : α) in A, f x ∂μ :=
begin
  nth_rewrite 1 ← measure_theory.lintegral_add_compl f hA,
  rw ennreal.add_sub_cancel_left hf.ne,
end


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

-- move to measure_theory.measurable_space_def, after `measurable_singleton_class`
theorem measurable_set_of_countable {α : Type*} [measurable_space α]
  [measurable_singleton_class α] {A : set α} (hA : set.countable A) : measurable_set A :=
begin
  convert @measurable_set.bUnion _ _ _ has_singleton.singleton _ hA
    (λ b _,  measurable_singleton_class.measurable_set_singleton _),
  simp,
end

-- move to measure_theory.measurable_space_def, after `measurable_singleton_class`
theorem measurable_set_of_encodable_singleton_class {α : Type*} [measurable_space α]
  [measurable_singleton_class α] [encodable α] (A : set α) : measurable_set A :=
 measurable_set_of_countable A.to_countable


theorem measurable_of_encodable_singleton_class {α : Type*} [measurable_space α]
  [measurable_singleton_class α] [encodable α] (f : α → ennreal) : measurable f :=
λ s hs, measurable_set_of_encodable_singleton_class _

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

theorem extracted_goal_from_next_theorem {α : Type*} {E : Type*}
  [measurable_space α]
  [measurable_singleton_class α]
  [encodable α]
  [normed_add_comm_group E]
  [normed_space ℝ E]
  [measurable_space E]
  [borel_space E]
  [complete_space E]
  {f : α → E}
  (hf : integrable f measure.count)
  (hf' : mem_ℒp f 1 measure.count)
  (hF : ∀ (s : finset α), mem_ℒp ((s:set α).indicator f) 1 measure.count)
  (hh : ∀ (s : finset α), L1.integral_clm ((hF s).to_Lp _) = s.sum f)
  :
  filter.tendsto (λ (s : finset α), s.sum f) filter.at_top
  (𝓝 (L1.integral_clm (integrable.to_L1 f hf))) :=
begin
  rw  tendsto_iff_nnnorm_tendsto_zero,

  have : filter.tendsto (λ (s : finset α),
    ∫⁻ x in (s : set α)ᶜ, nnnorm (f x) ∂measure.count )
    filter.at_top (𝓝 0),
  {
    exact extracted_goal_from_extracted_goal hf.2,
  },

  convert tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds)
    ((ennreal.tendsto_to_nnreal ennreal.zero_ne_top).comp this) bot_le _ using 1,

  intros s,
  simp only [coe_nnnorm, function.comp_app, ←hh s],
  rw ←continuous_linear_map.map_sub,

  -- FIX NAMING CONVENTION `continuous_linear_map.le_op_nnnorm_of_le`
  refine le_trans (continuous_linear_map.le_op_nnnorm _ _) _,
--  have := continuous_linear_map.le_op_norm_of_le (L1.integral_clm : ),

--  have h : ∥L1.integral_clm∥₊ ≤ 1,
--  {
--    have := measure_theory.L1.norm_Integral_le_one,
--  },

--  refine le_trans (mul_le_of_le_one_left bot_le measure_theory.L1.norm_Integral_le_one) _,
  convert mul_le_of_le_one_left (bot_le : (0 : nnreal) ≤ _) _,

  {
    symmetry,
    apply ennreal.eq_to_nnreal_of_coe_eq,
    rw measure_theory.L1.nnnorm_def,
    rw ← lintegral_indicator,
    {
      rw lintegral_congr_ae,
  --    have := mem_ℒp.coe_fn_to_Lp (hF s),
  --   have := measure_theory.Lp.coe_fn_sub ((hF s).to_Lp _) (hf.to_L1 _),
      have := integrable.coe_fn_to_L1 hf,
      filter_upwards [mem_ℒp.coe_fn_to_Lp (hF s), Lp.coe_fn_sub ((hF s).to_Lp _) (hf.to_L1 _),
        hf.coe_fn_to_L1] with x hx₁ hx₂ hx₃,

      rw hx₂,
      dsimp,
      rw hx₁,
      rw hx₃,
      rw nnnorm_sub,

      transitivity (nnnorm ((f - (s : set α).indicator f) x) : ennreal),
      { refl, },


      rw ← set.indicator_compl (s : set α) f,
      rw nnnorm_indicator_eq_indicator_nnnorm ,
      simp,
    },
    apply measurable_set.compl,
    exact finset.measurable_set s,
   -- rw hx,
    -- set.indicator_compl
  },

  exact measure_theory.L1.norm_Integral_le_one,
end

--- finite sum version of `measure_theory.Lp.coe_fn_add` ???
theorem something14 {α : Type*} {E : Type*}
  [measurable_space α]
  [measurable_singleton_class α]
  [encodable α]
  [normed_add_comm_group E]
  [normed_space ℝ E]
  [measurable_space E]
  [borel_space E]
  [complete_space E]
  {p : ennreal} {μ : measure_theory.measure α}
  {f : α → ↥(measure_theory.Lp E p μ)}
  (s : finset α)
  :
  ⇑(∑ (i : α) in s, f i) =ᵐ[μ] ∑ (i : α) in s, ⇑(f i) :=
begin
  -- induct on cardinality of s?
  sorry,
end

--- *** used in next theorem
theorem something13 {α : Type*} {E : Type*} [measurable_space α]
  [measurable_singleton_class α]
  [encodable α]
  [normed_add_comm_group E]
  [normed_space ℝ E]
  [measurable_space E]
  [borel_space E]
  [complete_space E]
  {f : α → E}
  (hf : integrable f measure.count)
  (hf' : mem_ℒp f 1 measure.count)
  (hF : ∀ (s : finset α), mem_ℒp ((s : set α).indicator f) 1 measure.count)
  (s : finset α)
  (single_not_top : ∀ (i : α), (measure.count : measure α) {i} ≠ ⊤)
  :
   ∫ (a : α), (∑ i in s,
      (indicator_const_Lp 1 (measurable_set_singleton i) (single_not_top i) (f i))) a ∂measure.count
      = s.sum f :=
begin
  have : (⇑(∑ (i : α) in s, indicator_const_Lp 1 (measurable_set_singleton i) (single_not_top i)
    (f i)) : α → E) =ᵐ[measure.count] ∑ (i : α) in s, (indicator_const_Lp 1
    (measurable_set_singleton i) (single_not_top i) (f i) : α → E) := something14 s,
  rw integral_congr_ae this,
  simp only [finset.sum_apply],
  rw measure_theory.integral_finset_sum,
  { rw finset.sum_congr rfl,
    intros i hi,
    have : indicator_const_Lp 1 (measurable_set_singleton i) (single_not_top i) (f i)
      =ᵐ[measure.count] _ :=  indicator_const_Lp_coe_fn,
    rw integral_congr_ae this,
    simp [measure_theory.measure.count_singleton],
  },

  {
    intros i hi,
    sorry,
  },

end

-- *** Garbage ***
theorem something12 {α : Type*} {E : Type*}
  [measurable_space α]
  [measurable_singleton_class α]
  [encodable α]
  [normed_add_comm_group E]
  [normed_space ℝ E]
  [measurable_space E]
  [borel_space E]
  [complete_space E]
  {f : α → E}
  (hf : integrable f measure.count)
  (hf : mem_ℒp f 1 measure.count)
  (hF : ∀ (s : finset α), mem_ℒp ((s : set α).indicator f) 1 measure.count)
  (s : finset α)
  :
  ∫ (a : α), (mem_ℒp.to_Lp _ (hF s)) a ∂measure.count = s.sum f :=
begin
  have single_not_top : ∀ i, measure.count ({i} : set α) ≠ ⊤,
  { intros i,
    rw measure_theory.measure.count_singleton,
    exact ennreal.one_ne_top ,
  },
  have : (⇑(∑ (i : α) in s, indicator_const_Lp 1 (measurable_set_singleton i) (single_not_top i)
    (f i)) : α → E) =ᵐ[measure.count] ∑ (i : α) in s, (indicator_const_Lp 1
    (measurable_set_singleton i) (single_not_top i) (f i) : α → E),
  {

    sorry,
  },
  have := integral_congr_ae this,
  rw integral_congr_ae this,
  simp only [finset.sum_apply],
  rw measure_theory.integral_finset_sum,
  rw finset.sum_congr rfl,
  intros i hi,

  have : indicator_const_Lp 1 (measurable_set_singleton i) (single_not_top i) (f i)
    =ᵐ[measure.count] _ :=  indicator_const_Lp_coe_fn,
  rw integral_congr_ae this,

  simp [measure_theory.measure.count_singleton],

  {
    sorry,
  },

  sorry,
end

theorem measure_theory.integral_count {α : Type*} [measurable_space α]
  [measurable_singleton_class α] [encodable α]
  {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [measurable_space E] [borel_space E]
  [complete_space E] {f : α → E} (hf : integrable f measure.count)  :
∫ (a : α), f a ∂measure.count = ∑' (a : α), f a :=
begin
  rw integral_eq f hf,
  rw L1.integral_eq,
  have hf' := mem_ℒp_one_iff_integrable.mpr hf,
  --have : summable f := sorry,
  symmetry,
  apply has_sum.tsum_eq,
  dsimp [has_sum],
  have hF : ∀ s : finset α, mem_ℒp ((s : set α).indicator f) 1 measure.count := λ s,
    measure_theory.mem_ℒp.indicator (finset.measurable_set s) hf',
  let F : finset α → Lp E 1 (measure.count : measure α) := λ s, (hF s).to_Lp _,
  have hh : ∀ s : finset α, L1.integral_clm (F s) = s.sum f,
  {
    intros s,
    rw ←  measure_theory.L1.integral_eq,
    have single_not_top : ∀ i, measure.count ({i} : set α) ≠ ⊤,
    {

      intros i,
      rw measure_theory.measure.count_singleton,
      exact ennreal.one_ne_top ,
    },
    let g : Lp E 1 (measure.count : measure α) := ∑ i in s,
      (indicator_const_Lp 1 (measurable_set_singleton i) (single_not_top i) (f i)),
    have : (F s : α → E) = g,
    {
      ext x,
      dsimp [F, g],
      by_cases hx : x ∈ s,
      {
        sorry,
      },
      sorry,
    },
    rw measure_theory.L1.integral_eq_integral,
    rw this,
    dsimp [g],
    refine something13 hf hf' hF  _ _, },
  refine extracted_goal_from_next_theorem _ hf' hF hh,
end

-- #exit

      /-
      ext i,
      simp only [option.mem_def, ennreal.some_eq_coe, ennreal.zero_eq_coe],
      by_cases hi : i = 0,
      {
        simp only [hi, ennreal.coe_zero, eq_self_iff_true, iff_true],
        rw measure_theory.measure.count_eq_zero_iff,
        simp only [set.compl_empty_iff],
        ext x,
        simp only [set.mem_set_of_eq, set.mem_univ, iff_true],
        by_cases hx : x ∈ s,
        {
          --simp [hx],
          sorry,
        },


        sorry,
      },
      {
        --push_neg at hi,
--        simp [hi],
        sorry,
      },




      --dsimp [F, g],
-/
      -- ALEX HOMEWORK
      --sorry,

-- open_locale ennreal
-- /-- playing with proof of `lintegral_supr'` -/
-- theorem lintegral_supr'' {α : Type*}  {m : measurable_space α}
--   {μ : measure_theory.measure α} {f : ℕ → α → ℝ≥0∞} (hf : ∀n, ae_measurable (f n) μ)
--   (h_mono : ∀ᵐ x ∂μ, monotone (λ n, f n x)) :
--   (∫⁻ a, ⨆n, f n a ∂μ) = (⨆n, ∫⁻ a, f n a ∂μ) :=
-- begin
--   simp_rw ←supr_apply,
--   let p : α → (ℕ → ℝ≥0∞) → Prop := λ x, monotone,
--   have hp : ∀ᵐ x ∂μ, p x (λ i, f i x), from h_mono,
--   have h_ae_seq_mono : monotone (ae_seq hf p),
--   { intros n m hnm x,
--     by_cases hx : x ∈ ae_seq_set hf p,
--     { exact ae_seq.prop_of_mem_ae_seq_set hf hx hnm, },
--     { simp only [ae_seq, hx, if_false],
--       exact le_rfl, }, },
--   rw lintegral_congr_ae (ae_seq.supr hf hp).symm,
--   simp_rw supr_apply,
--   rw @lintegral_supr _ _ μ _ (ae_seq.measurable hf p) h_ae_seq_mono,
--   congr,
--   exact funext (λ n, lintegral_congr_ae (ae_seq.ae_seq_n_eq_fun_n_ae hf hp n)),
-- end


/-- ALREADY PR'ed to mathlib! -/
lemma lintegral_tsum' {α : Type*} {β : Type*} {m : measurable_space α}
  {μ : measure_theory.measure α} [countable β] {f : β → α → ennreal} (hf : ∀i, ae_measurable (f i) μ) :
  ∫⁻ a, ∑' i, f i a ∂μ = ∑' i, ∫⁻ a, f i a ∂μ := sorry


--- remind me, why not `measure_theory.integral_integral` and
---- tsum as integral
/-- THIS IS WHERE WE STOPPED ON 11/2/22 -/
lemma measure_theory.integral_tsum {α : Type*} {β : Type*} {m : measurable_space α}
  {μ : measure_theory.measure α} [encodable β] {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  [measurable_space E] [borel_space E] [complete_space E]
  {f : β → α → E}
  (hf : ∀ (i : β), ae_strongly_measurable (f i) μ) -- (hf : ∀ (i : β), ae_measurable (f i) μ)
  (hf' : summable (λ (i : β), ∫⁻ (a : α), ∥f i a∥₊ ∂μ)) :
  ∫ (a : α), (∑' (i : β), f i a) ∂μ = ∑' (i : β), ∫ (a : α), f i a ∂μ :=
begin
  have hhh : ∀ᵐ (a : α) ∂μ, summable (λ (n : β), (∥f n a∥₊ : ℝ)),
  {
    have := ae_lt_top ,
    have := hf'.has_sum,
    rw ← lintegral_tsum' at hf',
    change has_finite_integral _ _ at hf',
    sorry,
  },
  convert (measure_theory.has_sum_integral_of_dominated_convergence _ hf _ _ _ _).tsum_eq.symm,
  { exact λ i a, ∥f i a∥₊, },
  { intros n,
    filter_upwards with x,
    refl, },
  { exact hhh, },
  {
    dsimp [integrable],
    split,
    { sorry, },
    {
      dsimp [has_finite_integral],
      have : ∫⁻ (a : α), ∑' (n : β), ∥f n a∥₊ ∂μ < ⊤,
      {
        rw lintegral_tsum',
        sorry, --exact hf', -- HOMEWORK
        exact_mod_cast λ i, (hf i).ae_measurable.nnnorm,
      },
      convert this,
      ext1 a,
      sorry, --- HOMEWORK
    },
  },
  { filter_upwards [hhh] with x hx,
    exact (summable_of_summable_norm hx).has_sum, },
end

#exit

open_locale ennreal

open measure_theory

-- move to facts about integrable functions
lemma integrable.mul_ℒ_infinity  {G : Type*} {E : Type*} [normed_ring E] [normed_algebra ℝ E]
  [measurable_space E] [borel_space E] [has_measurable_mul₂ E] [measurable_space G]
  {μ : measure G}
  (f : G → E)
  (f_ℒ_1 : integrable f μ)
  (g : G → E)
  (g_measurable : ae_strongly_measurable g μ)
  (g_ℒ_infinity : ess_sup (λ x, (∥g x∥₊ : ℝ≥0∞)) μ < ∞) :
  integrable (λ (x : G), f x * g x) μ :=
begin
  let s : set ℝ≥0∞ := {a : ℝ≥0∞ | μ {x : G | a < (λ (x : G), ↑∥g x∥₊) x} = 0},
  have : ess_sup (λ x, (∥g x∥₊ : ℝ≥0∞)) μ = Inf s := ess_sup_eq_Inf _ _,
  obtain ⟨a₀, has : μ _ = 0, ha₀⟩ : ∃ (a : ℝ≥0∞) (H : a ∈ s), a < ⊤,
  { rw ← Inf_lt_iff,
    rw ← ess_sup_eq_Inf,
    exact g_ℒ_infinity },
  rw ennreal.lt_iff_exists_coe at ha₀,
  obtain ⟨a, rfl, -⟩ := ha₀,
  rw integrable at f_ℒ_1 ⊢,
  rw measure_theory.has_finite_integral_iff_norm at f_ℒ_1 ⊢,
  refine ⟨f_ℒ_1.1.mul g_measurable, _⟩,
  calc ∫⁻ (x : G), ennreal.of_real (∥f x * g x∥) ∂μ ≤
    ∫⁻ (x : G), ennreal.of_real (∥f x∥ * ∥g x∥) ∂μ : _
    ... ≤  ∫⁻ (x : G), ennreal.of_real (∥f x∥ * a) ∂μ : _
    ... =  ∫⁻ (x : G), (ennreal.of_real (∥f x∥) * a) ∂μ : _
    ... = ∫⁻ (x : G), ennreal.of_real (∥f x∥) ∂μ * a : _
    ... < ⊤ : _ ,
  { mono,
    { exact rfl.le, },
    { intros x,
      apply ennreal.of_real_le_of_real,
      exact norm_mul_le _ _, }, },
  { apply measure_theory.lintegral_mono_ae,
    rw ← compl_mem_ae_iff at has,
    filter_upwards [has] with x hx,
    apply ennreal.of_real_le_of_real,
    refine mul_le_mul rfl.le _ (norm_nonneg _) (norm_nonneg _),
    exact_mod_cast le_of_not_lt hx },
  { congr,
    ext1 x,
    rw ennreal.of_real_mul,
    { simp },
    { exact norm_nonneg _ } },
  { refine measure_theory.lintegral_mul_const'' _ (ae_strongly_measurable.ae_measurable _),
    exact (ennreal.continuous_of_real.comp continuous_norm).comp_ae_strongly_measurable f_ℒ_1.1 },
  { apply ennreal.mul_lt_top f_ℒ_1.2.ne,
    simp, }
end

open set measure_theory topological_space measure_theory.measure
open_locale pointwise nnreal

variables {G : Type*} [group G] [measurable_space G] [topological_space G]
  [topological_group G] [borel_space G]
  (μ : measure G)
  (Γ : subgroup G)

/-- Given a subgroup `Γ` of `G` and a right invariant measure `μ` on `G`, the measure is also
  invariant under the action of `Γ` on `G` by **right** multiplication. -/
@[to_additive "Given a subgroup `Γ` of an additive group `G` and a right invariant measure `μ` on
  `G`, the measure is also invariant under the action of `Γ` on `G` by **right** addition."]
instance subgroup.smul_invariant_measure [μ.is_mul_right_invariant] :
  smul_invariant_measure Γ.opposite G μ :=
{ measure_preimage_smul :=
begin
  rintros ⟨c, hc⟩ s hs,
  dsimp [(•)],
  refine measure_preimage_mul_right μ (mul_opposite.unop c) s,
end}

variables {Γ} {μ}

/-- Measurability of the action of the topological group `G` on the left-coset space `G/Γ`. -/
@[to_additive "Measurability of the action of the additive topological group `G` on the left-coset
  space `G/Γ`."]
instance quotient_group.has_measurable_smul [measurable_space (G ⧸ Γ)] [borel_space (G ⧸ Γ)] :
  has_measurable_smul G (G ⧸ Γ) :=
{ measurable_const_smul := λ g, (continuous_const_smul g).measurable,
  measurable_smul_const := λ x, (quotient_group.continuous_smul₁ x).measurable }

variables {𝓕 : set G} (h𝓕 : is_fundamental_domain Γ.opposite 𝓕 μ)
include h𝓕

variables [countable Γ] [measurable_space (G ⧸ Γ)] [borel_space (G ⧸ Γ)]

/-- The pushforward to the coset space `G ⧸ Γ` of the restriction of a both left- and right-
  invariant measure on `G` to a fundamental domain `𝓕` is a `G`-invariant measure on `G ⧸ Γ`. -/
@[to_additive "The pushforward to the coset space `G ⧸ Γ` of the restriction of a both left- and
  right-invariant measure on an additive topological group `G` to a fundamental domain `𝓕` is a
  `G`-invariant measure on `G ⧸ Γ`."]
lemma measure_theory.is_fundamental_domain.smul_invariant_measure_map
  [μ.is_mul_left_invariant] [μ.is_mul_right_invariant] :
  smul_invariant_measure G (G ⧸ Γ) (measure.map quotient_group.mk (μ.restrict 𝓕)) :=
{ measure_preimage_smul :=
  begin
    let π : G → G ⧸ Γ := quotient_group.mk,
    have meas_π : measurable π :=
      continuous_quotient_mk.measurable,
    have 𝓕meas : null_measurable_set 𝓕 μ := h𝓕.null_measurable_set,
    intros g A hA,
    have meas_πA : measurable_set (π ⁻¹' A) := measurable_set_preimage meas_π hA,
    rw [measure.map_apply meas_π hA,
      measure.map_apply meas_π (measurable_set_preimage (measurable_const_smul g) hA),
      measure.restrict_apply₀' 𝓕meas, measure.restrict_apply₀' 𝓕meas],
    set π_preA := π ⁻¹' A,
    have : (quotient_group.mk ⁻¹' ((λ (x : G ⧸ Γ), g • x) ⁻¹' A)) = has_mul.mul g ⁻¹' π_preA,
    { ext1, simp },
    rw this,
    have : μ (has_mul.mul g ⁻¹' π_preA ∩ 𝓕) = μ (π_preA ∩ has_mul.mul (g⁻¹) ⁻¹' 𝓕),
    { transitivity μ (has_mul.mul g ⁻¹' (π_preA ∩ has_mul.mul g⁻¹ ⁻¹' 𝓕)),
      { rw preimage_inter,
        congr,
        rw [← preimage_comp, comp_mul_left, mul_left_inv],
        ext,
        simp, },
      rw measure_preimage_mul, },
    rw this,
    haveI : smul_invariant_measure G G μ := ⟨λ c s hs, measure_preimage_mul μ c s⟩,
    -- Lean can generate the next instance but it has no additive version of the autogenerated proof
    haveI : smul_comm_class G Γ.opposite G := ⟨λ a b c, (mul_assoc _ _ _).symm⟩,
    have h𝓕_translate_fundom : is_fundamental_domain Γ.opposite (g • 𝓕) μ := h𝓕.smul_of_comm g,
    rw [h𝓕.measure_set_eq h𝓕_translate_fundom meas_πA, ← preimage_smul_inv], refl,
    rintros ⟨γ, γ_in_Γ⟩,
    ext,
    have : π (x * (mul_opposite.unop γ)) = π (x) := by simpa [quotient_group.eq'] using γ_in_Γ,
    simp [(•), this],
  end }

/-- Assuming `Γ` is a normal subgroup of a topological group `G`, the pushforward to the quotient
  group `G ⧸ Γ` of the restriction of a both left- and right-invariant measure on `G` to a
  fundamental domain `𝓕` is a left-invariant measure on `G ⧸ Γ`. -/
@[to_additive "Assuming `Γ` is a normal subgroup of an additive topological group `G`, the
  pushforward to the quotient group `G ⧸ Γ` of the restriction of a both left- and right-invariant
  measure on `G` to a fundamental domain `𝓕` is a left-invariant measure on `G ⧸ Γ`."]
lemma measure_theory.is_fundamental_domain.is_mul_left_invariant_map [subgroup.normal Γ]
  [μ.is_mul_left_invariant] [μ.is_mul_right_invariant] :
  (measure.map (quotient_group.mk' Γ) (μ.restrict 𝓕)).is_mul_left_invariant :=
{ map_mul_left_eq_self := begin
    intros x,
    apply measure.ext,
    intros A hA,
    obtain ⟨x₁, _⟩ := @quotient.exists_rep _ (quotient_group.left_rel Γ) x,
    haveI := h𝓕.smul_invariant_measure_map,
    convert measure_preimage_smul x₁ ((measure.map quotient_group.mk) (μ.restrict 𝓕)) A using 1,
    rw [← h, measure.map_apply],
    { refl, },
    { exact measurable_const_mul _, },
    { exact hA, },
  end }

variables [t2_space (G ⧸ Γ)] [second_countable_topology (G ⧸ Γ)] (K : positive_compacts (G ⧸ Γ))

/-- Given a normal subgroup `Γ` of a topological group `G` with Haar measure `μ`, which is also
  right-invariant, and a finite volume fundamental domain `𝓕`, the pushforward to the quotient
  group `G ⧸ Γ` of the restriction of `μ` to `𝓕` is a multiple of Haar measure on `G ⧸ Γ`. -/
@[to_additive "Given a normal subgroup `Γ` of an additive topological group `G` with Haar measure
  `μ`, which is also right-invariant, and a finite volume fundamental domain `𝓕`, the pushforward
  to the quotient group `G ⧸ Γ` of the restriction of `μ` to `𝓕` is a multiple of Haar measure on
  `G ⧸ Γ`."]
lemma measure_theory.is_fundamental_domain.map_restrict_quotient [subgroup.normal Γ]
  [measure_theory.measure.is_haar_measure μ] [μ.is_mul_right_invariant]
  (h𝓕_finite : μ 𝓕 < ⊤) : measure.map (quotient_group.mk' Γ) (μ.restrict 𝓕)
  = (μ (𝓕 ∩ (quotient_group.mk' Γ) ⁻¹' K)) • (measure_theory.measure.haar_measure K) :=
begin
  let π : G →* G ⧸ Γ := quotient_group.mk' Γ,
  have meas_π : measurable π := continuous_quotient_mk.measurable,
  have 𝓕meas : null_measurable_set 𝓕 μ := h𝓕.null_measurable_set,
  haveI : is_finite_measure (μ.restrict 𝓕) :=
    ⟨by { rw [measure.restrict_apply₀' 𝓕meas, univ_inter], exact h𝓕_finite }⟩,
  -- the measure is left-invariant, so by the uniqueness of Haar measure it's enough to show that
  -- it has the stated size on the reference compact set `K`.
  haveI : (measure.map (quotient_group.mk' Γ) (μ.restrict 𝓕)).is_mul_left_invariant :=
    h𝓕.is_mul_left_invariant_map,
  rw [measure.haar_measure_unique (measure.map (quotient_group.mk' Γ) (μ.restrict 𝓕)) K,
    measure.map_apply meas_π, measure.restrict_apply₀' 𝓕meas, inter_comm],
  exact K.is_compact.measurable_set,
end







---------------------------- UNFOLDING TRICK ---------------

open_locale big_operators ennreal

-- theorem disjoint.inter {α : Type*} {s t : set α} (u : set α) (h : disjoint s t) :
-- disjoint (u ∩ s) (u ∩ t) := by apply_rules [disjoint.inter_right', disjoint.inter_left']

-- theorem disjoint.inter' {α : Type*} {s t : set α} (u : set α) (h : disjoint s t) :
-- disjoint (s ∩ u) (t ∩ u) := by apply_rules [disjoint.inter_left, disjoint.inter_right]


/-
-- see if this exists in fundamental domain
lemma integral_Union {ι : Type*} [encodable ι] {s : ι → set ℝ } (f : ℝ  → ℂ )
  (hm : ∀ i, measurable_set (s i)) (hd : pairwise (disjoint on s)) (hfi : integrable f  ) :
  (∫ a in (⋃ n, s n), f a ) = ∑' n, ∫ a in s n, f a  :=
sorry
-/

local notation `μ_𝓕` := measure.map (@quotient_group.mk G _ Γ) (μ.restrict 𝓕)

@[simp] lemma subgroup_mem_opposite_iff (γ : Gᵐᵒᵖ) : γ ∈ Γ.opposite ↔ mul_opposite.unop γ ∈ Γ :=
by simp [subgroup.opposite]



@[to_additive]
lemma mul_ess_sup_of_g [μ.is_mul_left_invariant] [μ.is_mul_right_invariant]
  (g : G ⧸ Γ → ℝ≥0∞) (g_measurable : ae_measurable g μ_𝓕) :
  ess_sup g μ_𝓕 = ess_sup (λ (x : G), g x) μ :=
begin
  have hπ : measurable (quotient_group.mk : G → G ⧸ Γ) := continuous_quotient_mk.measurable,
  rw ess_sup_map_measure g_measurable hπ.ae_measurable,
  refine h𝓕.ess_sup_measure_restrict _,
  rintros ⟨γ, hγ⟩ x,
  dsimp,
  congr' 1,
  exact quotient_group.mk_mul_of_mem x (mul_opposite.unop γ) hγ,
end

open_locale measure_theory

@[to_additive]
lemma _root_.measure_theory.is_fundamental_domain.absolutely_continuous_map
  [μ.is_mul_right_invariant] :
  map (quotient_group.mk : G → G ⧸ Γ) μ ≪ map (quotient_group.mk : G → G ⧸ Γ) (μ.restrict 𝓕) :=
begin
  set π : G → G ⧸ Γ := quotient_group.mk,
  have meas_π : measurable π := continuous_quotient_mk.measurable,
  apply measure_theory.measure.absolutely_continuous.mk,
  intros s s_meas hs,
  rw map_apply meas_π s_meas at hs ⊢,
  apply h𝓕.measure_zero_of_invariant _ hs,
  intros γ g hg,
  rw mem_preimage at hg ⊢,
  convert hg using 1,
  exact quotient_group.mk_mul_of_mem g (mul_opposite.unop γ) γ.2,
end

/-- This is the "unfolding" trick -/
@[to_additive]
lemma mul_unfolding_trick [μ.is_mul_left_invariant] [μ.is_mul_right_invariant]
  {f : G → ℂ}
  (f_summable: ∀ x : G, summable (λ (γ : Γ.opposite), f (γ⁻¹ • x))) -- NEEDED??
  (f_ℒ_1 : integrable f μ)
  {g : G ⧸ Γ → ℂ}
  (hg : ae_strongly_measurable g μ_𝓕)
  (g_ℒ_infinity : ess_sup (λ x, ↑∥g x∥₊) μ_𝓕 < ∞)
  {F : G ⧸ Γ → ℂ}
  (F_ae_measurable : ae_strongly_measurable F μ_𝓕) -- NEEDED??
  (hFf : ∀ (x : G), F (x : G ⧸ Γ) = ∑' (γ : Γ.opposite), f(γ • x)) :
  ∫ (x : G), f x * g (x : G ⧸ Γ) ∂μ = ∫ (x : G ⧸ Γ), F x * g x ∂μ_𝓕 :=
begin
--  set F : G ⧸ Γ → ℂ :=  λ x , ∑' (γ : Γ.opposite), f(γ • x)) ,
  have hFf' : ∀ (x : G), F (x : G ⧸ Γ) = ∑' (γ : Γ.opposite), f(γ⁻¹ • x),
  { intros x,
    rw hFf x,
    exact ((equiv.inv (Γ.opposite)).tsum_eq  (λ γ, f(γ • x))).symm, },
  let π : G → G ⧸ Γ := quotient_group.mk,
  have meas_π : measurable π := continuous_quotient_mk.measurable,
  rw integral_map meas_π.ae_measurable,
  have : ∀ (x : G), F (x : G ⧸ Γ) * g (x) = ∑' (γ : Γ.opposite), f (γ⁻¹ • x) * g (x),
  { intros x,
    rw hFf' x,
    convert (@tsum_smul_const _ Γ.opposite _ _ _ _ _ _ _ (λ γ, f (γ⁻¹ • x)) _ (g x) _).symm using 1,
    exact f_summable x, },
  refine eq.trans _ (integral_congr_ae (filter.eventually_of_forall this)).symm,
  haveI : encodable Γ.opposite := sorry,
  rw measure_theory.integral_tsum, --- WILL NEED MORE ASSUMPTIONS TO BE SATISFIED HERE
  haveI := h𝓕.smul_invariant_measure_map,
--  have := h𝓕.set_integral_eq_tsum (λ x, f x * g x) univ _,
  convert h𝓕.set_integral_eq_tsum (λ x, f x * g x) univ _,
  { simp, },
  { ext1 γ,
    simp only [smul_set_univ, univ_inter],
    congr,
    ext1 x,
    have : g ↑(γ⁻¹ • x) = g x,
    { obtain ⟨γ₀, hγ₀⟩ := γ,
      congr' 1,
      simpa [quotient_group.eq, (•)] using hγ₀, },
    rw this, },
  { refine integrable.mul_ℒ_infinity f _ (λ x : G, g (x : G ⧸ Γ)) _ _,
    { rw measure.restrict_univ,
      exact f_ℒ_1 },
    { rw measure.restrict_univ,
      exact (ae_strongly_measurable_of_absolutely_continuous h𝓕.absolutely_continuous_map _
        hg).comp_measurable meas_π, },
    { have hg' : ae_strongly_measurable (λ x, ↑∥g x∥₊) μ_𝓕 :=
        (ennreal.continuous_coe.comp continuous_nnnorm).comp_ae_strongly_measurable hg,
      rw [measure.restrict_univ, ← mul_ess_sup_of_g h𝓕 (λ x, ↑∥g x∥₊) hg'.ae_measurable],
      exact g_ℒ_infinity } },
  { intros γ,
    have hf' : ae_strongly_measurable f (measure.map ((•) γ⁻¹) μ),
    { rw measure_theory.map_smul,
      exact f_ℒ_1.1 },
    refine ((hf'.ae_measurable.comp_measurable (measurable_const_smul _)).mono_measure _).mul _,
    { exact measure.restrict_le_self },
    { exact hg.ae_measurable.comp_measurable meas_π } },
  { exact F_ae_measurable.mul hg, },
end


/-- Given a normal subgroup `Γ` of a topological group `G` with Haar measure `μ`, which is also
  right-invariant, and a finite volume fundamental domain `𝓕`, the quotient map to `G ⧸ Γ` is
  measure-preserving between appropriate multiples of Haar measure on `G` and `G ⧸ Γ`. -/
@[to_additive measure_preserving_quotient_add_group.mk' "Given a normal subgroup `Γ` of an additive
  topological group `G` with Haar measure `μ`, which is also right-invariant, and a finite volume
  fundamental domain `𝓕`, the quotient map to `G ⧸ Γ` is measure-preserving between appropriate
  multiples of Haar measure on `G` and `G ⧸ Γ`."]
lemma measure_preserving_quotient_group.mk' [subgroup.normal Γ]
  [measure_theory.measure.is_haar_measure μ] [μ.is_mul_right_invariant]
  (h𝓕_finite : μ 𝓕 < ⊤) (c : ℝ≥0) (h : μ (𝓕 ∩ (quotient_group.mk' Γ) ⁻¹' K) = c) :
  measure_preserving
    (quotient_group.mk' Γ)
    (μ.restrict 𝓕)
    (c • (measure_theory.measure.haar_measure K)) :=
{ measurable := continuous_quotient_mk.measurable,
  map_eq := by rw [h𝓕.map_restrict_quotient K h𝓕_finite, h]; refl }
