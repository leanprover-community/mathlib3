/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import measure_theory.simple_func_dense

/-!
# Strongly measurable functions

A function `f` is said to be strongly measurable with respect to a measure `μ` if `f` is the
sequential limit of simple functions whose support has finite measure.

The main property of those functions is `strongly_measurable.exists_set_sigma_finite`: there exists
a measurable set such that  `f =ᵐ[μ.restrict tᶜ] 0` and `sigma_finite (μ.restrict t)`.
As a consequence, we can prove some results for those functions as if the measure was sigma-finite.

## Main results

- `strongly_measurable.exists_set_sigma_finite` : if a function `f` is strongly measurable with
respect to a measure `μ`, then there exists a measurable set `t` such that `f =ᵐ[μ.restrict tᶜ] 0`
and `sigma_finite (μ.restrict t)`.
- `mem_ℒp.ae_strongly_measurable` : if `mem_ℒp f p μ` with `0 < p < ∞`, then
`∃ g, strongly_measurable g μ ∧ f =ᵐ[μ] g`.
- `Lp.strongly_measurable` : for `0 < p < ∞`, `Lp` functions are strongly measurable.

TODO: prove that constant non-zero functions are stongly measurable with respect to a measure `μ`
iff `μ` is sigma finite.

-/

open measure_theory filter topological_space
open_locale ennreal topological_space measure_theory

namespace measure_theory

/-- A function is `strongly_measurable` with respect to a measure if it is the limit of simple
  functions with support with finite measure. -/
def strongly_measurable {α γ} [semi_normed_group γ] {m0 : measurable_space α}
  [decidable_pred (λ (y : γ), y ≠ 0)] (f : α → γ) (μ : measure α) : Prop :=
∃ fs : ℕ → simple_func α γ,
  (∀ n, μ (⋃ y ∈ finset.filter (λ (y : γ), y ≠ 0) (fs n).range, (fs n) ⁻¹' {y}) < ∞)
  ∧ (∀ x, tendsto (λ n, fs n x) at_top (𝓝 (f x)))

namespace strongly_measurable

variables {α H : Type*} {m0 : measurable_space α} [normed_group H] [measurable_space H]
  {μ : measure α}

lemma measurable [decidable_pred (λ (y : H), y ≠ 0)] [borel_space H] {f : α → H}
  (hf : strongly_measurable f μ) : measurable f :=
measurable_of_tendsto_metric (λ n, (hf.some n).measurable) (tendsto_pi.mpr hf.some_spec.2)

variables [decidable_pred (λ (y : H), y ≠ 0)] [has_measurable_sub₂ H] [measurable_singleton_class H]
  {f : α → H}

lemma exists_set_sigma_finite (hf : strongly_measurable f μ) :
  ∃ t, measurable_set t ∧ f =ᵐ[μ.restrict tᶜ] 0 ∧ sigma_finite (μ.restrict t) :=
begin
  rcases hf with ⟨fs, hT_lt_top, h_approx⟩,
  let T := λ n, ⋃ y ∈ finset.filter (λ (y : H), y ≠ 0) (fs n).range, (fs n) ⁻¹' {y},
  have hT_meas : ∀ n, measurable_set (T n),
    from λ n, finset.measurable_set_bUnion _ (λ y hy, simple_func.measurable_set_fiber _ _),
  let t := ⋃ n, T n,
  refine ⟨t, measurable_set.Union hT_meas, _, _⟩,
  { have h_fs_zero : ∀ n, fs n =ᵐ[μ.restrict tᶜ] 0,
    { refine λ n, (ae_restrict_iff (measurable_set_eq_fun (fs n).measurable measurable_zero)).mpr _,
      refine eventually_of_forall (λ x hxt, _),
      simp only [true_and, exists_prop, set.mem_preimage, set.mem_Union, set.mem_range,
        set.mem_singleton_iff, not_exists_not, exists_eq_right', finset.mem_filter,
        set.mem_compl_eq, simple_func.mem_range, exists_apply_eq_apply] at hxt,
      exact hxt n, },
    simp_rw eventually_eq at h_fs_zero,
    rw ← ae_all_iff at h_fs_zero,
    refine h_fs_zero.mono (λ x hx, _),
    have h_approx_zero : tendsto (λ (n : ℕ), fs n x) at_top (𝓝 0),
    { have : (λ (n : ℕ), fs n x) = λ n, 0, by { ext1 n, exact hx n, },
      rw this,
      exact tendsto_const_nhds, },
    exact tendsto_nhds_unique (h_approx x) h_approx_zero, },
  { refine measure.finite_spanning_sets_in.sigma_finite _ _,
    { exact set.range (λ n, tᶜ ∪ T n), },
    { refine ⟨λ n, tᶜ ∪ T n, λ n, set.mem_range_self _, λ n, _, _⟩,
      { rw [measure.restrict_apply' (measurable_set.Union hT_meas), set.union_inter_distrib_right,
          set.compl_inter_self t, set.empty_union],
        exact (measure_mono (set.inter_subset_left _ _)).trans_lt (hT_lt_top n), },
      rw ← set.union_Union tᶜ T,
      exact set.compl_union_self _, },
    { intros s hs,
      rw set.mem_range at hs,
      cases hs with n hsn,
      rw ← hsn,
      exact (measurable_set.compl (measurable_set.Union hT_meas)).union (hT_meas n), }, },
end

/-- A measurable set `t` such that `f =ᵐ[μ.restrict tᶜ] 0` and `sigma_finite (μ.restrict t)`. -/
def sigma_finite_set (hf : strongly_measurable f μ) : set α := hf.exists_set_sigma_finite.some

protected lemma measurable_set (hf : strongly_measurable f μ) :
  measurable_set hf.sigma_finite_set :=
hf.exists_set_sigma_finite.some_spec.1

lemma ae_eq_zero_compl (hf : strongly_measurable f μ) :
  f =ᵐ[μ.restrict hf.sigma_finite_setᶜ] 0 :=
hf.exists_set_sigma_finite.some_spec.2.1

lemma sigma_finite_restrict (hf : strongly_measurable f μ) :
  sigma_finite (μ.restrict hf.sigma_finite_set) :=
hf.exists_set_sigma_finite.some_spec.2.2

end strongly_measurable

variables {α G : Type*} {p : ℝ≥0∞} {m m0 : measurable_space α} {μ : measure α}
  [normed_group G] [measurable_space G] [borel_space G] [second_countable_topology G]

lemma mem_ℒp.strongly_measurable_of_measurable [decidable_pred (λ (y : G), y ≠ 0)] {f : α → G}
  (hf : mem_ℒp f p μ) (hf_meas : measurable f) (hp_pos : 0 < p) (hp_ne_top : p ≠ ∞) :
  strongly_measurable f μ :=
begin
  let fs := simple_func.approx_on f hf_meas set.univ 0 (set.mem_univ _),
  refine ⟨fs, _, _⟩,
  { have h_fs_Lp : ∀ n, mem_ℒp (fs n) p μ,
      from simple_func.mem_ℒp_approx_on_univ hf_meas hf,
    refine λ n, (measure_bUnion_finset_le _ _).trans_lt _,
    refine ennreal.sum_lt_top_iff.mpr (λ y hy, _),
    refine simple_func.measure_preimage_lt_top_of_mem_ℒp hp_pos hp_ne_top (fs n) (h_fs_Lp n) _ _,
    rw finset.mem_filter at hy,
    exact hy.2, },
  { exact λ x, simple_func.tendsto_approx_on hf_meas (set.mem_univ 0)
      (by { rw [closure_univ], exact set.mem_univ (f x), }), },
end

lemma mem_ℒp.ae_strongly_measurable [decidable_pred (λ (y : G), y ≠ 0)] {f : α → G}
  (hf : mem_ℒp f p μ) (hp_pos : 0 < p) (hp_ne_top : p ≠ ∞) :
  ∃ g, strongly_measurable g μ ∧ f =ᵐ[μ] g :=
begin
  obtain ⟨f', hf'_meas, hff'⟩ := hf.ae_measurable,
  exact ⟨f', ((mem_ℒp_congr_ae hff').mp hf).strongly_measurable_of_measurable hf'_meas hp_pos
    hp_ne_top, hff'⟩,
end

lemma integrable.ae_strongly_measurable [decidable_pred (λ (y : G), y ≠ 0)] {f : α → G}
  (hf : integrable f μ) :
  ∃ g, strongly_measurable g μ ∧ f =ᵐ[μ] g :=
begin
  rw ← mem_ℒp_one_iff_integrable at hf,
  exact hf.ae_strongly_measurable ennreal.zero_lt_one ennreal.coe_ne_top,
end

lemma Lp.strongly_measurable [decidable_pred (λ (y : G), y ≠ 0)] (f : Lp G p μ)
  (hp_pos : 0 < p) (hp_ne_top : p ≠ ∞) :
  strongly_measurable f μ :=
(Lp.mem_ℒp f).strongly_measurable_of_measurable (Lp.measurable _) hp_pos hp_ne_top

lemma Lp.exists_set_sigma_finite (f : Lp G p μ) (hp_pos : 0 < p) (hp_ne_top : p ≠ ∞) :
  ∃ t, measurable_set t ∧ f =ᵐ[μ.restrict tᶜ] 0 ∧ sigma_finite (μ.restrict t) :=
begin
  haveI : decidable_pred (λ (y : G), y ≠ 0) := classical.dec_pred _,
  exact (Lp.strongly_measurable f hp_pos hp_ne_top).exists_set_sigma_finite,
end

lemma exists_set_sigma_finite_of_ae_strongly_measurable [decidable_pred (λ (y : G), y ≠ 0)]
  {f : α → G} (hf : ∃ g, strongly_measurable g μ ∧ f =ᵐ[μ] g) :
  ∃ t, measurable_set t ∧ f =ᵐ[μ.restrict tᶜ] 0 ∧ sigma_finite (μ.restrict t) :=
begin
  rcases hf with ⟨g, hg, hfg⟩,
  obtain ⟨t, ht, hg_zero, htμ⟩ := hg.exists_set_sigma_finite,
  exact ⟨t, ht, eventually_eq.trans (ae_restrict_of_ae hfg) hg_zero, htμ⟩,
end

lemma exists_set_sigma_finite_of_ae_strongly_measurable' [decidable_pred (λ (y : G), y ≠ 0)]
  (hm : m ≤ m0) {f : α → G} (hf : ∃ g, strongly_measurable g (μ.trim hm) ∧ f =ᵐ[μ] g) :
  ∃ t, measurable_set[m] t ∧ f =ᵐ[μ.restrict tᶜ] 0 ∧ @sigma_finite _ m ((μ.restrict t).trim hm) :=
begin
  rcases hf with ⟨g, hg, hfg⟩,
  obtain ⟨t, ht, hg_zero, htμ⟩ := hg.exists_set_sigma_finite,
  refine ⟨t, ht, _, _⟩,
  { have hfg_eq : f =ᵐ[μ.restrict tᶜ] g, from ae_restrict_of_ae hfg,
    refine hfg_eq.trans _,
    rw restrict_trim hm μ (@measurable_set.compl _ _ m ht) at hg_zero,
    exact measure_eq_zero_of_trim_eq_zero hm hg_zero, },
  { rwa restrict_trim hm μ ht at htμ, },
end

end measure_theory
