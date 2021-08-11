/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import measure_theory.function.simple_func_dense

/-!
# Strongly measurable functions

A function `f` is said to be strongly measurable with respect to a measure `μ` if `f` is the
sequential limit of simple functions whose support has finite measure.

Functions in `Lp` for `0 < p < ∞` are strongly measurable.
If the measure is sigma-finite, measurable and strongly measurable are equivalent.

The main property of strongly measurable functions is `strongly_measurable.exists_set_sigma_finite`:
there exists a measurable set such that `f =ᵐ[μ.restrict tᶜ] 0` and `μ.restrict t` is sigma-finite.
As a consequence, we can prove some results for those functions as if the measure was sigma-finite.

## Main definitions

* `strongly_measurable f μ`: `f : α → γ` is the limit of a sequence `fs : ℕ → simple_func α γ`
  such that for all `n ∈ ℕ`, the measure of the support of `fs n` is finite.
* `strongly_measurable.sigma_finite_set`: a measurable set `t` such that `f =ᵐ[μ.restrict tᶜ] 0` and
  `μ.restrict t` is sigma-finite.

## Main statements

* `strongly_measurable.exists_set_sigma_finite`: if a function `f` is strongly measurable with
  respect to a measure `μ`, then there exists a measurable set `t` such that `f =ᵐ[μ.restrict tᶜ] 0`
  and `sigma_finite (μ.restrict t)`.
* `mem_ℒp.ae_strongly_measurable`: if `mem_ℒp f p μ` with `0 < p < ∞`, then
  `∃ g, strongly_measurable g μ ∧ f =ᵐ[μ] g`.
* `Lp.strongly_measurable`: for `0 < p < ∞`, `Lp` functions are strongly measurable.
* `stongly_measurable.measurable`: a stongly measurable function is measurable.
* `measurable.strongly_measurable`: if a measure is sigma-finite, then all measurable functions are
  strongly measurable.

## References

* Hytönen, Tuomas, Jan Van Neerven, Mark Veraar, and Lutz Weis. Analysis in Banach spaces.
  Springer, 2016.

-/

open measure_theory filter topological_space
open_locale ennreal topological_space measure_theory

namespace measure_theory

/-- A function is `strongly_measurable` with respect to a measure if it is the limit of simple
  functions with support with finite measure. -/
def strongly_measurable {α γ} [topological_space γ] [has_zero γ] {m0 : measurable_space α}
  [decidable_pred (λ (y : γ), y ≠ 0)] (f : α → γ) (μ : measure α) : Prop :=
∃ fs : ℕ → simple_func α γ,
  (∀ n, μ (⋃ y ∈ finset.filter (λ (y : γ), y ≠ 0) (fs n).range, (fs n) ⁻¹' {y}) < ∞)
  ∧ (∀ x, tendsto (λ n, fs n x) at_top (𝓝 (f x)))

namespace strongly_measurable

variables {α H : Type*} {m0 : measurable_space α} [normed_group H] [measurable_space H]
  {μ : measure α} [decidable_pred (λ (y : H), y ≠ 0)] {f : α → H}

/-- A strongly measurable function is measurable. -/
lemma measurable [borel_space H] (hf : strongly_measurable f μ) : measurable f :=
measurable_of_tendsto_metric (λ n, (hf.some n).measurable) (tendsto_pi.mpr hf.some_spec.2)

variables [has_measurable_sub₂ H] [measurable_singleton_class H]

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
    simp_rw [eventually_eq, ← ae_all_iff] at h_fs_zero,
    refine h_fs_zero.mono (λ x hx, _),
    refine tendsto_nhds_unique (h_approx x) _,
    rw funext (λ n, hx n),
    exact tendsto_const_nhds, },
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

/-- If the measure is sigma-finite, all measurable functions are strongly measurable. -/
lemma measurable.strongly_measurable {α G : Type*} [measurable_space G] [emetric_space G]
  [has_zero G] [second_countable_topology G] [opens_measurable_space G]
  [decidable_pred (λ (y : G), y ≠ 0)]
  {m0 : measurable_space α} {f : α → G} (hf : measurable f) (μ : measure α) [sigma_finite μ]  :
  strongly_measurable f μ :=
begin
  let S := spanning_sets μ,
  have hS_meas : ∀ n, measurable_set (S n), from measurable_spanning_sets μ,
  let f_approx := simple_func.approx_on f hf set.univ 0 (set.mem_univ _),
  let fs := λ n, simple_func.restrict (f_approx n) (S n),
  refine ⟨fs, _, λ x, _⟩,
  { refine λ n, (measure_bUnion_finset_le _ _).trans_lt _,
    refine ennreal.sum_lt_top_iff.mpr (λ y hy, _),
    rw simple_func.restrict_preimage_singleton _ (hS_meas n) (finset.mem_filter.mp hy).2,
    refine (measure_mono (set.inter_subset_left _ _)).trans_lt _,
    exact measure_spanning_sets_lt_top μ n, },
  { have h : tendsto (λ n, (simple_func.approx_on f hf set.univ 0 _ n) x) at_top (𝓝 (f x)),
      from simple_func.tendsto_approx_on hf (set.mem_univ 0) (by simp),
    obtain ⟨n₁, hn₁⟩ : ∃ n, ∀ m, n ≤ m → fs m x = f_approx m x,
    { obtain ⟨n, hn⟩ : ∃ n, ∀ m, n ≤ m → x ∈ S m,
      { suffices : ∃ n, x ∈ S n,
        { rcases this with ⟨n, hn⟩,
          exact ⟨n, λ m hnm, monotone_spanning_sets μ hnm hn⟩, },
        rw [← set.mem_Union, Union_spanning_sets μ],
        trivial, },
      refine ⟨n, λ m hnm, _⟩,
      simp_rw [fs, simple_func.restrict_apply _ (hS_meas m), set.indicator_of_mem (hn m hnm)], },
    rw tendsto_at_top' at h ⊢,
    intros s hs,
    obtain ⟨n₂, hn₂⟩ := h s hs,
    refine ⟨max n₁ n₂, λ m hm, _⟩,
    rw hn₁ m ((le_max_left _ _).trans hm.le),
    exact hn₂ m ((le_max_right _ _).trans hm.le), },
end

variables {α G : Type*} {p : ℝ≥0∞} {m m0 : measurable_space α} {μ : measure α}
  [normed_group G] [measurable_space G] [borel_space G] [second_countable_topology G]
  [decidable_pred (λ (y : G), y ≠ 0)]
  {f : α → G}

/-- If the measure is sigma-finite, strongly measurable and measurable are equivalent. -/
lemma strongly_measurable_iff_measurable {m0 : measurable_space α} (μ : measure α)
  [sigma_finite μ] :
  strongly_measurable f μ ↔ measurable f :=
⟨λ h, h.measurable, λ h, measurable.strongly_measurable h μ⟩

lemma mem_ℒp.strongly_measurable_of_measurable (hf : mem_ℒp f p μ) (hf_meas : measurable f)
  (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
  strongly_measurable f μ :=
begin
  let fs := simple_func.approx_on f hf_meas set.univ 0 (set.mem_univ _),
  refine ⟨fs, _, _⟩,
  { have h_fs_Lp : ∀ n, mem_ℒp (fs n) p μ, from simple_func.mem_ℒp_approx_on_univ hf_meas hf,
    refine λ n, (measure_bUnion_finset_le _ _).trans_lt (ennreal.sum_lt_top_iff.mpr (λ y hy, _)),
    exact simple_func.measure_preimage_lt_top_of_mem_ℒp (pos_iff_ne_zero.mpr hp_ne_zero) hp_ne_top
      (fs n) (h_fs_Lp n) _ (finset.mem_filter.mp hy).2, },
  { exact λ x, simple_func.tendsto_approx_on hf_meas (set.mem_univ 0) (by simp), },
end

lemma mem_ℒp.ae_strongly_measurable (hf : mem_ℒp f p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
  ∃ g, strongly_measurable g μ ∧ f =ᵐ[μ] g :=
⟨hf.ae_measurable.mk f,
  ((mem_ℒp_congr_ae hf.ae_measurable.ae_eq_mk).mp hf).strongly_measurable_of_measurable
    hf.ae_measurable.measurable_mk hp_ne_zero hp_ne_top,
  hf.ae_measurable.ae_eq_mk⟩

lemma integrable.ae_strongly_measurable (hf : integrable f μ) :
  ∃ g, strongly_measurable g μ ∧ f =ᵐ[μ] g :=
(mem_ℒp_one_iff_integrable.mpr hf).ae_strongly_measurable one_ne_zero ennreal.coe_ne_top

lemma Lp.strongly_measurable (f : Lp G p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
  strongly_measurable f μ :=
(Lp.mem_ℒp f).strongly_measurable_of_measurable (Lp.measurable f) hp_ne_zero hp_ne_top

lemma exists_set_sigma_finite_of_ae_strongly_measurable
  (hf : ∃ g, strongly_measurable g μ ∧ f =ᵐ[μ] g) :
  ∃ t, measurable_set t ∧ f =ᵐ[μ.restrict tᶜ] 0 ∧ sigma_finite (μ.restrict t) :=
begin
  rcases hf with ⟨g, hg, hfg⟩,
  exact ⟨hg.sigma_finite_set, hg.measurable_set,
    eventually_eq.trans (ae_restrict_of_ae hfg) hg.ae_eq_zero_compl, hg.sigma_finite_restrict⟩,
end

lemma exists_set_sigma_finite_of_ae_strongly_measurable' (hm : m ≤ m0)
  (hf : ∃ g, strongly_measurable g (μ.trim hm) ∧ f =ᵐ[μ] g) :
  ∃ t, measurable_set[m] t ∧ f =ᵐ[μ.restrict tᶜ] 0 ∧ @sigma_finite _ m ((μ.restrict t).trim hm) :=
begin
  rcases hf with ⟨g, hg, hfg⟩,
  refine ⟨hg.sigma_finite_set, hg.measurable_set, _, _⟩,
  { have hfg_eq : f =ᵐ[μ.restrict hg.sigma_finite_setᶜ] g, from ae_restrict_of_ae hfg,
    have hg_zero := hg.ae_eq_zero_compl,
    refine hfg_eq.trans (measure_eq_zero_of_trim_eq_zero hm _),
    rwa restrict_trim hm μ (@measurable_set.compl _ _ m hg.measurable_set) at hg_zero, },
  { exact (restrict_trim hm μ hg.measurable_set).subst hg.sigma_finite_restrict, },
end

end measure_theory
