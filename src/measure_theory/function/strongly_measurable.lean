/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import measure_theory.function.simple_func_dense

/-!
# Strongly measurable and finitely strongly measurable functions

A function `f` is said to be strongly measurable if `f` is the sequential limit of simple functions.
It is said to be finitely strongly measurable with respect to a measure `μ` if the supports
of those simple functions have finite measure.

If the target space has a second countable topology, strongly measurable and measurable are
equivalent.

Functions in `Lp` for `0 < p < ∞` are finitely strongly measurable.
If the measure is sigma-finite, strongly measurable and finitely strongly measurable are equivalent.

The main property of finitely strongly measurable functions is
`fin_strongly_measurable.exists_set_sigma_finite`: there exists a measurable set `t` such that the
function is supported on `t` and `μ.restrict t` is sigma-finite. As a consequence, we can prove some
results for those functions as if the measure was sigma-finite.

## Main definitions

* `strongly_measurable f`: `f : α → β` is the limit of a sequence `fs : ℕ → simple_func α β`.
* `fin_strongly_measurable f μ`: `f : α → β` is the limit of a sequence `fs : ℕ → simple_func α β`
  such that for all `n ∈ ℕ`, the measure of the support of `fs n` is finite.
* `ae_fin_strongly_measurable f μ`: `f` is almost everywhere equal to a `fin_strongly_measurable`
  function.

* `ae_fin_strongly_measurable.sigma_finite_set`: a measurable set `t` such that
  `f =ᵐ[μ.restrict tᶜ] 0` and `μ.restrict t` is sigma-finite.

## Main statements

* `ae_fin_strongly_measurable.exists_set_sigma_finite`: there exists a measurable set `t` such that
  `f =ᵐ[μ.restrict tᶜ] 0` and `μ.restrict t` is sigma-finite.
* `mem_ℒp.ae_fin_strongly_measurable`: if `mem_ℒp f p μ` with `0 < p < ∞`, then
  `ae_fin_strongly_measurable f μ`.
* `Lp.fin_strongly_measurable`: for `0 < p < ∞`, `Lp` functions are finitely strongly measurable.

## References

* Hytönen, Tuomas, Jan Van Neerven, Mark Veraar, and Lutz Weis. Analysis in Banach spaces.
  Springer, 2016.

-/

open measure_theory filter topological_space function
open_locale nnreal ennreal topological_space measure_theory

namespace measure_theory

local infixr ` →ₛ `:25 := simple_func

section definitions
variables {α β : Type*} [topological_space β]

/-- A function is `strongly_measurable` if it is the limit of simple functions. -/
def strongly_measurable [measurable_space α] (f : α → β) : Prop :=
∃ fs : ℕ → α →ₛ β, ∀ x, tendsto (λ n, fs n x) at_top (𝓝 (f x))

/-- A function is `ae_strongly_measurable` with respect to a measure if it is almost everywhere
equal to the limit of a sequence of simple functions. -/
def ae_strongly_measurable {m0 : measurable_space α} (f : α → β) (μ : measure α) :
  Prop :=
∃ g, strongly_measurable g ∧ f =ᵐ[μ] g

/-- A function is `fin_strongly_measurable` with respect to a measure if it is the limit of simple
  functions with support with finite measure. -/
def fin_strongly_measurable [has_zero β] {m0 : measurable_space α} (f : α → β) (μ : measure α) :
  Prop :=
∃ fs : ℕ → α →ₛ β, (∀ n, μ (support (fs n)) < ∞) ∧ (∀ x, tendsto (λ n, fs n x) at_top (𝓝 (f x)))

/-- A function is `ae_fin_strongly_measurable` with respect to a measure if it is almost everywhere
equal to the limit of a sequence of simple functions with support with finite measure. -/
def ae_fin_strongly_measurable [has_zero β] {m0 : measurable_space α} (f : α → β) (μ : measure α) :
  Prop :=
∃ g, fin_strongly_measurable g μ ∧ f =ᵐ[μ] g

end definitions

/-! ## Strongly measurable functions -/

lemma subsingleton.strongly_measurable {α β} [measurable_space α] [topological_space β]
  [subsingleton β] (f : α → β) :
  strongly_measurable f :=
begin
  let f_sf : α →ₛ β := ⟨f, λ x, _,
    set.subsingleton.finite set.subsingleton_of_subsingleton⟩,
  { exact ⟨λ n, f_sf, λ x, tendsto_const_nhds⟩, },
  { have h_univ : f ⁻¹' {x} = set.univ, by { ext1 y, simp, },
    rw h_univ,
    exact measurable_set.univ, },
end

lemma strongly_measurable_const {α β} [measurable_space α] [topological_space β] {b : β} :
  strongly_measurable (λ a : α, b) :=
⟨λ n, simple_func.const α b, λ a, tendsto_const_nhds⟩

namespace strongly_measurable

variables {α β δ : Type*} {f g : α → β}

section basic_properties_in_any_topological_space
variables [topological_space β]

protected lemma ae_strongly_measurable {m : measurable_space α} {μ : measure α}
  (hf : strongly_measurable f) :
  ae_strongly_measurable f μ :=
⟨f, hf, eventually_eq.rfl⟩

/-- A sequence of simple functions such that `∀ x, tendsto (λ n, hf.approx n x) at_top (𝓝 (f x))`.
That property is given by `strongly_measurable.tendsto_approx`. -/
protected noncomputable
def approx [measurable_space α] (hf : strongly_measurable f) : ℕ → α →ₛ β :=
hf.some

protected lemma tendsto_approx [measurable_space α] (hf : strongly_measurable f) :
  ∀ x, tendsto (λ n, hf.approx n x) at_top (𝓝 (f x)) :=
hf.some_spec

end basic_properties_in_any_topological_space

lemma fin_strongly_measurable_of_set_sigma_finite [topological_space β] [has_zero β]
  {m : measurable_space α} {μ : measure α} (hf_meas : strongly_measurable f) {t : set α}
  (ht : measurable_set t) (hft_zero : ∀ x ∈ tᶜ, f x = 0) (htμ : sigma_finite (μ.restrict t)) :
  fin_strongly_measurable f μ :=
begin
  haveI : sigma_finite (μ.restrict t) := htμ,
  let S := spanning_sets (μ.restrict t),
  have hS_meas : ∀ n, measurable_set (S n), from measurable_spanning_sets (μ.restrict t),
  let f_approx := hf_meas.approx,
  let fs := λ n, simple_func.restrict (f_approx n) (S n ∩ t),
  have h_fs_t_compl : ∀ n, ∀ x ∉ t, fs n x = 0,
  { intros n x hxt,
    rw simple_func.restrict_apply _ ((hS_meas n).inter ht),
    refine set.indicator_of_not_mem _ _,
    simp [hxt], },
  refine ⟨fs, _, λ x, _⟩,
  { simp_rw simple_func.support_eq,
    refine λ n, (measure_bUnion_finset_le _ _).trans_lt _,
    refine ennreal.sum_lt_top_iff.mpr (λ y hy, _),
    rw simple_func.restrict_preimage_singleton _ ((hS_meas n).inter ht),
    swap, { rw finset.mem_filter at hy, exact hy.2, },
    refine (measure_mono (set.inter_subset_left _ _)).trans_lt _,
    have h_lt_top := measure_spanning_sets_lt_top (μ.restrict t) n,
    rwa measure.restrict_apply' ht at h_lt_top, },
  { by_cases hxt : x ∈ t,
    swap, { rw [funext (λ n, h_fs_t_compl n x hxt), hft_zero x hxt], exact tendsto_const_nhds, },
    have h : tendsto (λ n, (f_approx n) x) at_top (𝓝 (f x)), from hf_meas.tendsto_approx x,
    obtain ⟨n₁, hn₁⟩ : ∃ n, ∀ m, n ≤ m → fs m x = f_approx m x,
    { obtain ⟨n, hn⟩ : ∃ n, ∀ m, n ≤ m → x ∈ S m ∩ t,
      { suffices : ∃ n, ∀ m, n ≤ m → x ∈ S m,
        { obtain ⟨n, hn⟩ := this,
          exact ⟨n, λ m hnm, set.mem_inter (hn m hnm) hxt⟩, },
        suffices : ∃ n, x ∈ S n,
        { rcases this with ⟨n, hn⟩,
          exact ⟨n, λ m hnm, monotone_spanning_sets (μ.restrict t) hnm hn⟩, },
        rw [← set.mem_Union, Union_spanning_sets (μ.restrict t)],
        trivial, },
      refine ⟨n, λ m hnm, _⟩,
      simp_rw [fs, simple_func.restrict_apply _ ((hS_meas m).inter ht),
        set.indicator_of_mem (hn m hnm)], },
    rw tendsto_at_top' at h ⊢,
    intros s hs,
    obtain ⟨n₂, hn₂⟩ := h s hs,
    refine ⟨max n₁ n₂, λ m hm, _⟩,
    rw hn₁ m ((le_max_left _ _).trans hm.le),
    exact hn₂ m ((le_max_right _ _).trans hm.le), },
end

/-- If the measure is sigma-finite, all strongly measurable functions are
  `fin_strongly_measurable`. -/
protected lemma fin_strongly_measurable [topological_space β] [has_zero β] {m0 : measurable_space α}
  (hf : strongly_measurable f) (μ : measure α) [sigma_finite μ] :
  fin_strongly_measurable f μ :=
hf.fin_strongly_measurable_of_set_sigma_finite measurable_set.univ (by simp)
  (by rwa measure.restrict_univ)

/-- A strongly measurable function is measurable. -/
protected lemma measurable [measurable_space α] [metric_space β] [measurable_space β]
  [borel_space β] (hf : strongly_measurable f) :
  measurable f :=
measurable_of_tendsto_metric (λ n, (hf.approx n).measurable) (tendsto_pi_nhds.mpr hf.tendsto_approx)

protected lemma measurable_ennreal [measurable_space α] {f : α → ℝ≥0∞}
  (hf : strongly_measurable f) :
  measurable f :=
measurable_of_tendsto_ennreal (λ n, (hf.approx n).measurable)
  (tendsto_pi_nhds.mpr hf.tendsto_approx)

section arithmetic
variables [measurable_space α] [topological_space β]

@[to_additive]
protected lemma mul [has_mul β] [has_continuous_mul β]
  (hf : strongly_measurable f) (hg : strongly_measurable g) :
  strongly_measurable (f * g) :=
⟨λ n, hf.approx n * hg.approx n, λ x, (hf.tendsto_approx x).mul (hg.tendsto_approx x)⟩

@[to_additive]
protected lemma inv [group β] [topological_group β] (hf : strongly_measurable f) :
  strongly_measurable f⁻¹ :=
⟨λ n, (hf.approx n)⁻¹, λ x, (hf.tendsto_approx x).inv⟩

protected lemma sub [has_sub β] [has_continuous_sub β]
  (hf : strongly_measurable f) (hg : strongly_measurable g) :
  strongly_measurable (f - g) :=
⟨λ n, hf.approx n - hg.approx n, λ x, (hf.tendsto_approx x).sub (hg.tendsto_approx x)⟩

protected lemma const_smul {𝕜} [semiring 𝕜] [topological_space 𝕜] [add_comm_monoid β] [module 𝕜 β]
  [has_continuous_smul 𝕜 β] (hf : strongly_measurable f) (c : 𝕜) :
  strongly_measurable (c • f) :=
⟨λ n, c • (hf.approx n), λ x, (hf.tendsto_approx x).const_smul c⟩

end arithmetic

section order
variables [measurable_space α] [topological_space β]

open filter
open_locale filter

/- Move next to `filter.tendsto_prod_iff` -/
lemma tendsto_prod_iff' {ι G G'} {f : filter ι} {g : filter G} {g' : filter G'}
  {s : ι → G × G'} :
  tendsto s f (g ×ᶠ g') ↔ tendsto (λ n, (s n).1) f g ∧ tendsto (λ n, (s n).2) f g' :=
begin
  unfold filter.prod,
  simp only [tendsto_inf, tendsto_comap_iff, iff_self]
end

lemma prod.tendsto_iff {ι G G'} [topological_space G] [topological_space G']
  (seq : ι → G × G') {f : filter ι} (x : G × G') :
  tendsto seq f (𝓝 x)
    ↔ tendsto (λ n, (seq n).fst) f (𝓝 x.fst) ∧ tendsto (λ n, (seq n).snd) f (𝓝 x.snd) :=
by { cases x, rw [nhds_prod_eq, tendsto_prod_iff'], }

-- TODO: move this
lemma _root_.filter.tendsto.sup_right {ι} [preorder ι] {f g : ι → β} [has_sup β]
  [has_continuous_sup β] {l : filter ι} {x y : β}
  (hf : tendsto f l (𝓝 x)) (hg : tendsto g l (𝓝 y)) :
  tendsto (f ⊔ g) l (𝓝 (x ⊔ y)) :=
begin
  have h_prod_left : f ⊔ g = (λ p : β × β, (p.fst ⊔ p.snd : β)) ∘ (λ i, (f i, g i)) := rfl,
  have h_prod_right : x ⊔ y = (λ p : β × β, p.fst ⊔ p.snd) (x, y) := rfl,
  rw [h_prod_left, h_prod_right],
  refine (continuous_sup.tendsto (x,y)).comp _,
  rw prod.tendsto_iff,
  exact ⟨hf, hg⟩,
end

-- TODO: move this
lemma _root_.filter.tendsto.inf_right {ι} [preorder ι] {f g : ι → β} [has_inf β]
  [has_continuous_inf β] {l : filter ι} {x y : β}
  (hf : tendsto f l (𝓝 x)) (hg : tendsto g l (𝓝 y)) :
  tendsto (f ⊓ g) l (𝓝 (x ⊓ y)) :=
begin
  have h_prod_left : f ⊓ g = (λ p : β × β, (p.fst ⊓ p.snd : β)) ∘ (λ i, (f i, g i)) := rfl,
  have h_prod_right : x ⊓ y = (λ p : β × β, p.fst ⊓ p.snd) (x, y) := rfl,
  rw [h_prod_left, h_prod_right],
  refine (continuous_inf.tendsto (x,y)).comp _,
  rw prod.tendsto_iff,
  exact ⟨hf, hg⟩,
end

protected lemma sup [has_sup β] [has_continuous_sup β] (hf : strongly_measurable f)
  (hg : strongly_measurable g) :
  strongly_measurable (f ⊔ g) :=
⟨λ n, hf.approx n ⊔ hg.approx n, λ x, (hf.tendsto_approx x).sup_right (hg.tendsto_approx x)⟩

protected lemma inf [has_inf β] [has_continuous_inf β] (hf : strongly_measurable f)
  (hg : strongly_measurable g) :
  strongly_measurable (f ⊓ g) :=
⟨λ n, hf.approx n ⊓ hg.approx n, λ x, (hf.tendsto_approx x).inf_right (hg.tendsto_approx x)⟩

end order

end strongly_measurable

section second_countable_strongly_measurable
variables {α β : Type*} [measurable_space α] [measurable_space β] {f : α → β}

/-- In a space with second countable topology, measurable implies strongly measurable. -/
lemma _root_.measurable.strongly_measurable [emetric_space β] [opens_measurable_space β]
  [second_countable_topology β] (hf : measurable f) :
  strongly_measurable f :=
begin
  rcases is_empty_or_nonempty β; resetI,
  { exact subsingleton.strongly_measurable f, },
  { inhabit β,
    exact ⟨simple_func.approx_on f hf set.univ default (set.mem_univ _),
      λ x, simple_func.tendsto_approx_on hf (set.mem_univ _) (by simp)⟩, },
end

/-- In a space with second countable topology, strongly measurable and measurable are equivalent. -/
lemma strongly_measurable_iff_measurable [metric_space β] [borel_space β]
  [second_countable_topology β] :
  strongly_measurable f ↔ measurable f :=
⟨λ h, h.measurable, λ h, measurable.strongly_measurable h⟩

end second_countable_strongly_measurable

lemma ae_strongly_measurable_const {α β} {m : measurable_space α} {μ : measure α}
  [topological_space β] {b : β} :
  ae_strongly_measurable (λ a : α, b) μ :=
strongly_measurable_const.ae_strongly_measurable

namespace ae_strongly_measurable

variables {α β : Type*} {m0 : measurable_space α} {μ : measure α} {f g : α → β}
  [topological_space β]

protected noncomputable def mk (f : α → β) (hf : ae_strongly_measurable f μ) : α → β := hf.some

lemma strongly_measurable_mk (hf : ae_strongly_measurable f μ) : strongly_measurable (hf.mk f) :=
hf.some_spec.1

lemma ae_eq_mk (hf : ae_strongly_measurable f μ) : f =ᵐ[μ] hf.mk f :=
hf.some_spec.2

protected lemma ae_measurable {β} [measurable_space β] [metric_space β] [borel_space β] {f : α → β}
  (hf : ae_strongly_measurable f μ) :
  ae_measurable f μ :=
⟨hf.mk f, hf.strongly_measurable_mk.measurable, hf.ae_eq_mk⟩

protected lemma ae_measurable_ennreal {f : α → ℝ≥0∞} (hf : ae_strongly_measurable f μ) :
  ae_measurable f μ :=
⟨hf.mk f, hf.strongly_measurable_mk.measurable_ennreal, hf.ae_eq_mk⟩

section arithmetic

@[to_additive]
protected lemma mul [has_mul β] [has_continuous_mul β]
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) :
  ae_strongly_measurable (f * g) μ :=
⟨(hf.mk f) * (hg.mk g), hf.strongly_measurable_mk.mul hg.strongly_measurable_mk,
  hf.ae_eq_mk.mul hg.ae_eq_mk⟩

attribute [to_additive] ae_strongly_measurable.mul

@[to_additive]
protected lemma inv [group β] [topological_group β] (hf : ae_strongly_measurable f μ) :
  ae_strongly_measurable f⁻¹ μ :=
⟨(hf.mk f)⁻¹, hf.strongly_measurable_mk.inv, hf.ae_eq_mk.inv⟩

protected lemma sub [add_group β] [topological_add_group β]
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) :
  ae_strongly_measurable (f - g) μ :=
⟨(hf.mk f) - (hg.mk g), hf.strongly_measurable_mk.sub hg.strongly_measurable_mk,
  hf.ae_eq_mk.sub hg.ae_eq_mk⟩

protected lemma const_smul {𝕜} [semiring 𝕜] [topological_space 𝕜] [add_comm_monoid β] [module 𝕜 β]
  [has_continuous_smul 𝕜 β] (hf : ae_strongly_measurable f μ) (c : 𝕜) :
  ae_strongly_measurable (c • f) μ :=
⟨c • (hf.mk f), hf.strongly_measurable_mk.const_smul c,
  by { refine hf.ae_eq_mk.mono (λ x hx, _), rw [pi.smul_apply, pi.smul_apply, hx], }⟩

end arithmetic

section order

protected lemma sup [has_sup β] [has_continuous_sup β] (hf : ae_strongly_measurable f μ)
  (hg : ae_strongly_measurable g μ) :
  ae_strongly_measurable (f ⊔ g) μ :=
⟨(hf.mk f) ⊔ (hg.mk g), hf.strongly_measurable_mk.sup hg.strongly_measurable_mk,
  by { filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx,
    rw [pi.sup_apply, pi.sup_apply, hfx, hgx], }⟩

protected lemma inf [has_inf β] [has_continuous_inf β] (hf : ae_strongly_measurable f μ)
  (hg : ae_strongly_measurable g μ) :
  ae_strongly_measurable (f ⊓ g) μ :=
⟨(hf.mk f) ⊓ (hg.mk g), hf.strongly_measurable_mk.inf hg.strongly_measurable_mk,
  by { filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx,
    rw [pi.inf_apply, pi.inf_apply, hfx, hgx], }⟩

end order

end ae_strongly_measurable

/-! ## Finitely strongly measurable functions -/

namespace fin_strongly_measurable

variables {α β : Type*} {m0 : measurable_space α} {μ : measure α} {f g : α → β}

lemma ae_fin_strongly_measurable [has_zero β] [topological_space β]
  (hf : fin_strongly_measurable f μ) :
  ae_fin_strongly_measurable f μ :=
⟨f, hf, ae_eq_refl f⟩

section sequence
variables [has_zero β] [topological_space β] (hf : fin_strongly_measurable f μ)

/-- A sequence of simple functions such that `∀ x, tendsto (λ n, hf.approx n x) at_top (𝓝 (f x))`
and `∀ n, μ (support (hf.approx n)) < ∞`. These properties are given by
`fin_strongly_measurable.tendsto_approx` and `fin_strongly_measurable.fin_support_approx`. -/
protected noncomputable def approx : ℕ → α →ₛ β := hf.some

protected lemma fin_support_approx : ∀ n, μ (support (hf.approx n)) < ∞ := hf.some_spec.1

protected lemma tendsto_approx : ∀ x, tendsto (λ n, hf.approx n x) at_top (𝓝 (f x)) :=
hf.some_spec.2

end sequence

protected lemma strongly_measurable [has_zero β] [topological_space β]
  (hf : fin_strongly_measurable f μ) :
  strongly_measurable f :=
⟨hf.approx, hf.tendsto_approx⟩

lemma exists_set_sigma_finite [has_zero β] [topological_space β] [t2_space β]
  (hf : fin_strongly_measurable f μ) :
  ∃ t, measurable_set t ∧ (∀ x ∈ tᶜ, f x = 0) ∧ sigma_finite (μ.restrict t) :=
begin
  rcases hf with ⟨fs, hT_lt_top, h_approx⟩,
  let T := λ n, support (fs n),
  have hT_meas : ∀ n, measurable_set (T n), from λ n, simple_func.measurable_set_support (fs n),
  let t := ⋃ n, T n,
  refine ⟨t, measurable_set.Union hT_meas, _, _⟩,
  { have h_fs_zero : ∀ n, ∀ x ∈ tᶜ, fs n x = 0,
    { intros n x hxt,
      rw [set.mem_compl_iff, set.mem_Union, not_exists] at hxt,
      simpa using (hxt n), },
    refine λ x hxt, tendsto_nhds_unique (h_approx x) _,
    rw funext (λ n, h_fs_zero n x hxt),
    exact tendsto_const_nhds, },
  { refine ⟨⟨⟨λ n, tᶜ ∪ T n, λ n, trivial, λ n, _, _⟩⟩⟩,
    { rw [measure.restrict_apply' (measurable_set.Union hT_meas), set.union_inter_distrib_right,
        set.compl_inter_self t, set.empty_union],
      exact (measure_mono (set.inter_subset_left _ _)).trans_lt (hT_lt_top n), },
    { rw ← set.union_Union tᶜ T,
      exact set.compl_union_self _ } }
end

/-- A finitely strongly measurable function is measurable. -/
protected lemma measurable [has_zero β] [metric_space β] [measurable_space β] [borel_space β]
  (hf : fin_strongly_measurable f μ) :
  measurable f :=
hf.strongly_measurable.measurable

protected lemma measurable_ennreal {f : α → ℝ≥0∞} (hf : fin_strongly_measurable f μ) :
  measurable f :=
hf.strongly_measurable.measurable_ennreal

section arithmetic
variables [topological_space β]

protected lemma mul [monoid_with_zero β] [no_zero_divisors β] [has_continuous_mul β]
  (hf : fin_strongly_measurable f μ) (hg : fin_strongly_measurable g μ) :
  fin_strongly_measurable (f * g) μ :=
begin
  refine ⟨λ n, hf.approx n * hg.approx n, _, λ x, (hf.tendsto_approx x).mul (hg.tendsto_approx x)⟩,
  intro n,
  rw (_ : support ⇑(hf.approx n * hg.approx n) = support (hf.approx n) ∩ support (hg.approx n)),
  { exact measure_inter_lt_top_of_left_ne_top (hf.fin_support_approx n).ne,},
  { exact function.support_mul _ _, },
end

protected lemma add [add_monoid β] [has_continuous_add β]
  (hf : fin_strongly_measurable f μ) (hg : fin_strongly_measurable g μ) :
  fin_strongly_measurable (f + g) μ :=
⟨λ n, hf.approx n + hg.approx n,
  λ n, (measure_mono (function.support_add _ _)).trans_lt ((measure_union_le _ _).trans_lt
    (ennreal.add_lt_top.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩)),
  λ x, (hf.tendsto_approx x).add (hg.tendsto_approx x)⟩

protected lemma neg [add_group β] [topological_add_group β] (hf : fin_strongly_measurable f μ) :
  fin_strongly_measurable (-f) μ :=
begin
  refine ⟨λ n, -hf.approx n, λ n, _, λ x, (hf.tendsto_approx x).neg⟩,
  suffices : μ (function.support (λ x, - (hf.approx n) x)) < ∞, by convert this,
  rw function.support_neg (hf.approx n),
  exact hf.fin_support_approx n,
end

protected lemma sub [add_group β] [has_continuous_sub β]
  (hf : fin_strongly_measurable f μ) (hg : fin_strongly_measurable g μ) :
  fin_strongly_measurable (f - g) μ :=
⟨λ n, hf.approx n - hg.approx n,
  λ n, (measure_mono (function.support_sub _ _)).trans_lt ((measure_union_le _ _).trans_lt
    (ennreal.add_lt_top.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩)),
  λ x, (hf.tendsto_approx x).sub (hg.tendsto_approx x)⟩

end arithmetic

section order
variables [topological_space β]

protected lemma sup [has_zero β] [has_sup β] [has_continuous_sup β] (hf : fin_strongly_measurable f μ)
  (hg : fin_strongly_measurable g μ) :
  fin_strongly_measurable (f ⊔ g) μ :=
begin
  refine ⟨λ n, hf.approx n ⊔ hg.approx n, λ n, _,
    λ x, (hf.tendsto_approx x).sup_right (hg.tendsto_approx x)⟩,
  --refine (measure_mono (support_sup _ _)).trans_lt _,
end

protected lemma inf [has_inf β] [has_continuous_inf β] (hf : strongly_measurable f)
  (hg : strongly_measurable g) :
  strongly_measurable (f ⊓ g) :=
⟨λ n, hf.approx n ⊓ hg.approx n, λ x, (hf.tendsto_approx x).inf_right (hg.tendsto_approx x)⟩

end order

end fin_strongly_measurable

lemma fin_strongly_measurable_iff_strongly_measurable_and_exists_set_sigma_finite {α β} {f : α → β}
  [topological_space β] [t2_space β] [has_zero β] {m : measurable_space α} {μ : measure α} :
  fin_strongly_measurable f μ ↔ (strongly_measurable f
    ∧ (∃ t, measurable_set t ∧ (∀ x ∈ tᶜ, f x = 0) ∧ sigma_finite (μ.restrict t))) :=
⟨λ hf, ⟨hf.strongly_measurable, hf.exists_set_sigma_finite⟩,
  λ hf, hf.1.fin_strongly_measurable_of_set_sigma_finite hf.2.some_spec.1 hf.2.some_spec.2.1
    hf.2.some_spec.2.2⟩

namespace ae_fin_strongly_measurable

variables {α β : Type*} {m : measurable_space α} {μ : measure α} [topological_space β]
  {f g : α → β}

section mk
variables [has_zero β]

protected noncomputable def mk (f : α → β) (hf : ae_fin_strongly_measurable f μ) : α → β := hf.some

lemma fin_strongly_measurable_mk (hf : ae_fin_strongly_measurable f μ) :
  fin_strongly_measurable (hf.mk f) μ :=
hf.some_spec.1

lemma ae_eq_mk (hf : ae_fin_strongly_measurable f μ) : f =ᵐ[μ] hf.mk f :=
hf.some_spec.2

protected lemma ae_measurable {β} [has_zero β] [measurable_space β] [metric_space β] [borel_space β]
  {f : α → β} (hf : ae_fin_strongly_measurable f μ) :
  ae_measurable f μ :=
⟨hf.mk f, hf.fin_strongly_measurable_mk.measurable, hf.ae_eq_mk⟩

protected lemma ae_measurable_ennreal {f : α → ℝ≥0∞} (hf : ae_fin_strongly_measurable f μ) :
  ae_measurable f μ :=
⟨hf.mk f, hf.fin_strongly_measurable_mk.measurable_ennreal, hf.ae_eq_mk⟩

end mk

section arithmetic

protected lemma mul [monoid_with_zero β] [no_zero_divisors β] [has_continuous_mul β]
  (hf : ae_fin_strongly_measurable f μ) (hg : ae_fin_strongly_measurable g μ) :
  ae_fin_strongly_measurable (f * g) μ :=
⟨hf.mk f * hg.mk g, hf.fin_strongly_measurable_mk.mul hg.fin_strongly_measurable_mk,
  hf.ae_eq_mk.mul hg.ae_eq_mk⟩

protected lemma add [add_monoid β] [has_continuous_add β]
  (hf : ae_fin_strongly_measurable f μ) (hg : ae_fin_strongly_measurable g μ) :
  ae_fin_strongly_measurable (f + g) μ :=
⟨hf.mk f + hg.mk g, hf.fin_strongly_measurable_mk.add hg.fin_strongly_measurable_mk,
  hf.ae_eq_mk.add hg.ae_eq_mk⟩

protected lemma neg [add_group β] [topological_add_group β] (hf : ae_fin_strongly_measurable f μ) :
  ae_fin_strongly_measurable (-f) μ :=
⟨-hf.mk f, hf.fin_strongly_measurable_mk.neg, hf.ae_eq_mk.neg⟩

protected lemma sub [add_group β] [has_continuous_sub β]
  (hf : ae_fin_strongly_measurable f μ) (hg : ae_fin_strongly_measurable g μ) :
  ae_fin_strongly_measurable (f - g) μ :=
⟨hf.mk f - hg.mk g, hf.fin_strongly_measurable_mk.sub hg.fin_strongly_measurable_mk,
  hf.ae_eq_mk.sub hg.ae_eq_mk⟩

end arithmetic

variables [has_zero β] [t2_space β]

lemma exists_set_sigma_finite (hf : ae_fin_strongly_measurable f μ) :
  ∃ t, measurable_set t ∧ f =ᵐ[μ.restrict tᶜ] 0 ∧ sigma_finite (μ.restrict t) :=
begin
  rcases hf with ⟨g, hg, hfg⟩,
  obtain ⟨t, ht, hgt_zero, htμ⟩ := hg.exists_set_sigma_finite,
  refine ⟨t, ht, _, htμ⟩,
  refine eventually_eq.trans (ae_restrict_of_ae hfg) _,
  rw [eventually_eq, ae_restrict_iff' ht.compl],
  exact eventually_of_forall hgt_zero,
end

/-- A measurable set `t` such that `f =ᵐ[μ.restrict tᶜ] 0` and `sigma_finite (μ.restrict t)`. -/
def sigma_finite_set (hf : ae_fin_strongly_measurable f μ) : set α :=
hf.exists_set_sigma_finite.some

protected lemma measurable_set (hf : ae_fin_strongly_measurable f μ) :
  measurable_set hf.sigma_finite_set :=
hf.exists_set_sigma_finite.some_spec.1

lemma ae_eq_zero_compl (hf : ae_fin_strongly_measurable f μ) :
  f =ᵐ[μ.restrict hf.sigma_finite_setᶜ] 0 :=
hf.exists_set_sigma_finite.some_spec.2.1

instance sigma_finite_restrict (hf : ae_fin_strongly_measurable f μ) :
  sigma_finite (μ.restrict hf.sigma_finite_set) :=
hf.exists_set_sigma_finite.some_spec.2.2

end ae_fin_strongly_measurable

section second_countable_topology

variables {α G : Type*} {p : ℝ≥0∞} {m m0 : measurable_space α} {μ : measure α}
  [normed_group G] [measurable_space G] [borel_space G] [second_countable_topology G]
  {f : α → G}

/-- In a space with second countable topology and a sigma-finite measure, `fin_strongly_measurable`
  and `measurable` are equivalent. -/
lemma fin_strongly_measurable_iff_measurable {m0 : measurable_space α} (μ : measure α)
  [sigma_finite μ] :
  fin_strongly_measurable f μ ↔ measurable f :=
⟨λ h, h.measurable, λ h, (measurable.strongly_measurable h).fin_strongly_measurable μ⟩

/-- In a space with second countable topology and a sigma-finite measure,
  `ae_fin_strongly_measurable` and `ae_measurable` are equivalent. -/
lemma ae_fin_strongly_measurable_iff_ae_measurable {m0 : measurable_space α} (μ : measure α)
  [sigma_finite μ] :
  ae_fin_strongly_measurable f μ ↔ ae_measurable f μ :=
by simp_rw [ae_fin_strongly_measurable, ae_measurable, fin_strongly_measurable_iff_measurable]

lemma mem_ℒp.fin_strongly_measurable_of_measurable (hf : mem_ℒp f p μ) (hf_meas : measurable f)
  (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
  fin_strongly_measurable f μ :=
begin
  let fs := simple_func.approx_on f hf_meas set.univ 0 (set.mem_univ _),
  refine ⟨fs, _, _⟩,
  { have h_fs_Lp : ∀ n, mem_ℒp (fs n) p μ, from simple_func.mem_ℒp_approx_on_univ hf_meas hf,
    exact λ n, (fs n).measure_support_lt_top_of_mem_ℒp (h_fs_Lp n) hp_ne_zero hp_ne_top, },
  { exact λ x, simple_func.tendsto_approx_on hf_meas (set.mem_univ 0) (by simp), },
end

lemma mem_ℒp.ae_fin_strongly_measurable (hf : mem_ℒp f p μ) (hp_ne_zero : p ≠ 0)
  (hp_ne_top : p ≠ ∞) :
  ae_fin_strongly_measurable f μ :=
⟨hf.ae_measurable.mk f,
  ((mem_ℒp_congr_ae hf.ae_measurable.ae_eq_mk).mp hf).fin_strongly_measurable_of_measurable
    hf.ae_measurable.measurable_mk hp_ne_zero hp_ne_top,
  hf.ae_measurable.ae_eq_mk⟩

lemma integrable.ae_fin_strongly_measurable (hf : integrable f μ) :
  ae_fin_strongly_measurable f μ :=
(mem_ℒp_one_iff_integrable.mpr hf).ae_fin_strongly_measurable one_ne_zero ennreal.coe_ne_top

lemma Lp.fin_strongly_measurable (f : Lp G p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
  fin_strongly_measurable f μ :=
(Lp.mem_ℒp f).fin_strongly_measurable_of_measurable (Lp.measurable f) hp_ne_zero hp_ne_top

end second_countable_topology






section

variables {α β : Type*} {m : measurable_space α} {μ : measure α} [topological_space β]

variables (β μ)
def measure.ae_str_meas_setoid : setoid {f : α → β // ae_strongly_measurable f μ} :=
⟨λf g, (f : α → β) =ᵐ[μ] g, λ f, ae_eq_refl f, λ f g, ae_eq_symm, λ f g h, ae_eq_trans⟩

def ae_str_meas : Type* := quotient (μ.ae_str_meas_setoid β)
variables {β μ}

notation α ` →ₛₘ[`:25 μ `] ` β := ae_str_meas β μ

namespace ae_str_meas
variables {γ δ : Type*} [topological_space γ] [topological_space δ]

/-- Construct the equivalence class `[f]` of an almost everywhere strongly measurable function `f`,
  based on the equivalence relation of being almost everywhere equal. -/
def mk (f : α → β) (hf : ae_strongly_measurable f μ) : α →ₛₘ[μ] β := quotient.mk' ⟨f, hf⟩

/-- A measurable representative of an `ae_eq_fun` [f] -/
noncomputable
instance : has_coe_to_fun (α →ₛₘ[μ] β) (λ _, α → β) :=
⟨λf, ae_strongly_measurable.mk _ (quotient.out' f : {f : α → β // ae_strongly_measurable f μ}).2⟩

protected lemma strongly_measurable (f : α →ₛₘ[μ] β) : strongly_measurable f :=
ae_strongly_measurable.strongly_measurable_mk _

protected lemma ae_strongly_measurable (f : α →ₛₘ[μ] β) : ae_strongly_measurable f μ :=
f.strongly_measurable.ae_strongly_measurable

@[simp] lemma quot_mk_eq_mk (f : α → β) (hf) :
  (quot.mk (@setoid.r _ $ μ.ae_str_meas_setoid β) ⟨f, hf⟩ : α →ₛₘ[μ] β) = mk f hf :=
rfl

@[simp] lemma mk_eq_mk {f g : α → β} {hf hg} :
  (mk f hf : α →ₛₘ[μ] β) = mk g hg ↔ f =ᵐ[μ] g :=
quotient.eq'

@[simp] lemma mk_coe_fn (f : α →ₛₘ[μ] β) : mk f f.ae_strongly_measurable = f :=
begin
  conv_rhs { rw ← quotient.out_eq' f },
  set g : {f : α → β // ae_strongly_measurable f μ} := quotient.out' f with hg,
  have : g = ⟨g.1, g.2⟩ := subtype.eq rfl,
  rw [this, ← mk, mk_eq_mk],
  exact (ae_strongly_measurable.ae_eq_mk _).symm,
end

@[ext] lemma ext {f g : α →ₛₘ[μ] β} (h : f =ᵐ[μ] g) : f = g :=
by rwa [← f.mk_coe_fn, ← g.mk_coe_fn, mk_eq_mk]

lemma ext_iff {f g : α →ₛₘ[μ] β} : f = g ↔ f =ᵐ[μ] g :=
⟨λ h, by rw h, λ h, ext h⟩

lemma coe_fn_mk (f : α → β) (hf) : (mk f hf : α →ₛₘ[μ] β) =ᵐ[μ] f :=
begin
  apply (ae_strongly_measurable.ae_eq_mk _).symm.trans,
  exact @quotient.mk_out' _ (μ.ae_str_meas_setoid β) (⟨f, hf⟩ : {f // ae_strongly_measurable f μ})
end

@[elab_as_eliminator]
lemma induction_on (f : α →ₛₘ[μ] β) {p : (α →ₛₘ[μ] β) → Prop} (H : ∀ f hf, p (mk f hf)) : p f :=
quotient.induction_on' f $ subtype.forall.2 H

@[elab_as_eliminator]
lemma induction_on₂ {α' β' : Type*} [measurable_space α'] [topological_space β'] {μ' : measure α'}
  (f : α →ₛₘ[μ] β) (f' : α' →ₛₘ[μ'] β') {p : (α →ₛₘ[μ] β) → (α' →ₛₘ[μ'] β') → Prop}
  (H : ∀ f hf f' hf', p (mk f hf) (mk f' hf')) :
  p f f' :=
induction_on f $ λ f hf, induction_on f' $ H f hf

@[elab_as_eliminator]
lemma induction_on₃ {α' β' : Type*} [measurable_space α'] [topological_space β'] {μ' : measure α'}
  {α'' β'' : Type*} [measurable_space α''] [topological_space β''] {μ'' : measure α''}
  (f : α →ₛₘ[μ] β) (f' : α' →ₛₘ[μ'] β') (f'' : α'' →ₛₘ[μ''] β'')
  {p : (α →ₛₘ[μ] β) → (α' →ₛₘ[μ'] β') → (α'' →ₛₘ[μ''] β'') → Prop}
  (H : ∀ f hf f' hf' f'' hf'', p (mk f hf) (mk f' hf') (mk f'' hf'')) :
  p f f' f'' :=
induction_on f $ λ f hf, induction_on₂ f' f'' $ H f hf

/-- Interpret `f : α →ₛₘ[μ] β` as a germ at `μ.ae` forgetting that `f` is almost everywhere
    strongly measurable. -/
def to_germ (f : α →ₛₘ[μ] β) : germ μ.ae β :=
quotient.lift_on' f (λ f, ((f : α → β) : germ μ.ae β)) $ λ f g H, germ.coe_eq.2 H

@[simp] lemma mk_to_germ (f : α → β) (hf) : (mk f hf : α →ₛₘ[μ] β).to_germ = f := rfl

lemma to_germ_eq (f : α →ₛₘ[μ] β) : f.to_germ = (f : α → β) :=
by rw [← mk_to_germ, mk_coe_fn]

lemma to_germ_injective : injective (to_germ : (α →ₛₘ[μ] β) → germ μ.ae β) :=
λ f g H, ext $ germ.coe_eq.1 $ by rwa [← to_germ_eq, ← to_germ_eq]

/-- Given a predicate `p` and an equivalence class `[f]`, return true if `p` holds of `f a`
    for almost all `a` -/
def lift_pred (p : β → Prop) (f : α →ₛₘ[μ] β) : Prop := f.to_germ.lift_pred p

/-- Given a relation `r` and equivalence class `[f]` and `[g]`, return true if `r` holds of
    `(f a, g a)` for almost all `a` -/
def lift_rel (r : β → γ → Prop) (f : α →ₛₘ[μ] β) (g : α →ₛₘ[μ] γ) : Prop :=
f.to_germ.lift_rel r g.to_germ

lemma lift_rel_mk_mk {r : β → γ → Prop} {f : α → β} {g : α → γ} {hf hg} :
  lift_rel r (mk f hf : α →ₛₘ[μ] β) (mk g hg) ↔ ∀ᵐ a ∂μ, r (f a) (g a) :=
iff.rfl

lemma lift_rel_iff_coe_fn {r : β → γ → Prop} {f : α →ₛₘ[μ] β} {g : α →ₛₘ[μ] γ} :
  lift_rel r f g ↔ ∀ᵐ a ∂μ, r (f a) (g a) :=
by rw [← lift_rel_mk_mk, mk_coe_fn, mk_coe_fn]

section order

instance [preorder β] : preorder (α →ₛₘ[μ] β) := preorder.lift to_germ

@[simp] lemma mk_le_mk [preorder β] {f g : α → β} (hf hg) :
  (mk f hf : α →ₛₘ[μ] β) ≤ mk g hg ↔ f ≤ᵐ[μ] g :=
iff.rfl

@[simp, norm_cast] lemma coe_fn_le [preorder β] {f g : α →ₛₘ[μ] β} :
  (f : α → β) ≤ᵐ[μ] g ↔ f ≤ g :=
lift_rel_iff_coe_fn.symm

instance [partial_order β] : partial_order (α →ₛₘ[μ] β) :=
partial_order.lift to_germ to_germ_injective

section lattice

section sup
variables [semilattice_sup β] [has_continuous_sup β]

noncomputable instance : has_sup (α →ₛₘ[μ] β) :=
⟨λ f g, mk (f ⊔ g) (f.ae_strongly_measurable.sup g.ae_strongly_measurable)⟩

lemma coe_fn_sup (f g : α →ₛₘ[μ] β) : ⇑(f ⊔ g) =ᵐ[μ] λ x, f x ⊔ g x := coe_fn_mk _ _

protected lemma le_sup_left (f g : α →ₛₘ[μ] β) : f ≤ f ⊔ g :=
by { rw ← coe_fn_le, filter_upwards [coe_fn_sup f g] with _ ha, rw ha, exact le_sup_left, }

protected lemma le_sup_right (f g : α →ₛₘ[μ] β) : g ≤ f ⊔ g :=
by { rw ← coe_fn_le, filter_upwards [coe_fn_sup f g] with _ ha, rw ha, exact le_sup_right, }

protected lemma sup_le (f g f' : α →ₛₘ[μ] β) (hf : f ≤ f') (hg : g ≤ f') : f ⊔ g ≤ f' :=
begin
  rw ← coe_fn_le at hf hg ⊢,
  filter_upwards [hf, hg, coe_fn_sup f g] with _ haf hag ha_sup,
  rw ha_sup,
  exact sup_le haf hag,
end

end sup

section inf
variables [semilattice_inf β] [has_continuous_inf β]

noncomputable instance : has_inf (α →ₛₘ[μ] β) :=
⟨λ f g, mk (f ⊓ g) (f.ae_strongly_measurable.inf g.ae_strongly_measurable)⟩

lemma coe_fn_inf (f g : α →ₛₘ[μ] β) : ⇑(f ⊓ g) =ᵐ[μ] λ x, f x ⊓ g x := coe_fn_mk _ _

protected lemma inf_le_left (f g : α →ₛₘ[μ] β) : f ⊓ g ≤ f :=
by { rw ← coe_fn_le, filter_upwards [coe_fn_inf f g] with _ ha, rw ha, exact inf_le_left, }

protected lemma inf_le_right (f g : α →ₛₘ[μ] β) : f ⊓ g ≤ g :=
by { rw ← coe_fn_le, filter_upwards [coe_fn_inf f g] with _ ha, rw ha, exact inf_le_right, }

protected lemma le_inf (f' f g : α →ₛₘ[μ] β) (hf : f' ≤ f) (hg : f' ≤ g) : f' ≤ f ⊓ g :=
begin
  rw ← coe_fn_le at hf hg ⊢,
  filter_upwards [hf, hg, coe_fn_inf f g] with _ haf hag ha_inf,
  rw ha_inf,
  exact le_inf haf hag,
end

end inf

noncomputable instance [lattice β] [topological_lattice β] : lattice (α →ₛₘ[μ] β) :=
{ sup           := has_sup.sup,
  le_sup_left   := ae_str_meas.le_sup_left,
  le_sup_right  := ae_str_meas.le_sup_right,
  sup_le        := ae_str_meas.sup_le,
  inf           := has_inf.inf,
  inf_le_left   := ae_str_meas.inf_le_left,
  inf_le_right  := ae_str_meas.inf_le_right,
  le_inf        := ae_str_meas.le_inf,
  ..ae_str_meas.partial_order}

end lattice

end order

variable (α)
/-- The equivalence class of a constant function: `[λ a : α, b]`, based on the equivalence relation
of being almost everywhere equal -/
def const (b : β) : α →ₛₘ[μ] β := mk (λ _, b) ae_strongly_measurable_const

lemma coe_fn_const (b : β) : (const α b : α →ₛₘ[μ] β) =ᵐ[μ] function.const α b :=
coe_fn_mk _ _

variable {α}

instance [inhabited β] : inhabited (α →ₛₘ[μ] β) := ⟨const α default⟩

@[to_additive] instance [has_one β] : has_one (α →ₛₘ[μ] β) := ⟨const α 1⟩
@[to_additive] lemma one_def [has_one β] :
  (1 : α →ₛₘ[μ] β) = mk (λ _, 1) ae_strongly_measurable_const := rfl
@[to_additive] lemma coe_fn_one [has_one β] : ⇑(1 : α →ₛₘ[μ] β) =ᵐ[μ] 1 := coe_fn_const _ _
@[simp, to_additive] lemma one_to_germ [has_one β] : (1 : α →ₛₘ[μ] β).to_germ = 1 := rfl

section monoid
variables [monoid γ] [has_continuous_mul γ]

@[to_additive] noncomputable instance : has_mul (α →ₛₘ[μ] γ) :=
⟨λ f g, mk (f * g) (f.ae_strongly_measurable.mul g.ae_strongly_measurable)⟩

@[simp, to_additive] lemma mk_mul_mk (f g : α → γ) (hf hg) :
  (mk f hf : α →ₛₘ[μ] γ) * (mk g hg) = mk (f * g) (hf.mul hg) :=
begin
  change mk ((mk f hf) * (mk g hg)) _ = mk (f * g) (hf.mul hg),
  simp only [mk_eq_mk],
  exact (coe_fn_mk f hf).mul (coe_fn_mk g hg),
end

@[to_additive] lemma coe_fn_mul (f g : α →ₛₘ[μ] γ) : ⇑(f * g) =ᵐ[μ] f * g := coe_fn_mk _ _

@[simp, to_additive] lemma mul_to_germ (f g : α →ₛₘ[μ] γ) :
  (f * g).to_germ = f.to_germ * g.to_germ :=
begin
  change (mk (f * g) _).to_germ = f.to_germ * g.to_germ,
  rw [mk_to_germ, to_germ_eq, to_germ_eq, germ.coe_mul],
end

@[to_additive] noncomputable instance : monoid (α →ₛₘ[μ] γ) :=
to_germ_injective.monoid to_germ one_to_germ mul_to_germ

end monoid

@[to_additive] noncomputable instance comm_monoid [comm_monoid γ] [has_continuous_mul γ] :
  comm_monoid (α →ₛₘ[μ] γ) :=
to_germ_injective.comm_monoid to_germ one_to_germ mul_to_germ

section group

variables [group γ] [topological_group γ]

@[to_additive] noncomputable instance : has_inv (α →ₛₘ[μ] γ) :=
⟨λ f, mk f⁻¹ f.ae_strongly_measurable.inv⟩

@[simp, to_additive] lemma inv_mk (f : α → γ) (hf) : (mk f hf : α →ₛₘ[μ] γ)⁻¹ = mk f⁻¹ hf.inv :=
begin
  change mk (mk f hf)⁻¹ _ = mk f⁻¹ hf.inv,
  simp only [mk_eq_mk],
  exact (coe_fn_mk f hf).inv,
end

@[to_additive] lemma coe_fn_inv (f : α →ₛₘ[μ] γ) : ⇑(f⁻¹) =ᵐ[μ] f⁻¹ := coe_fn_mk _ _

@[to_additive] lemma inv_to_germ (f : α →ₛₘ[μ] γ) : (f⁻¹).to_germ = (f.to_germ)⁻¹ :=
begin
  change (mk f⁻¹ _).to_germ = (f.to_germ)⁻¹,
  rw [mk_to_germ, to_germ_eq, germ.coe_inv],
end

end group

section add_group
variables [add_group γ] [topological_add_group γ]

noncomputable instance : has_sub (α →ₛₘ[μ] γ) :=
⟨λ f g, mk (f - g) (f.ae_strongly_measurable.sub g.ae_strongly_measurable)⟩

@[simp] lemma mk_sub_mk (f g : α → γ) (hf hg) :
  (mk f hf : α →ₛₘ[μ] γ) - (mk g hg) = mk (f - g) (ae_strongly_measurable.sub hf hg) :=
begin
  change mk ((mk f hf) - (mk g hg)) _ = mk (f - g) (hf.sub hg),
  simp only [mk_eq_mk],
  exact (coe_fn_mk f hf).sub (coe_fn_mk g hg),
end

lemma coe_fn_sub (f g : α →ₛₘ[μ] γ) : ⇑(f - g) =ᵐ[μ] f - g := coe_fn_mk _ _

lemma sub_to_germ (f g : α →ₛₘ[μ] γ) : (f - g).to_germ = f.to_germ - g.to_germ :=
begin
  change (mk (f - g) _).to_germ = f.to_germ - g.to_germ,
  rw [mk_to_germ, to_germ_eq, to_germ_eq, germ.coe_sub],
end

noncomputable instance : add_group (α →ₛₘ[μ] γ) :=
to_germ_injective.add_group _ zero_to_germ add_to_germ neg_to_germ sub_to_germ

end add_group

noncomputable
instance [add_comm_group γ] [topological_add_group γ] : add_comm_group (α →ₛₘ[μ] γ) :=
{ .. ae_str_meas.add_group, .. ae_str_meas.add_comm_monoid }

section module

variables {𝕜 : Type*} [semiring 𝕜] [topological_space 𝕜]
variables [add_comm_monoid γ] [module 𝕜 γ] [has_continuous_smul 𝕜 γ]

noncomputable instance : has_scalar 𝕜 (α →ₛₘ[μ] γ) :=
⟨λ c f, mk (c • f) (f.ae_strongly_measurable.const_smul c)⟩

@[simp] lemma smul_mk (c : 𝕜) (f : α → γ) (hf) :
  c • (mk f hf : α →ₛₘ[μ] γ) = mk (c • f) (hf.const_smul _) :=
begin
  change mk (c • (mk f hf)) _ = mk (c • f) (hf.const_smul c),
  simp only [mk_eq_mk],
  refine (coe_fn_mk f hf).mono (λ x hx, _),
  rw [pi.smul_apply, pi.smul_apply, hx],
end

lemma coe_fn_smul (c : 𝕜) (f : α →ₛₘ[μ] γ) : ⇑(c • f) =ᵐ[μ] c • f := coe_fn_mk _ _

lemma smul_to_germ (c : 𝕜) (f : α →ₛₘ[μ] γ) : (c • f).to_germ = c • f.to_germ :=
begin
  change (mk (c • f) _).to_germ = c • f.to_germ,
  rw [mk_to_germ, to_germ_eq, germ.coe_smul],
end

noncomputable instance [has_continuous_add γ] : module 𝕜 (α →ₛₘ[μ] γ) :=
to_germ_injective.module 𝕜 ⟨@to_germ α γ _ μ _, zero_to_germ, add_to_germ⟩ smul_to_germ

end module

section lintegral
open ennreal

/-- For `f : α → ℝ≥0∞`, define `∫ [f]` to be `∫ f` -/
noncomputable def lintegral (f : α →ₛₘ[μ] ℝ≥0∞) : ℝ≥0∞ :=
quotient.lift_on' f (λf, ∫⁻ a, (f : α → ℝ≥0∞) a ∂μ) (assume f g, lintegral_congr_ae)

@[simp] lemma lintegral_mk (f : α → ℝ≥0∞) (hf) :
  (mk f hf : α →ₛₘ[μ] ℝ≥0∞).lintegral = ∫⁻ a, f a ∂μ := rfl

lemma lintegral_coe_fn (f : α →ₛₘ[μ] ℝ≥0∞) : ∫⁻ a, f a ∂μ = f.lintegral :=
by rw [← lintegral_mk, mk_coe_fn]

@[simp] lemma lintegral_zero : lintegral (0 : α →ₛₘ[μ] ℝ≥0∞) = 0 := lintegral_zero

@[simp] lemma lintegral_eq_zero_iff {f : α →ₛₘ[μ] ℝ≥0∞} : lintegral f = 0 ↔ f = 0 :=
begin
  refine induction_on f (λ f hf, _),
  rw [lintegral_mk, lintegral_eq_zero_iff' hf.ae_measurable_ennreal, zero_def, mk_eq_mk],
  refl,
end

lemma lintegral_add (f g : α →ₛₘ[μ] ℝ≥0∞) : lintegral (f + g) = lintegral f + lintegral g :=
induction_on₂ f g $ λ f hf g hg,
  by simp [lintegral_add' hf.ae_measurable_ennreal hg.ae_measurable_ennreal]

lemma lintegral_mono {f g : α →ₛₘ[μ] ℝ≥0∞} : f ≤ g → lintegral f ≤ lintegral g :=
induction_on₂ f g $ λ f hf g hg hfg, lintegral_mono_ae hfg

end lintegral

end ae_str_meas

end







section

variables {α β : Type*} {m : measurable_space α} {μ : measure α} [topological_space β]

variables (β μ)
def measure.ae_fin_str_meas_setoid [has_zero β] :
  setoid {f : α → β // ae_fin_strongly_measurable f μ} :=
⟨λf g, (f : α → β) =ᵐ[μ] g, λ f, ae_eq_refl f, λ f g, ae_eq_symm, λ f g h, ae_eq_trans⟩

def ae_fin_str_meas [has_zero β] : Type* := quotient (μ.ae_fin_str_meas_setoid β)
variables {β μ}

notation α ` →ₛₘ₀[`:25 μ `] ` β := ae_fin_str_meas β μ

namespace ae_fin_str_meas
variables {γ δ : Type*} [topological_space γ] [topological_space δ] [has_zero β]

/-- Construct the equivalence class `[f]` of an almost everywhere strongly measurable function `f`,
  based on the equivalence relation of being almost everywhere equal. -/
def mk (f : α → β) (hf : ae_fin_strongly_measurable f μ) : α →ₛₘ₀[μ] β := quotient.mk' ⟨f, hf⟩

/-- A measurable representative of an `ae_eq_fun` [f] -/
noncomputable
instance : has_coe_to_fun (α →ₛₘ₀[μ] β) (λ _, α → β) :=
⟨λf, ae_fin_strongly_measurable.mk _
  (quotient.out' f : {f : α → β // ae_fin_strongly_measurable f μ}).2⟩

protected lemma fin_strongly_measurable (f : α →ₛₘ₀[μ] β) : fin_strongly_measurable f μ :=
ae_fin_strongly_measurable.fin_strongly_measurable_mk _

protected lemma ae_fin_strongly_measurable (f : α →ₛₘ₀[μ] β) : ae_fin_strongly_measurable f μ :=
f.fin_strongly_measurable.ae_fin_strongly_measurable

@[simp] lemma quot_mk_eq_mk (f : α → β) (hf) :
  (quot.mk (@setoid.r _ $ μ.ae_fin_str_meas_setoid β) ⟨f, hf⟩ : α →ₛₘ₀[μ] β) = mk f hf :=
rfl

@[simp] lemma mk_eq_mk {f g : α → β} {hf hg} :
  (mk f hf : α →ₛₘ₀[μ] β) = mk g hg ↔ f =ᵐ[μ] g :=
quotient.eq'

@[simp] lemma mk_coe_fn (f : α →ₛₘ₀[μ] β) : mk f f.ae_fin_strongly_measurable = f :=
begin
  conv_rhs { rw ← quotient.out_eq' f },
  set g : {f : α → β // ae_fin_strongly_measurable f μ} := quotient.out' f with hg,
  have : g = ⟨g.1, g.2⟩ := subtype.eq rfl,
  rw [this, ← mk, mk_eq_mk],
  exact (ae_fin_strongly_measurable.ae_eq_mk _).symm,
end

@[ext] lemma ext {f g : α →ₛₘ₀[μ] β} (h : f =ᵐ[μ] g) : f = g :=
by rwa [← f.mk_coe_fn, ← g.mk_coe_fn, mk_eq_mk]

lemma ext_iff {f g : α →ₛₘ₀[μ] β} : f = g ↔ f =ᵐ[μ] g :=
⟨λ h, by rw h, λ h, ext h⟩

lemma coe_fn_mk (f : α → β) (hf) : (mk f hf : α →ₛₘ₀[μ] β) =ᵐ[μ] f :=
begin
  apply (ae_fin_strongly_measurable.ae_eq_mk _).symm.trans,
  exact @quotient.mk_out' _ (μ.ae_fin_str_meas_setoid β)
    (⟨f, hf⟩ : {f // ae_fin_strongly_measurable f μ})
end

@[elab_as_eliminator]
lemma induction_on (f : α →ₛₘ₀[μ] β) {p : (α →ₛₘ₀[μ] β) → Prop} (H : ∀ f hf, p (mk f hf)) : p f :=
quotient.induction_on' f $ subtype.forall.2 H

@[elab_as_eliminator]
lemma induction_on₂ {α' β' : Type*} [measurable_space α'] [topological_space β'] [has_zero β']
  {μ' : measure α'} (f : α →ₛₘ₀[μ] β) (f' : α' →ₛₘ₀[μ'] β')
  {p : (α →ₛₘ₀[μ] β) → (α' →ₛₘ₀[μ'] β') → Prop} (H : ∀ f hf f' hf', p (mk f hf) (mk f' hf')) :
  p f f' :=
induction_on f $ λ f hf, induction_on f' $ H f hf

@[elab_as_eliminator]
lemma induction_on₃ {α' β' : Type*} [measurable_space α'] [topological_space β'] [has_zero β']
  {μ' : measure α'} {α'' β'' : Type*} [measurable_space α''] [topological_space β''] [has_zero β'']
  {μ'' : measure α''} (f : α →ₛₘ₀[μ] β) (f' : α' →ₛₘ₀[μ'] β') (f'' : α'' →ₛₘ₀[μ''] β'')
  {p : (α →ₛₘ₀[μ] β) → (α' →ₛₘ₀[μ'] β') → (α'' →ₛₘ₀[μ''] β'') → Prop}
  (H : ∀ f hf f' hf' f'' hf'', p (mk f hf) (mk f' hf') (mk f'' hf'')) :
  p f f' f'' :=
induction_on f $ λ f hf, induction_on₂ f' f'' $ H f hf

/-- Interpret `f : α →ₛₘ₀[μ] β` as a germ at `μ.ae` forgetting that `f` is almost everywhere
    strongly measurable. -/
def to_germ (f : α →ₛₘ₀[μ] β) : germ μ.ae β :=
quotient.lift_on' f (λ f, ((f : α → β) : germ μ.ae β)) $ λ f g H, germ.coe_eq.2 H

@[simp] lemma mk_to_germ (f : α → β) (hf) : (mk f hf : α →ₛₘ₀[μ] β).to_germ = f := rfl

lemma to_germ_eq (f : α →ₛₘ₀[μ] β) : f.to_germ = (f : α → β) :=
by rw [← mk_to_germ, mk_coe_fn]

lemma to_germ_injective : injective (to_germ : (α →ₛₘ₀[μ] β) → germ μ.ae β) :=
λ f g H, ext $ germ.coe_eq.1 $ by rwa [← to_germ_eq, ← to_germ_eq]

/-- Given a predicate `p` and an equivalence class `[f]`, return true if `p` holds of `f a`
    for almost all `a` -/
def lift_pred (p : β → Prop) (f : α →ₛₘ₀[μ] β) : Prop := f.to_germ.lift_pred p

/-- Given a relation `r` and equivalence class `[f]` and `[g]`, return true if `r` holds of
    `(f a, g a)` for almost all `a` -/
def lift_rel [has_zero γ] (r : β → γ → Prop) (f : α →ₛₘ₀[μ] β) (g : α →ₛₘ₀[μ] γ) : Prop :=
f.to_germ.lift_rel r g.to_germ

lemma lift_rel_mk_mk [has_zero γ] {r : β → γ → Prop} {f : α → β} {g : α → γ} {hf hg} :
  lift_rel r (mk f hf : α →ₛₘ₀[μ] β) (mk g hg) ↔ ∀ᵐ a ∂μ, r (f a) (g a) :=
iff.rfl

lemma lift_rel_iff_coe_fn [has_zero γ] {r : β → γ → Prop} {f : α →ₛₘ₀[μ] β} {g : α →ₛₘ₀[μ] γ} :
  lift_rel r f g ↔ ∀ᵐ a ∂μ, r (f a) (g a) :=
by rw [← lift_rel_mk_mk, mk_coe_fn, mk_coe_fn]

section order

instance [preorder β] : preorder (α →ₛₘ₀[μ] β) := preorder.lift to_germ

@[simp] lemma mk_le_mk [preorder β] {f g : α → β} (hf hg) :
  (mk f hf : α →ₛₘ₀[μ] β) ≤ mk g hg ↔ f ≤ᵐ[μ] g :=
iff.rfl

@[simp, norm_cast] lemma coe_fn_le [preorder β] {f g : α →ₛₘ₀[μ] β} :
  (f : α → β) ≤ᵐ[μ] g ↔ f ≤ g :=
lift_rel_iff_coe_fn.symm

instance [partial_order β] : partial_order (α →ₛₘ₀[μ] β) :=
partial_order.lift to_germ to_germ_injective

section lattice

section sup
variables [semilattice_sup β] [has_continuous_sup β]

noncomputable instance : has_sup (α →ₛₘ₀[μ] β) :=
⟨λ f g, mk (f ⊔ g) (f.ae_fin_strongly_measurable.sup g.ae_fin_strongly_measurable)⟩

lemma coe_fn_sup (f g : α →ₛₘ₀[μ] β) : ⇑(f ⊔ g) =ᵐ[μ] λ x, f x ⊔ g x := coe_fn_mk _ _

protected lemma le_sup_left (f g : α →ₛₘ₀[μ] β) : f ≤ f ⊔ g :=
by { rw ← coe_fn_le, filter_upwards [coe_fn_sup f g] with _ ha, rw ha, exact le_sup_left, }

protected lemma le_sup_right (f g : α →ₛₘ₀[μ] β) : g ≤ f ⊔ g :=
by { rw ← coe_fn_le, filter_upwards [coe_fn_sup f g] with _ ha, rw ha, exact le_sup_right, }

protected lemma sup_le (f g f' : α →ₛₘ₀[μ] β) (hf : f ≤ f') (hg : g ≤ f') : f ⊔ g ≤ f' :=
begin
  rw ← coe_fn_le at hf hg ⊢,
  filter_upwards [hf, hg, coe_fn_sup f g] with _ haf hag ha_sup,
  rw ha_sup,
  exact sup_le haf hag,
end

end sup

section inf
variables [semilattice_inf β] [has_continuous_inf β]

noncomputable instance : has_inf (α →ₛₘ₀[μ] β) :=
⟨λ f g, mk (f ⊓ g) (f.ae_fin_strongly_measurable.inf g.ae_fin_strongly_measurable)⟩

lemma coe_fn_inf (f g : α →ₛₘ₀[μ] β) : ⇑(f ⊓ g) =ᵐ[μ] λ x, f x ⊓ g x := coe_fn_mk _ _

protected lemma inf_le_left (f g : α →ₛₘ₀[μ] β) : f ⊓ g ≤ f :=
by { rw ← coe_fn_le, filter_upwards [coe_fn_inf f g] with _ ha, rw ha, exact inf_le_left, }

protected lemma inf_le_right (f g : α →ₛₘ₀[μ] β) : f ⊓ g ≤ g :=
by { rw ← coe_fn_le, filter_upwards [coe_fn_inf f g] with _ ha, rw ha, exact inf_le_right, }

protected lemma le_inf (f' f g : α →ₛₘ₀[μ] β) (hf : f' ≤ f) (hg : f' ≤ g) : f' ≤ f ⊓ g :=
begin
  rw ← coe_fn_le at hf hg ⊢,
  filter_upwards [hf, hg, coe_fn_inf f g] with _ haf hag ha_inf,
  rw ha_inf,
  exact le_inf haf hag,
end

end inf

noncomputable instance [lattice β] [topological_lattice β] : lattice (α →ₛₘ₀[μ] β) :=
{ sup           := has_sup.sup,
  le_sup_left   := ae_fin_str_meas.le_sup_left,
  le_sup_right  := ae_fin_str_meas.le_sup_right,
  sup_le        := ae_fin_str_meas.sup_le,
  inf           := has_inf.inf,
  inf_le_left   := ae_fin_str_meas.inf_le_left,
  inf_le_right  := ae_fin_str_meas.inf_le_right,
  le_inf        := ae_fin_str_meas.le_inf,
  ..ae_fin_str_meas.partial_order}

end lattice

end order

variable (α)
/-- The equivalence class of a constant function: `[λ a : α, b]`, based on the equivalence relation
of being almost everywhere equal -/
def const (b : β) : α →ₛₘ₀[μ] β := mk (λ _, b) ae_fin_strongly_measurable_const

lemma coe_fn_const (b : β) : (const α b : α →ₛₘ₀[μ] β) =ᵐ[μ] function.const α b :=
coe_fn_mk _ _

variable {α}

instance [inhabited β] : inhabited (α →ₛₘ₀[μ] β) := ⟨const α default⟩

@[to_additive] instance [has_one β] : has_one (α →ₛₘ₀[μ] β) := ⟨const α 1⟩
@[to_additive] lemma one_def [has_one β] :
  (1 : α →ₛₘ₀[μ] β) = mk (λ _, 1) ae_fin_strongly_measurable_const := rfl
@[to_additive] lemma coe_fn_one [has_one β] : ⇑(1 : α →ₛₘ₀[μ] β) =ᵐ[μ] 1 := coe_fn_const _ _
@[simp] lemma one_to_germ [has_one β] : (1 : α →ₛₘ₀[μ] β).to_germ = 1 := rfl
@[simp] lemma zero_to_germ : (0 : α →ₛₘ₀[μ] β).to_germ = 0 := rfl

section monoid
variables [monoid_with_zero γ] [no_zero_divisors γ] [has_continuous_mul γ]

noncomputable instance : has_mul (α →ₛₘ₀[μ] γ) :=
⟨λ f g, mk (f * g) (f.ae_fin_strongly_measurable.mul g.ae_fin_strongly_measurable)⟩

@[simp] lemma mk_mul_mk (f g : α → γ) (hf hg) :
  (mk f hf : α →ₛₘ₀[μ] γ) * (mk g hg) = mk (f * g) (hf.mul hg) :=
begin
  change mk ((mk f hf) * (mk g hg)) _ = mk (f * g) (hf.mul hg),
  simp only [mk_eq_mk],
  exact (coe_fn_mk f hf).mul (coe_fn_mk g hg),
end

lemma coe_fn_mul (f g : α →ₛₘ₀[μ] γ) : ⇑(f * g) =ᵐ[μ] f * g := coe_fn_mk _ _

@[simp] lemma mul_to_germ (f g : α →ₛₘ₀[μ] γ) :
  (f * g).to_germ = f.to_germ * g.to_germ :=
begin
  change (mk (f * g) _).to_germ = f.to_germ * g.to_germ,
  rw [mk_to_germ, to_germ_eq, to_germ_eq, germ.coe_mul],
end

noncomputable instance : monoid (α →ₛₘ₀[μ] γ) :=
to_germ_injective.monoid to_germ one_to_germ mul_to_germ

end monoid

noncomputable instance comm_monoid [comm_monoid_with_zero γ] [no_zero_divisors γ]
  [has_continuous_mul γ] :
  comm_monoid (α →ₛₘ₀[μ] γ) :=
to_germ_injective.comm_monoid to_germ one_to_germ mul_to_germ

section add_monoid
variables [add_monoid γ] [has_continuous_add γ]

noncomputable instance : has_add (α →ₛₘ₀[μ] γ) :=
⟨λ f g, mk (f + g) (f.ae_fin_strongly_measurable.add g.ae_fin_strongly_measurable)⟩

@[simp] lemma mk_add_mk (f g : α → γ) (hf hg) :
  (mk f hf : α →ₛₘ₀[μ] γ) + (mk g hg) = mk (f + g) (hf.add hg) :=
begin
  change mk ((mk f hf) + (mk g hg)) _ = mk (f + g) (hf.add hg),
  simp only [mk_eq_mk],
  exact (coe_fn_mk f hf).add (coe_fn_mk g hg),
end

lemma coe_fn_add (f g : α →ₛₘ₀[μ] γ) : ⇑(f + g) =ᵐ[μ] f + g := coe_fn_mk _ _

@[simp] lemma add_to_germ (f g : α →ₛₘ₀[μ] γ) :
  (f + g).to_germ = f.to_germ + g.to_germ :=
begin
  change (mk (f + g) _).to_germ = f.to_germ + g.to_germ,
  rw [mk_to_germ, to_germ_eq, to_germ_eq, germ.coe_add],
end

noncomputable instance : add_monoid (α →ₛₘ₀[μ] γ) :=
to_germ_injective.add_monoid to_germ zero_to_germ add_to_germ

end add_monoid

noncomputable instance add_comm_monoid [add_comm_monoid γ] [has_continuous_add γ] :
  add_comm_monoid (α →ₛₘ₀[μ] γ) :=
to_germ_injective.add_comm_monoid to_germ zero_to_germ add_to_germ

section add_group
variables [add_group γ] [topological_add_group γ]

noncomputable instance : has_neg (α →ₛₘ₀[μ] γ) :=
⟨λ f, mk (-f) f.ae_fin_strongly_measurable.neg⟩

@[simp] lemma neg_mk (f : α → γ) (hf) : - (mk f hf : α →ₛₘ₀[μ] γ) = mk (-f) hf.neg :=
by { change mk (-(mk f hf)) _ = mk (-f) hf.neg, simp only [mk_eq_mk], exact (coe_fn_mk f hf).neg, }

lemma coe_fn_neg (f : α →ₛₘ₀[μ] γ) : ⇑(-f) =ᵐ[μ] -f := coe_fn_mk _ _

lemma neg_to_germ (f : α →ₛₘ₀[μ] γ) : (-f).to_germ = - f.to_germ :=
by { change (mk (-f) _).to_germ = - f.to_germ, rw [mk_to_germ, to_germ_eq, germ.coe_neg], }

noncomputable instance : has_sub (α →ₛₘ₀[μ] γ) :=
⟨λ f g, mk (f - g) (f.ae_fin_strongly_measurable.sub g.ae_fin_strongly_measurable)⟩

@[simp] lemma mk_sub_mk (f g : α → γ) (hf hg) :
  (mk f hf : α →ₛₘ₀[μ] γ) - (mk g hg) = mk (f - g) (hf.sub hg) :=
begin
  change mk ((mk f hf) - (mk g hg)) _ = mk (f - g) (hf.sub hg),
  simp only [mk_eq_mk],
  exact (coe_fn_mk f hf).sub (coe_fn_mk g hg),
end

lemma coe_fn_sub (f g : α →ₛₘ₀[μ] γ) : ⇑(f - g) =ᵐ[μ] f - g := coe_fn_mk _ _

lemma sub_to_germ (f g : α →ₛₘ₀[μ] γ) : (f - g).to_germ = f.to_germ - g.to_germ :=
begin
  change (mk (f - g) _).to_germ = f.to_germ - g.to_germ,
  rw [mk_to_germ, to_germ_eq, to_germ_eq, germ.coe_sub],
end

noncomputable instance : add_group (α →ₛₘ₀[μ] γ) :=
to_germ_injective.add_group _ zero_to_germ add_to_germ neg_to_germ sub_to_germ

end add_group

noncomputable
instance [add_comm_group γ] [topological_add_group γ] : add_comm_group (α →ₛₘ₀[μ] γ) :=
{ .. ae_fin_str_meas.add_group, .. ae_fin_str_meas.add_comm_monoid }

section module

variables {𝕜 : Type*} [semiring 𝕜] [topological_space 𝕜]
variables [add_comm_monoid γ] [module 𝕜 γ] [has_continuous_smul 𝕜 γ]

noncomputable instance : has_scalar 𝕜 (α →ₛₘ₀[μ] γ) :=
⟨λ c f, mk (c • f) (f.ae_fin_strongly_measurable.const_smul c)⟩

@[simp] lemma smul_mk (c : 𝕜) (f : α → γ) (hf) :
  c • (mk f hf : α →ₛₘ₀[μ] γ) = mk (c • f) (hf.const_smul _) :=
begin
  change mk (c • (mk f hf)) _ = mk (c • f) (hf.const_smul c),
  simp only [mk_eq_mk],
  refine (coe_fn_mk f hf).mono (λ x hx, _),
  rw [pi.smul_apply, pi.smul_apply, hx],
end

lemma coe_fn_smul (c : 𝕜) (f : α →ₛₘ₀[μ] γ) : ⇑(c • f) =ᵐ[μ] c • f := coe_fn_mk _ _

lemma smul_to_germ (c : 𝕜) (f : α →ₛₘ₀[μ] γ) : (c • f).to_germ = c • f.to_germ :=
begin
  change (mk (c • f) _).to_germ = c • f.to_germ,
  rw [mk_to_germ, to_germ_eq, germ.coe_smul],
end

noncomputable instance [has_continuous_add γ] : module 𝕜 (α →ₛₘ₀[μ] γ) :=
to_germ_injective.module 𝕜 ⟨@to_germ α γ _ μ _ _, zero_to_germ, add_to_germ⟩ smul_to_germ

end module

section lintegral
open ennreal

/-- For `f : α → ℝ≥0∞`, define `∫ [f]` to be `∫ f` -/
noncomputable def lintegral (f : α →ₛₘ₀[μ] ℝ≥0∞) : ℝ≥0∞ :=
quotient.lift_on' f (λf, ∫⁻ a, (f : α → ℝ≥0∞) a ∂μ) (assume f g, lintegral_congr_ae)

@[simp] lemma lintegral_mk (f : α → ℝ≥0∞) (hf) :
  (mk f hf : α →ₛₘ₀[μ] ℝ≥0∞).lintegral = ∫⁻ a, f a ∂μ := rfl

lemma lintegral_coe_fn (f : α →ₛₘ₀[μ] ℝ≥0∞) : ∫⁻ a, f a ∂μ = f.lintegral :=
by rw [← lintegral_mk, mk_coe_fn]

@[simp] lemma lintegral_zero : lintegral (0 : α →ₛₘ₀[μ] ℝ≥0∞) = 0 := lintegral_zero

@[simp] lemma lintegral_eq_zero_iff {f : α →ₛₘ₀[μ] ℝ≥0∞} : lintegral f = 0 ↔ f = 0 :=
begin
  refine induction_on f (λ f hf, _),
  rw [lintegral_mk, lintegral_eq_zero_iff' hf.ae_measurable_ennreal, zero_def, mk_eq_mk],
  refl,
end

lemma lintegral_add (f g : α →ₛₘ₀[μ] ℝ≥0∞) : lintegral (f + g) = lintegral f + lintegral g :=
induction_on₂ f g $ λ f hf g hg,
  by simp [lintegral_add' hf.ae_measurable_ennreal hg.ae_measurable_ennreal]

lemma lintegral_mono {f g : α →ₛₘ₀[μ] ℝ≥0∞} : f ≤ g → lintegral f ≤ lintegral g :=
induction_on₂ f g $ λ f hf g hg hfg, lintegral_mono_ae hfg

end lintegral

end ae_fin_str_meas

end





end measure_theory
