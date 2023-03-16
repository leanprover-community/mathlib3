/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
import analysis.normed_space.bounded_linear_maps
import topology.metric_space.metrizable
import measure_theory.function.simple_func_dense

/-!
# Strongly measurable and finitely strongly measurable functions

A function `f` is said to be strongly measurable if `f` is the sequential limit of simple functions.
It is said to be finitely strongly measurable with respect to a measure `μ` if the supports
of those simple functions have finite measure. We also provide almost everywhere versions of
these notions.

Almost everywhere strongly measurable functions form the largest class of functions that can be
integrated using the Bochner integral.

If the target space has a second countable topology, strongly measurable and measurable are
equivalent.

If the measure is sigma-finite, strongly measurable and finitely strongly measurable are equivalent.

The main property of finitely strongly measurable functions is
`fin_strongly_measurable.exists_set_sigma_finite`: there exists a measurable set `t` such that the
function is supported on `t` and `μ.restrict t` is sigma-finite. As a consequence, we can prove some
results for those functions as if the measure was sigma-finite.

## Main definitions

* `strongly_measurable f`: `f : α → β` is the limit of a sequence `fs : ℕ → simple_func α β`.
* `fin_strongly_measurable f μ`: `f : α → β` is the limit of a sequence `fs : ℕ → simple_func α β`
  such that for all `n ∈ ℕ`, the measure of the support of `fs n` is finite.
* `ae_strongly_measurable f μ`: `f` is almost everywhere equal to a `strongly_measurable` function.
* `ae_fin_strongly_measurable f μ`: `f` is almost everywhere equal to a `fin_strongly_measurable`
  function.

* `ae_fin_strongly_measurable.sigma_finite_set`: a measurable set `t` such that
  `f =ᵐ[μ.restrict tᶜ] 0` and `μ.restrict t` is sigma-finite.

## Main statements

* `ae_fin_strongly_measurable.exists_set_sigma_finite`: there exists a measurable set `t` such that
  `f =ᵐ[μ.restrict tᶜ] 0` and `μ.restrict t` is sigma-finite.

We provide a solid API for strongly measurable functions, and for almost everywhere strongly
measurable functions, as a basis for the Bochner integral.

## References

* Hytönen, Tuomas, Jan Van Neerven, Mark Veraar, and Lutz Weis. Analysis in Banach spaces.
  Springer, 2016.

-/

open measure_theory filter topological_space function set measure_theory.measure
open_locale ennreal topology measure_theory nnreal big_operators

/-- The typeclass `second_countable_topology_either α β` registers the fact that at least one of
the two spaces has second countable topology. This is the right assumption to ensure that continuous
maps from `α` to `β` are strongly measurable. -/
class second_countable_topology_either
  (α β : Type*) [topological_space α] [topological_space β] : Prop :=
(out : second_countable_topology α ∨ second_countable_topology β)

@[priority 100] instance second_countable_topology_either_of_left
  (α β : Type*) [topological_space α] [topological_space β] [second_countable_topology α] :
  second_countable_topology_either α β :=
{ out := or.inl (by apply_instance) }

@[priority 100] instance second_countable_topology_either_of_right
  (α β : Type*) [topological_space α] [topological_space β] [second_countable_topology β] :
  second_countable_topology_either α β :=
{ out := or.inr (by apply_instance) }

variables {α β γ ι : Type*} [countable ι]
namespace measure_theory

local infixr ` →ₛ `:25 := simple_func

section definitions
variable [topological_space β]

/-- A function is `strongly_measurable` if it is the limit of simple functions. -/
def strongly_measurable [measurable_space α] (f : α → β) : Prop :=
∃ fs : ℕ → α →ₛ β, ∀ x, tendsto (λ n, fs n x) at_top (𝓝 (f x))

localized "notation (name := strongly_measurable_of)
  `strongly_measurable[` m `]` := @measure_theory.strongly_measurable _ _ _ m" in measure_theory

/-- A function is `fin_strongly_measurable` with respect to a measure if it is the limit of simple
  functions with support with finite measure. -/
def fin_strongly_measurable [has_zero β] {m0 : measurable_space α} (f : α → β) (μ : measure α) :
  Prop :=
∃ fs : ℕ → α →ₛ β, (∀ n, μ (support (fs n)) < ∞) ∧ (∀ x, tendsto (λ n, fs n x) at_top (𝓝 (f x)))

/-- A function is `ae_strongly_measurable` with respect to a measure `μ` if it is almost everywhere
equal to the limit of a sequence of simple functions. -/
def ae_strongly_measurable {m0 : measurable_space α} (f : α → β) (μ : measure α) : Prop :=
∃ g, strongly_measurable g ∧ f =ᵐ[μ] g

/-- A function is `ae_fin_strongly_measurable` with respect to a measure if it is almost everywhere
equal to the limit of a sequence of simple functions with support with finite measure. -/
def ae_fin_strongly_measurable [has_zero β] {m0 : measurable_space α} (f : α → β) (μ : measure α) :
  Prop :=
∃ g, fin_strongly_measurable g μ ∧ f =ᵐ[μ] g

end definitions

open_locale measure_theory

/-! ## Strongly measurable functions -/

protected lemma strongly_measurable.ae_strongly_measurable {α β} {m0 : measurable_space α}
  [topological_space β] {f : α → β} {μ : measure α} (hf : strongly_measurable f) :
  ae_strongly_measurable f μ :=
⟨f, hf, eventually_eq.refl _ _⟩

@[simp] lemma subsingleton.strongly_measurable {α β} [measurable_space α] [topological_space β]
  [subsingleton β] (f : α → β) :
  strongly_measurable f :=
begin
  let f_sf : α →ₛ β := ⟨f, λ x, _, set.subsingleton.finite set.subsingleton_of_subsingleton⟩,
  { exact ⟨λ n, f_sf, λ x, tendsto_const_nhds⟩, },
  { have h_univ : f ⁻¹' {x} = set.univ, by { ext1 y, simp, },
    rw h_univ,
    exact measurable_set.univ, },
end

lemma simple_func.strongly_measurable {α β} {m : measurable_space α} [topological_space β]
  (f : α →ₛ β) :
  strongly_measurable f :=
⟨λ _, f, λ x, tendsto_const_nhds⟩

lemma strongly_measurable_of_is_empty [is_empty α] {m : measurable_space α} [topological_space β]
  (f : α → β) : strongly_measurable f :=
⟨λ n, simple_func.of_is_empty, is_empty_elim⟩

lemma strongly_measurable_const {α β} {m : measurable_space α} [topological_space β] {b : β} :
  strongly_measurable (λ a : α, b) :=
⟨λ n, simple_func.const α b, λ a, tendsto_const_nhds⟩

@[to_additive]
lemma strongly_measurable_one {α β} {m : measurable_space α} [topological_space β] [has_one β] :
  strongly_measurable (1 : α → β) :=
@strongly_measurable_const _ _ _ _ 1

/-- A version of `strongly_measurable_const` that assumes `f x = f y` for all `x, y`.
This version works for functions between empty types. -/
lemma strongly_measurable_const' {α β} {m : measurable_space α} [topological_space β] {f : α → β}
  (hf : ∀ x y, f x = f y) : strongly_measurable f :=
begin
  casesI is_empty_or_nonempty α,
  { exact strongly_measurable_of_is_empty f },
  { convert strongly_measurable_const, exact funext (λ x, hf x h.some) }
end

@[simp] lemma subsingleton.strongly_measurable' {α β} [measurable_space α] [topological_space β]
  [subsingleton α] (f : α → β) :
  strongly_measurable f :=
strongly_measurable_const' (λ x y, by rw subsingleton.elim x y)

namespace strongly_measurable

variables {f g : α → β}

section basic_properties_in_any_topological_space
variables [topological_space β]

/-- A sequence of simple functions such that `∀ x, tendsto (λ n, hf.approx n x) at_top (𝓝 (f x))`.
That property is given by `strongly_measurable.tendsto_approx`. -/
protected noncomputable
def approx {m : measurable_space α} (hf : strongly_measurable f) : ℕ → α →ₛ β :=
hf.some

protected lemma tendsto_approx {m : measurable_space α} (hf : strongly_measurable f) :
  ∀ x, tendsto (λ n, hf.approx n x) at_top (𝓝 (f x)) :=
hf.some_spec

/-- Similar to `strongly_measurable.approx`, but enforces that the norm of every function in the
sequence is less than `c` everywhere. If `‖f x‖ ≤ c` this sequence of simple functions verifies
`tendsto (λ n, hf.approx_bounded n x) at_top (𝓝 (f x))`. -/
noncomputable
def approx_bounded {m : measurable_space α}
  [has_norm β] [has_smul ℝ β] (hf : strongly_measurable f) (c : ℝ) :
  ℕ → simple_func α β :=
λ n, (hf.approx n).map (λ x, (min 1 (c / ‖x‖)) • x)

lemma tendsto_approx_bounded_of_norm_le {β} {f : α → β} [normed_add_comm_group β] [normed_space ℝ β]
  {m : measurable_space α} (hf : strongly_measurable[m] f) {c : ℝ} {x : α} (hfx : ‖f x‖ ≤ c) :
  tendsto (λ n, hf.approx_bounded c n x) at_top (𝓝 (f x)) :=
begin
  have h_tendsto := hf.tendsto_approx x,
  simp only [strongly_measurable.approx_bounded, simple_func.coe_map, function.comp_app],
  by_cases hfx0 : ‖f x‖ = 0,
  { rw norm_eq_zero at hfx0,
    rw hfx0 at h_tendsto ⊢,
    have h_tendsto_norm : tendsto (λ n, ‖hf.approx n x‖) at_top (𝓝 0),
    { convert h_tendsto.norm,
      rw norm_zero, },
    refine squeeze_zero_norm (λ n, _) h_tendsto_norm,
    calc ‖min 1 (c / ‖hf.approx n x‖) • hf.approx n x‖
        = ‖min 1 (c / ‖hf.approx n x‖)‖ * ‖hf.approx n x‖ : norm_smul _ _
    ... ≤ ‖(1 : ℝ)‖ * ‖hf.approx n x‖ :
      begin
        refine mul_le_mul_of_nonneg_right _ (norm_nonneg _),
        rw [norm_one, real.norm_of_nonneg],
        { exact min_le_left _ _, },
        { exact le_min zero_le_one
            (div_nonneg ((norm_nonneg _).trans hfx) (norm_nonneg _)), },
      end
    ... = ‖hf.approx n x‖ : by rw [norm_one, one_mul], },
  rw ← one_smul ℝ (f x),
  refine tendsto.smul _ h_tendsto,
  have : min 1 (c / ‖f x‖) = 1,
  { rw [min_eq_left_iff, one_le_div (lt_of_le_of_ne (norm_nonneg _) (ne.symm hfx0))],
    exact hfx, },
  nth_rewrite 0 this.symm,
  refine tendsto.min tendsto_const_nhds _,
  refine tendsto.div tendsto_const_nhds h_tendsto.norm hfx0,
end

lemma tendsto_approx_bounded_ae {β} {f : α → β} [normed_add_comm_group β] [normed_space ℝ β]
  {m m0 : measurable_space α} {μ : measure α}
  (hf : strongly_measurable[m] f) {c : ℝ}
  (hf_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ c) :
  ∀ᵐ x ∂μ, tendsto (λ n, hf.approx_bounded c n x) at_top (𝓝 (f x)) :=
by filter_upwards [hf_bound] with x hfx using tendsto_approx_bounded_of_norm_le hf hfx

lemma norm_approx_bounded_le {β} {f : α → β} [seminormed_add_comm_group β] [normed_space ℝ β]
  {m : measurable_space α} {c : ℝ} (hf : strongly_measurable[m] f) (hc : 0 ≤ c) (n : ℕ) (x : α) :
  ‖hf.approx_bounded c n x‖ ≤ c :=
begin
  simp only [strongly_measurable.approx_bounded, simple_func.coe_map, function.comp_app],
  refine (norm_smul _ _).le.trans _,
  by_cases h0 : ‖hf.approx n x‖ = 0,
  { simp only [h0, div_zero, min_eq_right, zero_le_one, norm_zero, mul_zero],
    exact hc, },
  cases le_total (‖hf.approx n x‖) c,
  { rw min_eq_left _,
    { simpa only [norm_one, one_mul] using h, },
    { rwa one_le_div (lt_of_le_of_ne (norm_nonneg _) (ne.symm h0)), }, },
  { rw min_eq_right _,
    { rw [norm_div, norm_norm, mul_comm, mul_div, div_eq_mul_inv, mul_comm, ← mul_assoc,
        inv_mul_cancel h0, one_mul, real.norm_of_nonneg hc], },
    { rwa div_le_one (lt_of_le_of_ne (norm_nonneg _) (ne.symm h0)), }, },
end

lemma _root_.strongly_measurable_bot_iff [nonempty β] [t2_space β] :
  strongly_measurable[⊥] f ↔ ∃ c, f = λ _, c :=
begin
  casesI is_empty_or_nonempty α with hα hα,
  { simp only [subsingleton.strongly_measurable', eq_iff_true_of_subsingleton, exists_const], },
  refine ⟨λ hf, _, λ hf_eq, _⟩,
  { refine ⟨f hα.some, _⟩,
    let fs := hf.approx,
    have h_fs_tendsto : ∀ x, tendsto (λ n, fs n x) at_top (𝓝 (f x)) := hf.tendsto_approx,
    have : ∀ n, ∃ c, ∀ x, fs n x = c := λ n, simple_func.simple_func_bot (fs n),
    let cs := λ n, (this n).some,
    have h_cs_eq : ∀ n, ⇑(fs n) = (λ x, cs n) := λ n, funext (this n).some_spec,
    simp_rw h_cs_eq at h_fs_tendsto,
    have h_tendsto : tendsto cs at_top (𝓝 (f hα.some)) := h_fs_tendsto hα.some,
    ext1 x,
    exact tendsto_nhds_unique (h_fs_tendsto x) h_tendsto, },
  { obtain ⟨c, rfl⟩ := hf_eq,
    exact strongly_measurable_const, },
end

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
      { rsuffices ⟨n, hn⟩ : ∃ n, ∀ m, n ≤ m → x ∈ S m,
        { exact ⟨n, λ m hnm, set.mem_inter (hn m hnm) hxt⟩, },
        rsuffices ⟨n, hn⟩ : ∃ n, x ∈ S n,
        { exact ⟨n, λ m hnm, monotone_spanning_sets (μ.restrict t) hnm hn⟩, },
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
protected lemma measurable {m : measurable_space α} [topological_space β]
  [pseudo_metrizable_space β] [measurable_space β] [borel_space β] (hf : strongly_measurable f) :
  measurable f :=
measurable_of_tendsto_metrizable (λ n, (hf.approx n).measurable)
  (tendsto_pi_nhds.mpr hf.tendsto_approx)

/-- A strongly measurable function is almost everywhere measurable. -/
protected lemma ae_measurable {m : measurable_space α} [topological_space β]
  [pseudo_metrizable_space β] [measurable_space β] [borel_space β] {μ : measure α}
  (hf : strongly_measurable f) :
  ae_measurable f μ :=
hf.measurable.ae_measurable

lemma _root_.continuous.comp_strongly_measurable
  {m : measurable_space α} [topological_space β] [topological_space γ] {g : β → γ} {f : α → β}
  (hg : continuous g) (hf : strongly_measurable f) : strongly_measurable (λ x, g (f x)) :=
⟨λ n, simple_func.map g (hf.approx n), λ x, (hg.tendsto _).comp (hf.tendsto_approx x)⟩

@[to_additive]
lemma measurable_set_mul_support {m : measurable_space α}
  [has_one β] [topological_space β] [metrizable_space β] (hf : strongly_measurable f) :
  measurable_set (mul_support f) :=
by { borelize β, exact measurable_set_mul_support hf.measurable }

protected lemma mono {m m' : measurable_space α} [topological_space β]
  (hf : strongly_measurable[m'] f) (h_mono : m' ≤ m) :
  strongly_measurable[m] f :=
begin
  let f_approx : ℕ → @simple_func α m β := λ n,
  { to_fun := hf.approx n,
    measurable_set_fiber' := λ x, h_mono _ (simple_func.measurable_set_fiber' _ x),
    finite_range' := simple_func.finite_range (hf.approx n) },
  exact ⟨f_approx, hf.tendsto_approx⟩,
end

protected lemma prod_mk {m : measurable_space α} [topological_space β] [topological_space γ]
  {f : α → β} {g : α → γ} (hf : strongly_measurable f) (hg : strongly_measurable g) :
  strongly_measurable (λ x, (f x, g x)) :=
begin
  refine ⟨λ n, simple_func.pair (hf.approx n) (hg.approx n), λ x, _⟩,
  rw nhds_prod_eq,
  exact tendsto.prod_mk (hf.tendsto_approx x) (hg.tendsto_approx x),
end

lemma comp_measurable [topological_space β] {m : measurable_space α} {m' : measurable_space γ}
  {f : α → β} {g : γ → α} (hf : strongly_measurable f) (hg : measurable g) :
  strongly_measurable (f ∘ g) :=
⟨λ n, simple_func.comp (hf.approx n) g hg, λ x, hf.tendsto_approx (g x)⟩

lemma of_uncurry_left [topological_space β] {mα : measurable_space α} {mγ : measurable_space γ}
  {f : α → γ → β} (hf : strongly_measurable (uncurry f)) {x : α} :
  strongly_measurable (f x) :=
hf.comp_measurable measurable_prod_mk_left

lemma of_uncurry_right [topological_space β] {mα : measurable_space α} {mγ : measurable_space γ}
  {f : α → γ → β} (hf : strongly_measurable (uncurry f)) {y : γ} :
  strongly_measurable (λ x, f x y) :=
hf.comp_measurable measurable_prod_mk_right

section arithmetic
variables {mα : measurable_space α} [topological_space β]
include mα

@[to_additive]
protected lemma mul [has_mul β] [has_continuous_mul β]
  (hf : strongly_measurable f) (hg : strongly_measurable g) :
  strongly_measurable (f * g) :=
⟨λ n, hf.approx n * hg.approx n, λ x, (hf.tendsto_approx x).mul (hg.tendsto_approx x)⟩

@[to_additive]
lemma mul_const [has_mul β] [has_continuous_mul β] (hf : strongly_measurable f) (c : β) :
  strongly_measurable (λ x, f x * c) :=
hf.mul strongly_measurable_const

@[to_additive]
lemma const_mul [has_mul β] [has_continuous_mul β] (hf : strongly_measurable f) (c : β) :
  strongly_measurable (λ x, c * f x) :=
strongly_measurable_const.mul hf

@[to_additive]
protected lemma inv [group β] [topological_group β] (hf : strongly_measurable f) :
  strongly_measurable f⁻¹ :=
⟨λ n, (hf.approx n)⁻¹, λ x, (hf.tendsto_approx x).inv⟩

@[to_additive]
protected lemma div [has_div β] [has_continuous_div β]
  (hf : strongly_measurable f) (hg : strongly_measurable g) :
  strongly_measurable (f / g) :=
⟨λ n, hf.approx n / hg.approx n, λ x, (hf.tendsto_approx x).div' (hg.tendsto_approx x)⟩

@[to_additive]
protected lemma smul {𝕜} [topological_space 𝕜] [has_smul 𝕜 β] [has_continuous_smul 𝕜 β]
  {f : α → 𝕜} {g : α → β} (hf : strongly_measurable f) (hg : strongly_measurable g) :
  strongly_measurable (λ x, f x • g x) :=
continuous_smul.comp_strongly_measurable (hf.prod_mk hg)

protected lemma const_smul {𝕜} [has_smul 𝕜 β] [has_continuous_const_smul 𝕜 β]
  (hf : strongly_measurable f) (c : 𝕜) :
  strongly_measurable (c • f) :=
⟨λ n, c • (hf.approx n), λ x, (hf.tendsto_approx x).const_smul c⟩

protected lemma const_smul' {𝕜} [has_smul 𝕜 β] [has_continuous_const_smul 𝕜 β]
  (hf : strongly_measurable f) (c : 𝕜) :
  strongly_measurable (λ x, c • (f x)) :=
hf.const_smul c

@[to_additive]
protected lemma smul_const {𝕜} [topological_space 𝕜] [has_smul 𝕜 β] [has_continuous_smul 𝕜 β]
  {f : α → 𝕜} (hf : strongly_measurable f) (c : β) :
  strongly_measurable (λ x, f x • c) :=
continuous_smul.comp_strongly_measurable (hf.prod_mk strongly_measurable_const)

end arithmetic

section mul_action

variables [topological_space β] {G : Type*} [group G] [mul_action G β]
  [has_continuous_const_smul G β]

lemma _root_.strongly_measurable_const_smul_iff {m : measurable_space α} (c : G) :
  strongly_measurable (λ x, c • f x) ↔ strongly_measurable f :=
⟨λ h, by simpa only [inv_smul_smul] using h.const_smul' c⁻¹, λ h, h.const_smul c⟩

variables {G₀ : Type*} [group_with_zero G₀] [mul_action G₀ β]
  [has_continuous_const_smul G₀ β]

lemma _root_.strongly_measurable_const_smul_iff₀ {m : measurable_space α} {c : G₀} (hc : c ≠ 0) :
  strongly_measurable (λ x, c • f x) ↔ strongly_measurable f :=
begin
  refine ⟨λ h, _, λ h, h.const_smul c⟩,
  convert h.const_smul' c⁻¹,
  simp [smul_smul, inv_mul_cancel hc]
end

end mul_action

section order
variables [measurable_space α] [topological_space β]

open filter
open_locale filter

protected lemma sup [has_sup β] [has_continuous_sup β] (hf : strongly_measurable f)
  (hg : strongly_measurable g) :
  strongly_measurable (f ⊔ g) :=
⟨λ n, hf.approx n ⊔ hg.approx n, λ x, (hf.tendsto_approx x).sup_right_nhds (hg.tendsto_approx x)⟩

protected lemma inf [has_inf β] [has_continuous_inf β] (hf : strongly_measurable f)
  (hg : strongly_measurable g) :
  strongly_measurable (f ⊓ g) :=
⟨λ n, hf.approx n ⊓ hg.approx n, λ x, (hf.tendsto_approx x).inf_right_nhds (hg.tendsto_approx x)⟩

end order

/-!
### Big operators: `∏` and `∑`
-/

section monoid
variables {M : Type*} [monoid M] [topological_space M] [has_continuous_mul M]
  {m : measurable_space α}

include m

@[to_additive]
lemma _root_.list.strongly_measurable_prod'
  (l : list (α → M)) (hl : ∀ f ∈ l, strongly_measurable f) :
  strongly_measurable l.prod :=
begin
  induction l with f l ihl, { exact strongly_measurable_one },
  rw [list.forall_mem_cons] at hl,
  rw [list.prod_cons],
  exact hl.1.mul (ihl hl.2)
end

@[to_additive]
lemma _root_.list.strongly_measurable_prod
  (l : list (α → M)) (hl : ∀ f ∈ l, strongly_measurable f) :
  strongly_measurable (λ x, (l.map (λ f : α → M, f x)).prod) :=
by simpa only [← pi.list_prod_apply] using l.strongly_measurable_prod' hl

end monoid

section comm_monoid
variables {M : Type*} [comm_monoid M] [topological_space M] [has_continuous_mul M]
  {m : measurable_space α}

include m

@[to_additive]
lemma _root_.multiset.strongly_measurable_prod'
  (l : multiset (α → M)) (hl : ∀ f ∈ l, strongly_measurable f) :
  strongly_measurable l.prod :=
by { rcases l with ⟨l⟩, simpa using l.strongly_measurable_prod' (by simpa using hl) }

@[to_additive]
lemma _root_.multiset.strongly_measurable_prod
  (s : multiset (α → M)) (hs : ∀ f ∈ s, strongly_measurable f) :
  strongly_measurable (λ x, (s.map (λ f : α → M, f x)).prod) :=
by simpa only [← pi.multiset_prod_apply] using s.strongly_measurable_prod' hs

@[to_additive]
lemma _root_.finset.strongly_measurable_prod'
  {ι : Type*} {f : ι → α → M} (s : finset ι) (hf : ∀i ∈ s, strongly_measurable (f i)) :
  strongly_measurable (∏ i in s, f i) :=
finset.prod_induction _ _ (λ a b ha hb, ha.mul hb) (@strongly_measurable_one α M _ _ _) hf

@[to_additive]
lemma _root_.finset.strongly_measurable_prod
  {ι : Type*} {f : ι → α → M} (s : finset ι) (hf : ∀i ∈ s, strongly_measurable (f i)) :
  strongly_measurable (λ a, ∏ i in s, f i a) :=
by simpa only [← finset.prod_apply] using s.strongly_measurable_prod' hf

end comm_monoid

/-- The range of a strongly measurable function is separable. -/
lemma is_separable_range {m : measurable_space α} [topological_space β]
  (hf : strongly_measurable f) :
  topological_space.is_separable (range f) :=
begin
  have : is_separable (closure (⋃ n, range (hf.approx n))) :=
    (is_separable_Union (λ n, (simple_func.finite_range (hf.approx n)).is_separable)).closure,
  apply this.mono,
  rintros _ ⟨x, rfl⟩,
  apply mem_closure_of_tendsto (hf.tendsto_approx x),
  apply eventually_of_forall (λ n, _),
  apply mem_Union_of_mem n,
  exact mem_range_self _
end

lemma separable_space_range_union_singleton {m : measurable_space α} [topological_space β]
  [pseudo_metrizable_space β] (hf : strongly_measurable f) {b : β} :
  separable_space (range f ∪ {b} : set β) :=
begin
  letI := pseudo_metrizable_space_pseudo_metric β,
  exact (hf.is_separable_range.union (finite_singleton _).is_separable).separable_space
end

section second_countable_strongly_measurable

variables {mα : measurable_space α} [measurable_space β]
include mα

/-- In a space with second countable topology, measurable implies strongly measurable. -/
lemma _root_.measurable.strongly_measurable [topological_space β] [pseudo_metrizable_space β]
  [second_countable_topology β] [opens_measurable_space β] (hf : measurable f) :
  strongly_measurable f :=
begin
  letI := pseudo_metrizable_space_pseudo_metric β,
  rcases is_empty_or_nonempty β; resetI,
  { exact subsingleton.strongly_measurable f, },
  { inhabit β,
    exact ⟨simple_func.approx_on f hf set.univ default (set.mem_univ _),
      λ x, simple_func.tendsto_approx_on hf (set.mem_univ _) (by simp)⟩, },
end

/-- In a space with second countable topology, strongly measurable and measurable are equivalent. -/
lemma _root_.strongly_measurable_iff_measurable
  [topological_space β] [metrizable_space β] [borel_space β] [second_countable_topology β] :
  strongly_measurable f ↔ measurable f :=
⟨λ h, h.measurable, λ h, measurable.strongly_measurable h⟩

lemma _root_.strongly_measurable_id [topological_space α] [pseudo_metrizable_space α]
  [opens_measurable_space α] [second_countable_topology α] :
  strongly_measurable (id : α → α) :=
measurable_id.strongly_measurable

end second_countable_strongly_measurable

/-- A function is strongly measurable if and only if it is measurable and has separable
range. -/
theorem _root_.strongly_measurable_iff_measurable_separable {m : measurable_space α}
  [topological_space β] [pseudo_metrizable_space β] [measurable_space β] [borel_space β] :
  strongly_measurable f ↔ (measurable f ∧ is_separable (range f)) :=
begin
  refine ⟨λ H, ⟨H.measurable, H.is_separable_range⟩, _⟩,
  rintros ⟨H, H'⟩,
  letI := pseudo_metrizable_space_pseudo_metric β,
  let g := cod_restrict f (closure (range f)) (λ x, subset_closure (mem_range_self x)),
  have fg : f = (coe : closure (range f) → β) ∘ g, by { ext x, refl },
  have T : measurable_embedding (coe : closure (range f) → β),
  { apply closed_embedding.measurable_embedding,
    exact closed_embedding_subtype_coe is_closed_closure },
  have g_meas : measurable g,
  { rw fg at H, exact T.measurable_comp_iff.1 H },
  haveI : second_countable_topology (closure (range f)),
  { suffices : separable_space (closure (range f)),
      by exactI uniform_space.second_countable_of_separable _,
    exact (is_separable.closure H').separable_space },
  have g_smeas : strongly_measurable g := measurable.strongly_measurable g_meas,
  rw fg,
  exact continuous_subtype_coe.comp_strongly_measurable g_smeas,
end

/-- A continuous function is strongly measurable when either the source space or the target space
is second-countable. -/
lemma _root_.continuous.strongly_measurable [measurable_space α]
  [topological_space α] [opens_measurable_space α]
  {β : Type*} [topological_space β] [pseudo_metrizable_space β]
  [h : second_countable_topology_either α β]
  {f : α → β} (hf : continuous f) :
  strongly_measurable f :=
begin
  borelize β,
  casesI h.out,
  { rw strongly_measurable_iff_measurable_separable,
    refine ⟨hf.measurable, _⟩,
    rw ← image_univ,
    exact (is_separable_of_separable_space univ).image hf },
  { exact hf.measurable.strongly_measurable }
end

/-- If `g` is a topological embedding, then `f` is strongly measurable iff `g ∘ f` is. -/
lemma _root_.embedding.comp_strongly_measurable_iff {m : measurable_space α}
  [topological_space β] [pseudo_metrizable_space β] [topological_space γ]
  [pseudo_metrizable_space γ]
  {g : β → γ} {f : α → β} (hg : embedding g) :
  strongly_measurable (λ x, g (f x)) ↔ strongly_measurable f :=
begin
  letI := pseudo_metrizable_space_pseudo_metric γ,
  borelize [β, γ],
  refine ⟨λ H, strongly_measurable_iff_measurable_separable.2 ⟨_, _⟩,
    λ H, hg.continuous.comp_strongly_measurable H⟩,
  { let G : β → range g := cod_restrict g (range g) mem_range_self,
    have hG : closed_embedding G :=
    { closed_range :=
      begin
        convert is_closed_univ,
        apply eq_univ_of_forall,
        rintros ⟨-, ⟨x, rfl⟩⟩,
        exact mem_range_self x
      end,
      .. hg.cod_restrict _ _ },
    have : measurable (G ∘ f) := measurable.subtype_mk H.measurable,
    exact hG.measurable_embedding.measurable_comp_iff.1 this },
  { have : is_separable (g ⁻¹' (range (g ∘ f))) := hg.is_separable_preimage H.is_separable_range,
    convert this,
    ext x,
    simp [hg.inj.eq_iff] }
end

/-- A sequential limit of strongly measurable functions is strongly measurable. -/
lemma _root_.strongly_measurable_of_tendsto {ι : Type*} {m : measurable_space α}
  [topological_space β] [pseudo_metrizable_space β] (u : filter ι) [ne_bot u]
  [is_countably_generated u] {f : ι → α → β} {g : α → β} (hf : ∀ i, strongly_measurable (f i))
  (lim : tendsto f u (𝓝 g)) :
  strongly_measurable g :=
begin
  borelize β,
  refine strongly_measurable_iff_measurable_separable.2 ⟨_, _⟩,
  { exact measurable_of_tendsto_metrizable' u (λ i, (hf i).measurable) lim },
  { rcases u.exists_seq_tendsto with ⟨v, hv⟩,
    have : is_separable (closure (⋃ i, range (f (v i)))) :=
      (is_separable_Union (λ i, (hf (v i)).is_separable_range)).closure,
    apply this.mono,
    rintros _ ⟨x, rfl⟩,
    rw [tendsto_pi_nhds] at lim,
    apply mem_closure_of_tendsto ((lim x).comp hv),
    apply eventually_of_forall (λ n, _),
    apply mem_Union_of_mem n,
    exact mem_range_self _ }
end

protected lemma piecewise {m : measurable_space α} [topological_space β]
  {s : set α} {_ : decidable_pred (∈ s)} (hs : measurable_set s)
  (hf : strongly_measurable f) (hg : strongly_measurable g) :
  strongly_measurable (set.piecewise s f g) :=
begin
  refine ⟨λ n, simple_func.piecewise s hs (hf.approx n) (hg.approx n), λ x, _⟩,
  by_cases hx : x ∈ s,
  { simpa [hx] using hf.tendsto_approx x },
  { simpa [hx] using hg.tendsto_approx x },
end

/-- this is slightly different from `strongly_measurable.piecewise`. It can be used to show
`strongly_measurable (ite (x=0) 0 1)` by
`exact strongly_measurable.ite (measurable_set_singleton 0) strongly_measurable_const
strongly_measurable_const`, but replacing `strongly_measurable.ite` by
`strongly_measurable.piecewise` in that example proof does not work. -/
protected lemma ite {m : measurable_space α} [topological_space β]
  {p : α → Prop} {_ : decidable_pred p}
  (hp : measurable_set {a : α | p a}) (hf : strongly_measurable f) (hg : strongly_measurable g) :
  strongly_measurable (λ x, ite (p x) (f x) (g x)) :=
strongly_measurable.piecewise hp hf hg

lemma _root_.strongly_measurable_of_strongly_measurable_union_cover
  {m : measurable_space α} [topological_space β]
  {f : α → β} (s t : set α) (hs : measurable_set s) (ht : measurable_set t) (h : univ ⊆ s ∪ t)
  (hc : strongly_measurable (λ a : s, f a)) (hd : strongly_measurable (λ a : t, f a)) :
  strongly_measurable f :=
begin
  classical,
  let f : ℕ → α →ₛ β := λ n,
  { to_fun := λ x, if hx : x ∈ s then hc.approx n ⟨x, hx⟩
                   else hd.approx n ⟨x, by simpa [hx] using h (mem_univ x)⟩,
    measurable_set_fiber' :=
    begin
      assume x,
      convert (hs.subtype_image
        ((hc.approx n).measurable_set_fiber x)).union
        ((ht.subtype_image
        ((hd.approx n).measurable_set_fiber x)).diff hs),
      ext1 y,
      simp only [mem_union, mem_preimage, mem_singleton_iff, mem_image, set_coe.exists,
        subtype.coe_mk, exists_and_distrib_right, exists_eq_right, mem_diff],
      by_cases hy : y ∈ s,
      { rw dif_pos hy,
        simp only [hy, exists_true_left, not_true, and_false, or_false]},
      { rw dif_neg hy,
        have A : y ∈ t, by simpa [hy] using h (mem_univ y),
        simp only [A, hy, false_or, is_empty.exists_iff, not_false_iff, and_true,
          exists_true_left] }
    end,
    finite_range' :=
    begin
      apply ((hc.approx n).finite_range.union (hd.approx n).finite_range).subset,
      rintros - ⟨y, rfl⟩,
      dsimp,
      by_cases hy : y ∈ s,
      { left,
        rw dif_pos hy,
        exact mem_range_self _ },
      { right,
        rw dif_neg hy,
        exact mem_range_self _ }
    end },
  refine ⟨f, λ y, _⟩,
  by_cases hy : y ∈ s,
  { convert hc.tendsto_approx ⟨y, hy⟩ using 1,
    ext1 n,
    simp only [dif_pos hy, simple_func.apply_mk] },
  { have A : y ∈ t, by simpa [hy] using h (mem_univ y),
    convert hd.tendsto_approx ⟨y, A⟩ using 1,
    ext1 n,
    simp only [dif_neg hy, simple_func.apply_mk] }
end

lemma _root_.strongly_measurable_of_restrict_of_restrict_compl
  {m : measurable_space α} [topological_space β] {f : α → β} {s : set α} (hs : measurable_set s)
  (h₁ : strongly_measurable (s.restrict f)) (h₂ : strongly_measurable (sᶜ.restrict f)) :
  strongly_measurable f :=
strongly_measurable_of_strongly_measurable_union_cover s sᶜ hs hs.compl
  (union_compl_self s).ge h₁ h₂

protected lemma indicator {m : measurable_space α} [topological_space β] [has_zero β]
  (hf : strongly_measurable f) {s : set α} (hs : measurable_set s) :
  strongly_measurable (s.indicator f) :=
hf.piecewise hs strongly_measurable_const

protected lemma dist {m : measurable_space α} {β : Type*} [pseudo_metric_space β] {f g : α → β}
  (hf : strongly_measurable f) (hg : strongly_measurable g) :
  strongly_measurable (λ x, dist (f x) (g x)) :=
continuous_dist.comp_strongly_measurable (hf.prod_mk hg)

protected lemma norm {m : measurable_space α} {β : Type*} [seminormed_add_comm_group β]
  {f : α → β} (hf : strongly_measurable f) :
  strongly_measurable (λ x, ‖f x‖) :=
continuous_norm.comp_strongly_measurable hf

protected lemma nnnorm {m : measurable_space α} {β : Type*} [seminormed_add_comm_group β]
  {f : α → β} (hf : strongly_measurable f) :
  strongly_measurable (λ x, ‖f x‖₊) :=
continuous_nnnorm.comp_strongly_measurable hf

protected lemma ennnorm {m : measurable_space α} {β : Type*} [seminormed_add_comm_group β]
  {f : α → β} (hf : strongly_measurable f) :
  measurable (λ a, (‖f a‖₊ : ℝ≥0∞)) :=
(ennreal.continuous_coe.comp_strongly_measurable hf.nnnorm).measurable

protected lemma real_to_nnreal {m : measurable_space α} {f : α → ℝ}
  (hf : strongly_measurable f) :
  strongly_measurable (λ x, (f x).to_nnreal) :=
continuous_real_to_nnreal.comp_strongly_measurable hf

lemma _root_.measurable_embedding.strongly_measurable_extend {f : α → β} {g : α → γ} {g' : γ → β}
  {mα : measurable_space α} {mγ : measurable_space γ} [topological_space β]
  (hg : measurable_embedding g)
  (hf : strongly_measurable f) (hg' : strongly_measurable g') :
  strongly_measurable (function.extend g f g') :=
begin
  refine ⟨λ n, simple_func.extend (hf.approx n) g hg (hg'.approx n), _⟩,
  assume x,
  by_cases hx : ∃ y, g y = x,
  { rcases hx with ⟨y, rfl⟩,
    simpa only [simple_func.extend_apply, hg.injective,
      injective.extend_apply] using hf.tendsto_approx y },
  { simpa only [hx, simple_func.extend_apply', not_false_iff, extend_apply']
      using hg'.tendsto_approx x }
end

lemma _root_.measurable_embedding.exists_strongly_measurable_extend
  {f : α → β} {g : α → γ}
  {mα : measurable_space α} {mγ : measurable_space γ} [topological_space β]
  (hg : measurable_embedding g) (hf : strongly_measurable f) (hne : γ → nonempty β) :
  ∃ f' : γ → β, strongly_measurable f' ∧ f' ∘ g = f :=
⟨function.extend g f (λ x, classical.choice (hne x)),
  hg.strongly_measurable_extend hf (strongly_measurable_const' $ λ _ _, rfl),
  funext $ λ x, hg.injective.extend_apply _ _ _⟩

lemma measurable_set_eq_fun {m : measurable_space α} {E} [topological_space E] [metrizable_space E]
  {f g : α → E} (hf : strongly_measurable f) (hg : strongly_measurable g) :
  measurable_set {x | f x = g x} :=
begin
  borelize E × E,
  exact (hf.prod_mk hg).measurable is_closed_diagonal.measurable_set
end

lemma measurable_set_lt {m : measurable_space α} [topological_space β]
  [linear_order β] [order_closed_topology β] [pseudo_metrizable_space β]
  {f g : α → β} (hf : strongly_measurable f) (hg : strongly_measurable g) :
  measurable_set {a | f a < g a} :=
begin
  borelize β × β,
  exact (hf.prod_mk hg).measurable is_open_lt_prod.measurable_set
end

lemma measurable_set_le {m : measurable_space α} [topological_space β]
  [preorder β] [order_closed_topology β] [pseudo_metrizable_space β]
  {f g : α → β} (hf : strongly_measurable f) (hg : strongly_measurable g) :
  measurable_set {a | f a ≤ g a} :=
begin
  borelize β × β,
  exact (hf.prod_mk hg).measurable is_closed_le_prod.measurable_set
end

lemma strongly_measurable_in_set {m : measurable_space α} [topological_space β] [has_zero β]
  {s : set α} {f : α → β}
  (hs : measurable_set s) (hf : strongly_measurable f) (hf_zero : ∀ x ∉ s, f x = 0) :
  ∃ fs : ℕ → α →ₛ β, (∀ x, tendsto (λ n, fs n x) at_top (𝓝 (f x))) ∧ (∀ (x ∉ s) n, fs n x = 0) :=
begin
  let g_seq_s : ℕ → @simple_func α m β := λ n, (hf.approx n).restrict s,
  have hg_eq : ∀ x ∈ s, ∀ n, g_seq_s n x = hf.approx n x,
  { intros x hx n,
    rw [simple_func.coe_restrict _ hs, set.indicator_of_mem hx], },
  have hg_zero : ∀ x ∉ s, ∀ n, g_seq_s n x = 0,
  { intros x hx n,
    rw [simple_func.coe_restrict _ hs, set.indicator_of_not_mem hx], },
  refine ⟨g_seq_s, λ x, _, hg_zero⟩,
  by_cases hx : x ∈ s,
  { simp_rw hg_eq x hx,
    exact hf.tendsto_approx x, },
  { simp_rw [hg_zero x hx, hf_zero x hx],
    exact tendsto_const_nhds, },
end

/-- If the restriction to a set `s` of a σ-algebra `m` is included in the restriction to `s` of
another σ-algebra `m₂` (hypothesis `hs`), the set `s` is `m` measurable and a function `f` supported
on `s` is `m`-strongly-measurable, then `f` is also `m₂`-strongly-measurable. -/
lemma strongly_measurable_of_measurable_space_le_on {α E} {m m₂ : measurable_space α}
  [topological_space E] [has_zero E] {s : set α} {f : α → E}
  (hs_m : measurable_set[m] s) (hs : ∀ t, measurable_set[m] (s ∩ t) → measurable_set[m₂] (s ∩ t))
  (hf : strongly_measurable[m] f) (hf_zero : ∀ x ∉ s, f x = 0) :
  strongly_measurable[m₂] f :=
begin
  have hs_m₂ : measurable_set[m₂] s,
  { rw ← set.inter_univ s,
    refine hs set.univ _,
    rwa [set.inter_univ], },
  obtain ⟨g_seq_s, hg_seq_tendsto, hg_seq_zero⟩ := strongly_measurable_in_set hs_m hf hf_zero,
  let g_seq_s₂ : ℕ → @simple_func α m₂ E := λ n,
  { to_fun := g_seq_s n,
    measurable_set_fiber' := λ x, begin
      rw [← set.inter_univ ((g_seq_s n) ⁻¹' {x}), ← set.union_compl_self s,
        set.inter_union_distrib_left, set.inter_comm ((g_seq_s n) ⁻¹' {x})],
      refine measurable_set.union (hs _ (hs_m.inter _)) _,
      { exact @simple_func.measurable_set_fiber _ _ m _ _, },
      by_cases hx : x = 0,
      { suffices : (g_seq_s n) ⁻¹' {x} ∩ sᶜ = sᶜ, by { rw this, exact hs_m₂.compl, },
        ext1 y,
        rw [hx, set.mem_inter_iff, set.mem_preimage, set.mem_singleton_iff],
        exact ⟨λ h, h.2, λ h, ⟨hg_seq_zero y h n, h⟩⟩, },
      { suffices : (g_seq_s n) ⁻¹' {x} ∩ sᶜ = ∅, by { rw this, exact measurable_set.empty, },
        ext1 y,
        simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_compl_iff,
          mem_empty_iff_false, iff_false, not_and, not_not_mem],
        refine imp_of_not_imp_not _ _ (λ hys, _),
        rw hg_seq_zero y hys n,
        exact ne.symm hx, },
    end,
    finite_range' := @simple_func.finite_range _ _ m (g_seq_s n), },
  have hg_eq : ∀ x n, g_seq_s₂ n x = g_seq_s n x := λ x n, rfl,
  refine ⟨g_seq_s₂, λ x, _⟩,
  simp_rw hg_eq,
  exact hg_seq_tendsto x,
end

/-- If a function `f` is strongly measurable w.r.t. a sub-σ-algebra `m` and the measure is σ-finite
on `m`, then there exists spanning measurable sets with finite measure on which `f` has bounded
norm. In particular, `f` is integrable on each of those sets. -/
lemma exists_spanning_measurable_set_norm_le [seminormed_add_comm_group β]
  {m m0 : measurable_space α} (hm : m ≤ m0) (hf : strongly_measurable[m] f) (μ : measure α)
  [sigma_finite (μ.trim hm)] :
  ∃ s : ℕ → set α, (∀ n, measurable_set[m] (s n) ∧ μ (s n) < ∞ ∧ ∀ x ∈ s n, ‖f x‖ ≤ n)
    ∧ (⋃ i, s i) = set.univ :=
begin
  let sigma_finite_sets := spanning_sets (μ.trim hm),
  let norm_sets := λ (n : ℕ), {x | ‖f x‖ ≤ n},
  have norm_sets_spanning : (⋃ n, norm_sets n) = set.univ,
  { ext1 x, simp only [set.mem_Union, set.mem_set_of_eq, set.mem_univ, iff_true],
    exact ⟨⌈‖f x‖⌉₊, nat.le_ceil (‖f x‖)⟩, },
  let sets := λ n, sigma_finite_sets n ∩ norm_sets n,
  have h_meas : ∀ n, measurable_set[m] (sets n),
  { refine λ n, measurable_set.inter _ _,
    { exact measurable_spanning_sets (μ.trim hm) n, },
    { exact hf.norm.measurable_set_le strongly_measurable_const, }, },
  have h_finite : ∀ n, μ (sets n) < ∞,
  { refine λ n, (measure_mono (set.inter_subset_left _ _)).trans_lt _,
    exact (le_trim hm).trans_lt (measure_spanning_sets_lt_top (μ.trim hm) n), },
  refine ⟨sets, λ n, ⟨h_meas n, h_finite n, _⟩, _⟩,
  { exact λ x hx, hx.2, },
  { have : (⋃ i, sigma_finite_sets i ∩ norm_sets i)
      = (⋃ i, sigma_finite_sets i) ∩ (⋃ i, norm_sets i),
    { refine set.Union_inter_of_monotone (monotone_spanning_sets (μ.trim hm)) (λ i j hij x, _),
      simp only [norm_sets, set.mem_set_of_eq],
      refine λ hif, hif.trans _,
      exact_mod_cast hij, },
    rw [this, norm_sets_spanning, Union_spanning_sets (μ.trim hm), set.inter_univ], },
end

end strongly_measurable

/-! ## Finitely strongly measurable functions -/

lemma fin_strongly_measurable_zero {α β} {m : measurable_space α} {μ : measure α} [has_zero β]
  [topological_space β] :
  fin_strongly_measurable (0 : α → β) μ :=
⟨0, by simp only [pi.zero_apply, simple_func.coe_zero, support_zero', measure_empty,
    with_top.zero_lt_top, forall_const],
  λ n, tendsto_const_nhds⟩

namespace fin_strongly_measurable

variables {m0 : measurable_space α} {μ : measure α} {f g : α → β}

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
protected lemma measurable [has_zero β] [topological_space β] [pseudo_metrizable_space β]
  [measurable_space β] [borel_space β] (hf : fin_strongly_measurable f μ) :
  measurable f :=
hf.strongly_measurable.measurable

section arithmetic
variables [topological_space β]

protected lemma mul [monoid_with_zero β] [has_continuous_mul β]
  (hf : fin_strongly_measurable f μ) (hg : fin_strongly_measurable g μ) :
  fin_strongly_measurable (f * g) μ :=
begin
  refine ⟨λ n, hf.approx n * hg.approx n, _, λ x, (hf.tendsto_approx x).mul (hg.tendsto_approx x)⟩,
  intro n,
  exact (measure_mono (support_mul_subset_left _ _)).trans_lt (hf.fin_support_approx n),
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

protected lemma const_smul {𝕜} [topological_space 𝕜] [add_monoid β] [monoid 𝕜]
  [distrib_mul_action 𝕜 β] [has_continuous_smul 𝕜 β]
  (hf : fin_strongly_measurable f μ) (c : 𝕜) :
  fin_strongly_measurable (c • f) μ :=
begin
  refine ⟨λ n, c • (hf.approx n), λ n, _, λ x, (hf.tendsto_approx x).const_smul c⟩,
  rw simple_func.coe_smul,
  refine (measure_mono (support_smul_subset_right c _)).trans_lt (hf.fin_support_approx n),
end

end arithmetic

section order
variables [topological_space β] [has_zero β]

protected lemma sup [semilattice_sup β] [has_continuous_sup β]
  (hf : fin_strongly_measurable f μ) (hg : fin_strongly_measurable g μ) :
  fin_strongly_measurable (f ⊔ g) μ :=
begin
  refine ⟨λ n, hf.approx n ⊔ hg.approx n, λ n, _,
    λ x, (hf.tendsto_approx x).sup_right_nhds (hg.tendsto_approx x)⟩,
  refine (measure_mono (support_sup _ _)).trans_lt _,
  exact measure_union_lt_top_iff.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩,
end

protected lemma inf [semilattice_inf β] [has_continuous_inf β]
  (hf : fin_strongly_measurable f μ) (hg : fin_strongly_measurable g μ) :
  fin_strongly_measurable (f ⊓ g) μ :=
begin
  refine ⟨λ n, hf.approx n ⊓ hg.approx n, λ n, _,
    λ x, (hf.tendsto_approx x).inf_right_nhds (hg.tendsto_approx x)⟩,
  refine (measure_mono (support_inf _ _)).trans_lt _,
  exact measure_union_lt_top_iff.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩,
end

end order

end fin_strongly_measurable

lemma fin_strongly_measurable_iff_strongly_measurable_and_exists_set_sigma_finite {α β} {f : α → β}
  [topological_space β] [t2_space β] [has_zero β] {m : measurable_space α} {μ : measure α} :
  fin_strongly_measurable f μ ↔ (strongly_measurable f
    ∧ (∃ t, measurable_set t ∧ (∀ x ∈ tᶜ, f x = 0) ∧ sigma_finite (μ.restrict t))) :=
⟨λ hf, ⟨hf.strongly_measurable, hf.exists_set_sigma_finite⟩,
  λ hf, hf.1.fin_strongly_measurable_of_set_sigma_finite hf.2.some_spec.1 hf.2.some_spec.2.1
    hf.2.some_spec.2.2⟩

lemma ae_fin_strongly_measurable_zero {α β} {m : measurable_space α} (μ : measure α) [has_zero β]
  [topological_space β] :
  ae_fin_strongly_measurable (0 : α → β) μ :=
⟨0, fin_strongly_measurable_zero, eventually_eq.rfl⟩


/-! ## Almost everywhere strongly measurable functions -/

lemma ae_strongly_measurable_const {α β} {m : measurable_space α} {μ : measure α}
  [topological_space β] {b : β} :
  ae_strongly_measurable (λ a : α, b) μ :=
strongly_measurable_const.ae_strongly_measurable

@[to_additive] lemma ae_strongly_measurable_one {α β} {m : measurable_space α} {μ : measure α}
  [topological_space β] [has_one β] :
  ae_strongly_measurable (1 : α → β) μ :=
strongly_measurable_one.ae_strongly_measurable

@[simp] lemma subsingleton.ae_strongly_measurable {m : measurable_space α} [topological_space β]
  [subsingleton β] {μ : measure α} (f : α → β) :
  ae_strongly_measurable f μ :=
(subsingleton.strongly_measurable f).ae_strongly_measurable

@[simp] lemma subsingleton.ae_strongly_measurable' {m : measurable_space α} [topological_space β]
  [subsingleton α] {μ : measure α} (f : α → β) :
  ae_strongly_measurable f μ :=
(subsingleton.strongly_measurable' f).ae_strongly_measurable

@[simp] lemma ae_strongly_measurable_zero_measure [measurable_space α] [topological_space β]
  (f : α → β) :
  ae_strongly_measurable f (0 : measure α) :=
begin
  nontriviality α,
  inhabit α,
  exact ⟨λ x, f default, strongly_measurable_const, rfl⟩
end

lemma simple_func.ae_strongly_measurable {m : measurable_space α} {μ : measure α}
  [topological_space β] (f : α →ₛ β) :
  ae_strongly_measurable f μ :=
f.strongly_measurable.ae_strongly_measurable

namespace ae_strongly_measurable

variables {m : measurable_space α} {μ : measure α} [topological_space β] [topological_space γ]
  {f g : α → β}

section mk

/-- A `strongly_measurable` function such that `f =ᵐ[μ] hf.mk f`. See lemmas
`strongly_measurable_mk` and `ae_eq_mk`. -/
protected noncomputable def mk (f : α → β) (hf : ae_strongly_measurable f μ) : α → β := hf.some

lemma strongly_measurable_mk (hf : ae_strongly_measurable f μ) :
  strongly_measurable (hf.mk f) :=
hf.some_spec.1

lemma measurable_mk [pseudo_metrizable_space β] [measurable_space β] [borel_space β]
  (hf : ae_strongly_measurable f μ) :
  measurable (hf.mk f) :=
hf.strongly_measurable_mk.measurable

lemma ae_eq_mk (hf : ae_strongly_measurable f μ) : f =ᵐ[μ] hf.mk f :=
hf.some_spec.2

protected lemma ae_measurable {β} [measurable_space β] [topological_space β]
  [pseudo_metrizable_space β] [borel_space β] {f : α → β} (hf : ae_strongly_measurable f μ) :
  ae_measurable f μ :=
⟨hf.mk f, hf.strongly_measurable_mk.measurable, hf.ae_eq_mk⟩

end mk

lemma congr (hf : ae_strongly_measurable f μ) (h : f =ᵐ[μ] g) : ae_strongly_measurable g μ :=
⟨hf.mk f, hf.strongly_measurable_mk, h.symm.trans hf.ae_eq_mk⟩

lemma _root_.ae_strongly_measurable_congr (h : f =ᵐ[μ] g) :
  ae_strongly_measurable f μ ↔ ae_strongly_measurable g μ :=
⟨λ hf, hf.congr h, λ hg, hg.congr h.symm⟩

lemma mono_measure {ν : measure α} (hf : ae_strongly_measurable f μ) (h : ν ≤ μ) :
  ae_strongly_measurable f ν :=
⟨hf.mk f, hf.strongly_measurable_mk, eventually.filter_mono (ae_mono h) hf.ae_eq_mk⟩

protected lemma mono' {ν : measure α} (h : ae_strongly_measurable f μ) (h' : ν ≪ μ) :
  ae_strongly_measurable f ν :=
⟨h.mk f, h.strongly_measurable_mk, h' h.ae_eq_mk⟩

lemma mono_set {s t} (h : s ⊆ t) (ht : ae_strongly_measurable f (μ.restrict t)) :
  ae_strongly_measurable f (μ.restrict s) :=
ht.mono_measure (restrict_mono h le_rfl)

protected lemma restrict (hfm : ae_strongly_measurable f μ) {s} :
  ae_strongly_measurable f (μ.restrict s) :=
hfm.mono_measure measure.restrict_le_self

lemma ae_mem_imp_eq_mk {s} (h : ae_strongly_measurable f (μ.restrict s)) :
  ∀ᵐ x ∂μ, x ∈ s → f x = h.mk f x :=
ae_imp_of_ae_restrict h.ae_eq_mk

/-- The composition of a continuous function and an ae strongly measurable function is ae strongly
measurable. -/
lemma _root_.continuous.comp_ae_strongly_measurable {g : β → γ} {f : α → β}
  (hg : continuous g) (hf : ae_strongly_measurable f μ) :
  ae_strongly_measurable (λ x, g (f x)) μ :=
⟨_, hg.comp_strongly_measurable hf.strongly_measurable_mk, eventually_eq.fun_comp hf.ae_eq_mk g⟩

/-- A continuous function from `α` to `β` is ae strongly measurable when one of the two spaces is
second countable. -/
lemma _root_.continuous.ae_strongly_measurable [topological_space α] [opens_measurable_space α]
  [pseudo_metrizable_space β] [second_countable_topology_either α β] (hf : continuous f) :
  ae_strongly_measurable f μ :=
hf.strongly_measurable.ae_strongly_measurable

protected lemma prod_mk {f : α → β} {g : α → γ}
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) :
  ae_strongly_measurable (λ x, (f x, g x)) μ :=
⟨λ x, (hf.mk f x, hg.mk g x), hf.strongly_measurable_mk.prod_mk hg.strongly_measurable_mk,
  hf.ae_eq_mk.prod_mk hg.ae_eq_mk⟩

/-- In a space with second countable topology, measurable implies ae strongly measurable. -/
lemma _root_.measurable.ae_strongly_measurable {m : measurable_space α}
  {μ : measure α} [measurable_space β] [pseudo_metrizable_space β]
  [second_countable_topology β] [opens_measurable_space β] (hf : measurable f) :
  ae_strongly_measurable f μ :=
hf.strongly_measurable.ae_strongly_measurable

section arithmetic

@[to_additive]
protected lemma mul [has_mul β] [has_continuous_mul β]
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) :
  ae_strongly_measurable (f * g) μ :=
⟨hf.mk f * hg.mk g, hf.strongly_measurable_mk.mul hg.strongly_measurable_mk,
  hf.ae_eq_mk.mul hg.ae_eq_mk⟩

@[to_additive]
protected lemma mul_const [has_mul β] [has_continuous_mul β]
  (hf : ae_strongly_measurable f μ) (c : β) :
  ae_strongly_measurable (λ x, f x * c) μ :=
hf.mul ae_strongly_measurable_const

@[to_additive]
protected lemma const_mul [has_mul β] [has_continuous_mul β]
  (hf : ae_strongly_measurable f μ) (c : β) :
  ae_strongly_measurable (λ x, c * f x) μ :=
ae_strongly_measurable_const.mul hf

@[to_additive]
protected lemma inv [group β] [topological_group β] (hf : ae_strongly_measurable f μ) :
  ae_strongly_measurable (f⁻¹) μ :=
⟨(hf.mk f)⁻¹, hf.strongly_measurable_mk.inv, hf.ae_eq_mk.inv⟩

@[to_additive]
protected lemma div [group β] [topological_group β]
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) :
  ae_strongly_measurable (f / g) μ :=
⟨hf.mk f / hg.mk g, hf.strongly_measurable_mk.div hg.strongly_measurable_mk,
  hf.ae_eq_mk.div hg.ae_eq_mk⟩

@[to_additive]
protected lemma smul {𝕜} [topological_space 𝕜] [has_smul 𝕜 β] [has_continuous_smul 𝕜 β]
  {f : α → 𝕜} {g : α → β} (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) :
  ae_strongly_measurable (λ x, f x • g x) μ :=
continuous_smul.comp_ae_strongly_measurable (hf.prod_mk hg)

protected lemma const_smul {𝕜} [has_smul 𝕜 β] [has_continuous_const_smul 𝕜 β]
  (hf : ae_strongly_measurable f μ) (c : 𝕜) :
  ae_strongly_measurable (c • f) μ :=
⟨c • hf.mk f, hf.strongly_measurable_mk.const_smul c, hf.ae_eq_mk.const_smul c⟩

protected lemma const_smul' {𝕜} [has_smul 𝕜 β] [has_continuous_const_smul 𝕜 β]
  (hf : ae_strongly_measurable f μ) (c : 𝕜) :
  ae_strongly_measurable (λ x, c • (f x)) μ :=
hf.const_smul c

@[to_additive]
protected lemma smul_const {𝕜} [topological_space 𝕜] [has_smul 𝕜 β] [has_continuous_smul 𝕜 β]
  {f : α → 𝕜} (hf : ae_strongly_measurable f μ) (c : β) :
  ae_strongly_measurable (λ x, f x • c) μ :=
continuous_smul.comp_ae_strongly_measurable (hf.prod_mk ae_strongly_measurable_const)

end arithmetic

section order

protected lemma sup [semilattice_sup β] [has_continuous_sup β]
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) :
  ae_strongly_measurable (f ⊔ g) μ :=
⟨hf.mk f ⊔ hg.mk g, hf.strongly_measurable_mk.sup hg.strongly_measurable_mk,
  hf.ae_eq_mk.sup hg.ae_eq_mk⟩

protected lemma inf [semilattice_inf β] [has_continuous_inf β]
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) :
  ae_strongly_measurable (f ⊓ g) μ :=
⟨hf.mk f ⊓ hg.mk g, hf.strongly_measurable_mk.inf hg.strongly_measurable_mk,
  hf.ae_eq_mk.inf hg.ae_eq_mk⟩

end order

/-!
### Big operators: `∏` and `∑`
-/

section monoid
variables {M : Type*} [monoid M] [topological_space M] [has_continuous_mul M]

@[to_additive]
lemma _root_.list.ae_strongly_measurable_prod' (l : list (α → M))
  (hl : ∀ f ∈ l, ae_strongly_measurable f μ) : ae_strongly_measurable l.prod μ :=
begin
  induction l with f l ihl, { exact ae_strongly_measurable_one },
  rw [list.forall_mem_cons] at hl,
  rw [list.prod_cons],
  exact hl.1.mul (ihl hl.2)
end

@[to_additive]
lemma _root_.list.ae_strongly_measurable_prod
  (l : list (α → M)) (hl : ∀ f ∈ l, ae_strongly_measurable f μ) :
  ae_strongly_measurable (λ x, (l.map (λ f : α → M, f x)).prod) μ :=
by simpa only [← pi.list_prod_apply] using l.ae_strongly_measurable_prod' hl

end monoid

section comm_monoid
variables {M : Type*} [comm_monoid M] [topological_space M] [has_continuous_mul M]

@[to_additive]
lemma _root_.multiset.ae_strongly_measurable_prod' (l : multiset (α → M))
  (hl : ∀ f ∈ l, ae_strongly_measurable f μ) : ae_strongly_measurable l.prod μ :=
by { rcases l with ⟨l⟩, simpa using l.ae_strongly_measurable_prod' (by simpa using hl) }

@[to_additive]
lemma _root_.multiset.ae_strongly_measurable_prod (s : multiset (α → M))
  (hs : ∀ f ∈ s, ae_strongly_measurable f μ) :
  ae_strongly_measurable (λ x, (s.map (λ f : α → M, f x)).prod) μ :=
by simpa only [← pi.multiset_prod_apply] using s.ae_strongly_measurable_prod' hs

@[to_additive]
lemma _root_.finset.ae_strongly_measurable_prod' {ι : Type*}  {f : ι → α → M}
  (s : finset ι) (hf : ∀i ∈ s, ae_strongly_measurable (f i) μ) :
  ae_strongly_measurable (∏ i in s, f i) μ :=
multiset.ae_strongly_measurable_prod' _ $
  λ g hg, let ⟨i, hi, hg⟩ := multiset.mem_map.1 hg in (hg ▸ hf _ hi)

@[to_additive]
lemma _root_.finset.ae_strongly_measurable_prod {ι : Type*}  {f : ι → α → M}
  (s : finset ι) (hf : ∀i ∈ s, ae_strongly_measurable (f i) μ) :
  ae_strongly_measurable (λ a, ∏ i in s, f i a) μ :=
by simpa only [← finset.prod_apply] using s.ae_strongly_measurable_prod' hf

end comm_monoid

section second_countable_ae_strongly_measurable

variables [measurable_space β]

/-- In a space with second countable topology, measurable implies strongly measurable. -/
lemma _root_.ae_measurable.ae_strongly_measurable [pseudo_metrizable_space β]
  [opens_measurable_space β] [second_countable_topology β] (hf : ae_measurable f μ) :
  ae_strongly_measurable f μ :=
⟨hf.mk f, hf.measurable_mk.strongly_measurable, hf.ae_eq_mk⟩

lemma _root_.ae_strongly_measurable_id {α : Type*} [topological_space α] [pseudo_metrizable_space α]
  {m : measurable_space α} [opens_measurable_space α] [second_countable_topology α]
  {μ : measure α} :
  ae_strongly_measurable (id : α → α) μ :=
ae_measurable_id.ae_strongly_measurable

/-- In a space with second countable topology, strongly measurable and measurable are equivalent. -/
lemma _root_.ae_strongly_measurable_iff_ae_measurable [pseudo_metrizable_space β] [borel_space β]
  [second_countable_topology β] :
  ae_strongly_measurable f μ ↔ ae_measurable f μ :=
⟨λ h, h.ae_measurable, λ h, h.ae_strongly_measurable⟩

end second_countable_ae_strongly_measurable

protected lemma dist {β : Type*} [pseudo_metric_space β] {f g : α → β}
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) :
  ae_strongly_measurable (λ x, dist (f x) (g x)) μ :=
continuous_dist.comp_ae_strongly_measurable (hf.prod_mk hg)

protected lemma norm {β : Type*} [seminormed_add_comm_group β] {f : α → β}
  (hf : ae_strongly_measurable f μ) :
  ae_strongly_measurable (λ x, ‖f x‖) μ :=
continuous_norm.comp_ae_strongly_measurable hf

protected lemma nnnorm {β : Type*} [seminormed_add_comm_group β] {f : α → β}
  (hf : ae_strongly_measurable f μ) :
  ae_strongly_measurable (λ x, ‖f x‖₊) μ :=
continuous_nnnorm.comp_ae_strongly_measurable hf

protected lemma ennnorm {β : Type*} [seminormed_add_comm_group β] {f : α → β}
  (hf : ae_strongly_measurable f μ) :
  ae_measurable (λ a, (‖f a‖₊ : ℝ≥0∞)) μ :=
(ennreal.continuous_coe.comp_ae_strongly_measurable hf.nnnorm).ae_measurable

protected lemma edist {β : Type*} [seminormed_add_comm_group β] {f g : α → β}
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) :
  ae_measurable (λ a, edist (f a) (g a)) μ :=
(continuous_edist.comp_ae_strongly_measurable (hf.prod_mk hg)).ae_measurable

protected lemma real_to_nnreal {f : α → ℝ}
  (hf : ae_strongly_measurable f μ) :
  ae_strongly_measurable (λ x, (f x).to_nnreal) μ :=
continuous_real_to_nnreal.comp_ae_strongly_measurable hf

lemma _root_.ae_strongly_measurable_indicator_iff [has_zero β] {s : set α} (hs : measurable_set s) :
  ae_strongly_measurable (indicator s f) μ ↔ ae_strongly_measurable f (μ.restrict s)  :=
begin
  split,
  { intro h,
    exact (h.mono_measure measure.restrict_le_self).congr (indicator_ae_eq_restrict hs) },
  { intro h,
    refine ⟨indicator s (h.mk f), h.strongly_measurable_mk.indicator hs, _⟩,
    have A : s.indicator f =ᵐ[μ.restrict s] s.indicator (h.mk f) :=
      (indicator_ae_eq_restrict hs).trans (h.ae_eq_mk.trans $ (indicator_ae_eq_restrict hs).symm),
    have B : s.indicator f =ᵐ[μ.restrict sᶜ] s.indicator (h.mk f) :=
      (indicator_ae_eq_restrict_compl hs).trans (indicator_ae_eq_restrict_compl hs).symm,
    exact ae_of_ae_restrict_of_ae_restrict_compl _ A B },
end

protected lemma indicator [has_zero β]
  (hfm : ae_strongly_measurable f μ) {s : set α} (hs : measurable_set s) :
  ae_strongly_measurable (s.indicator f) μ :=
(ae_strongly_measurable_indicator_iff hs).mpr hfm.restrict

lemma null_measurable_set_eq_fun {E} [topological_space E] [metrizable_space E]
  {f g : α → E} (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) :
  null_measurable_set {x | f x = g x} μ :=
begin
  apply (hf.strongly_measurable_mk.measurable_set_eq_fun hg.strongly_measurable_mk)
    .null_measurable_set.congr,
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx,
  change (hf.mk f x = hg.mk g x) = (f x = g x),
  simp only [hfx, hgx]
end

lemma null_measurable_set_lt
  [linear_order β] [order_closed_topology β] [pseudo_metrizable_space β]
  {f g : α → β} (hf : ae_strongly_measurable f μ)
  (hg : ae_strongly_measurable g μ) :
  null_measurable_set {a | f a < g a} μ :=
begin
  apply (hf.strongly_measurable_mk.measurable_set_lt hg.strongly_measurable_mk)
    .null_measurable_set.congr,
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx,
  change (hf.mk f x < hg.mk g x) = (f x < g x),
  simp only [hfx, hgx]
end

lemma null_measurable_set_le [preorder β] [order_closed_topology β] [pseudo_metrizable_space β]
  {f g : α → β} (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) :
  null_measurable_set {a | f a ≤ g a} μ :=
begin
  apply (hf.strongly_measurable_mk.measurable_set_le hg.strongly_measurable_mk)
    .null_measurable_set.congr,
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx,
  change (hf.mk f x ≤ hg.mk g x) = (f x ≤ g x),
  simp only [hfx, hgx]
end

lemma _root_.ae_strongly_measurable_of_ae_strongly_measurable_trim {α} {m m0 : measurable_space α}
  {μ : measure α} (hm : m ≤ m0) {f : α → β} (hf : ae_strongly_measurable f (μ.trim hm)) :
  ae_strongly_measurable f μ :=
⟨hf.mk f, strongly_measurable.mono hf.strongly_measurable_mk hm, ae_eq_of_ae_eq_trim hf.ae_eq_mk⟩

lemma comp_ae_measurable {γ : Type*} {mγ : measurable_space γ} {mα : measurable_space α} {f : γ → α}
  {μ : measure γ} (hg : ae_strongly_measurable g (measure.map f μ)) (hf : ae_measurable f μ) :
  ae_strongly_measurable (g ∘ f) μ :=
⟨(hg.mk g) ∘ hf.mk f, hg.strongly_measurable_mk.comp_measurable hf.measurable_mk,
  (ae_eq_comp hf hg.ae_eq_mk).trans ((hf.ae_eq_mk).fun_comp (hg.mk g))⟩

lemma comp_measurable {γ : Type*} {mγ : measurable_space γ} {mα : measurable_space α} {f : γ → α}
  {μ : measure γ} (hg : ae_strongly_measurable g (measure.map f μ)) (hf : measurable f) :
  ae_strongly_measurable (g ∘ f) μ :=
hg.comp_ae_measurable hf.ae_measurable

lemma comp_quasi_measure_preserving {γ : Type*} {mγ : measurable_space γ} {mα : measurable_space α}
  {f : γ → α} {μ : measure γ} {ν : measure α} (hg : ae_strongly_measurable g ν)
  (hf : quasi_measure_preserving f μ ν) : ae_strongly_measurable (g ∘ f) μ :=
(hg.mono' hf.absolutely_continuous).comp_measurable hf.measurable

lemma is_separable_ae_range (hf : ae_strongly_measurable f μ) :
  ∃ (t : set β), is_separable t ∧ ∀ᵐ x ∂μ, f x ∈ t :=
begin
  refine ⟨range (hf.mk f), hf.strongly_measurable_mk.is_separable_range, _⟩,
  filter_upwards [hf.ae_eq_mk] with x hx,
  simp [hx]
end

/-- A function is almost everywhere strongly measurable if and only if it is almost everywhere
measurable, and up to a zero measure set its range is contained in a separable set. -/
theorem _root_.ae_strongly_measurable_iff_ae_measurable_separable
  [pseudo_metrizable_space β] [measurable_space β] [borel_space β] :
  ae_strongly_measurable f μ ↔
    (ae_measurable f μ ∧ ∃ (t : set β), is_separable t ∧ ∀ᵐ x ∂μ, f x ∈ t) :=
begin
  refine ⟨λ H, ⟨H.ae_measurable, H.is_separable_ae_range⟩, _⟩,
  rintros ⟨H, ⟨t, t_sep, ht⟩⟩,
  rcases eq_empty_or_nonempty t with rfl|h₀,
  { simp only [mem_empty_iff_false, eventually_false_iff_eq_bot, ae_eq_bot] at ht,
    rw ht,
    exact ae_strongly_measurable_zero_measure f },
  { obtain ⟨g, g_meas, gt, fg⟩ : ∃ (g : α → β), measurable g ∧ range g ⊆ t ∧ f =ᵐ[μ] g :=
      H.exists_ae_eq_range_subset ht h₀,
    refine ⟨g, _, fg⟩,
    exact strongly_measurable_iff_measurable_separable.2 ⟨g_meas, t_sep.mono gt⟩ }
end

lemma _root_.measurable_embedding.ae_strongly_measurable_map_iff
  {γ : Type*} {mγ : measurable_space γ} {mα : measurable_space α}
  {f : γ → α} {μ : measure γ} (hf : measurable_embedding f) {g : α → β} :
  ae_strongly_measurable g (measure.map f μ) ↔ ae_strongly_measurable (g ∘ f) μ :=
begin
  refine ⟨λ H, H.comp_measurable hf.measurable, _⟩,
  rintro ⟨g₁, hgm₁, heq⟩,
  rcases hf.exists_strongly_measurable_extend hgm₁ (λ x, ⟨g x⟩) with ⟨g₂, hgm₂, rfl⟩,
  exact ⟨g₂, hgm₂, hf.ae_map_iff.2 heq⟩
end

lemma _root_.embedding.ae_strongly_measurable_comp_iff
  [pseudo_metrizable_space β] [pseudo_metrizable_space γ]
  {g : β → γ} {f : α → β} (hg : embedding g) :
  ae_strongly_measurable (λ x, g (f x)) μ ↔ ae_strongly_measurable f μ :=
begin
  letI := pseudo_metrizable_space_pseudo_metric γ,
  borelize [β, γ],
  refine ⟨λ H, ae_strongly_measurable_iff_ae_measurable_separable.2 ⟨_, _⟩,
    λ H, hg.continuous.comp_ae_strongly_measurable H⟩,
  { let G : β → range g := cod_restrict g (range g) mem_range_self,
    have hG : closed_embedding G :=
    { closed_range :=
      begin
        convert is_closed_univ,
        apply eq_univ_of_forall,
        rintros ⟨-, ⟨x, rfl⟩⟩,
        exact mem_range_self x
      end,
      .. hg.cod_restrict _ _ },
    have : ae_measurable (G ∘ f) μ := ae_measurable.subtype_mk H.ae_measurable,
    exact hG.measurable_embedding.ae_measurable_comp_iff.1 this },
  { rcases (ae_strongly_measurable_iff_ae_measurable_separable.1 H).2 with ⟨t, ht, h't⟩,
    exact ⟨g⁻¹' t, hg.is_separable_preimage ht, h't⟩ }
end

lemma _root_.measure_theory.measure_preserving.ae_strongly_measurable_comp_iff {β : Type*}
  {f : α → β} {mα : measurable_space α} {μa : measure α}  {mβ : measurable_space β} {μb : measure β}
  (hf : measure_preserving f μa μb) (h₂ : measurable_embedding f) {g : β → γ} :
  ae_strongly_measurable (g ∘ f) μa ↔ ae_strongly_measurable g μb :=
by rw [← hf.map_eq, h₂.ae_strongly_measurable_map_iff]

/-- An almost everywhere sequential limit of almost everywhere strongly measurable functions is
almost everywhere strongly measurable. -/
lemma _root_.ae_strongly_measurable_of_tendsto_ae {ι : Type*}
  [pseudo_metrizable_space β] (u : filter ι) [ne_bot u] [is_countably_generated u]
  {f : ι → α → β} {g : α → β} (hf : ∀ i, ae_strongly_measurable (f i) μ)
  (lim : ∀ᵐ x ∂μ, tendsto (λ n, f n x) u (𝓝 (g x))) :
  ae_strongly_measurable g μ :=
begin
  borelize β,
  refine ae_strongly_measurable_iff_ae_measurable_separable.2 ⟨_, _⟩,
  { exact ae_measurable_of_tendsto_metrizable_ae _ (λ n, (hf n).ae_measurable) lim },
  { rcases u.exists_seq_tendsto with ⟨v, hv⟩,
    have : ∀ (n : ℕ), ∃ (t : set β), is_separable t ∧ f (v n) ⁻¹' t ∈ μ.ae :=
      λ n, (ae_strongly_measurable_iff_ae_measurable_separable.1 (hf (v n))).2,
    choose t t_sep ht using this,
    refine ⟨closure (⋃ i, (t i)), (is_separable_Union (λ i, (t_sep i))).closure, _⟩,
    filter_upwards [ae_all_iff.2 ht, lim] with x hx h'x,
    apply mem_closure_of_tendsto ((h'x).comp hv),
    apply eventually_of_forall (λ n, _),
    apply mem_Union_of_mem n,
    exact hx n }
end

/-- If a sequence of almost everywhere strongly measurable functions converges almost everywhere,
one can select a strongly measurable function as the almost everywhere limit. -/
lemma _root_.exists_strongly_measurable_limit_of_tendsto_ae [pseudo_metrizable_space β]
  {f : ℕ → α → β} (hf : ∀ n, ae_strongly_measurable (f n) μ)
  (h_ae_tendsto : ∀ᵐ x ∂μ, ∃ l : β, tendsto (λ n, f n x) at_top (𝓝 l)) :
  ∃ (f_lim : α → β) (hf_lim_meas : strongly_measurable f_lim),
    ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (𝓝 (f_lim x)) :=
begin
  borelize β,
  obtain ⟨g, g_meas, hg⟩ : ∃ (g : α → β) (g_meas : measurable g),
      ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (𝓝 (g x)) :=
    measurable_limit_of_tendsto_metrizable_ae (λ n, (hf n).ae_measurable) h_ae_tendsto,
  have Hg : ae_strongly_measurable g μ := ae_strongly_measurable_of_tendsto_ae _ hf hg,
  refine ⟨Hg.mk g, Hg.strongly_measurable_mk, _⟩,
  filter_upwards [hg, Hg.ae_eq_mk] with x hx h'x,
  rwa h'x at hx,
end

lemma sum_measure [pseudo_metrizable_space β]
  {m : measurable_space α} {μ : ι → measure α} (h : ∀ i, ae_strongly_measurable f (μ i)) :
  ae_strongly_measurable f (measure.sum μ) :=
begin
  borelize β,
  refine ae_strongly_measurable_iff_ae_measurable_separable.2
    ⟨ae_measurable.sum_measure (λ i, (h i).ae_measurable), _⟩,
  have A : ∀ (i : ι), ∃ (t : set β), is_separable t ∧ f ⁻¹' t ∈ (μ i).ae :=
    λ i, (ae_strongly_measurable_iff_ae_measurable_separable.1 (h i)).2,
  choose t t_sep ht using A,
  refine ⟨(⋃ i, t i), is_separable_Union t_sep, _⟩,
  simp only [measure.ae_sum_eq, mem_Union, eventually_supr],
  assume i,
  filter_upwards [ht i] with x hx,
  exact ⟨i, hx⟩
end

@[simp] lemma _root_.ae_strongly_measurable_sum_measure_iff
  [pseudo_metrizable_space β] {m : measurable_space α} {μ : ι → measure α} :
  ae_strongly_measurable f (sum μ) ↔ ∀ i, ae_strongly_measurable f (μ i) :=
⟨λ h i, h.mono_measure (measure.le_sum _ _), sum_measure⟩

@[simp] lemma _root_.ae_strongly_measurable_add_measure_iff [pseudo_metrizable_space β]
  {ν : measure α} :
  ae_strongly_measurable f (μ + ν) ↔ ae_strongly_measurable f μ ∧ ae_strongly_measurable f ν :=
by { rw [← sum_cond, ae_strongly_measurable_sum_measure_iff, bool.forall_bool, and.comm], refl }

lemma add_measure [pseudo_metrizable_space β] {ν : measure α} {f : α → β}
  (hμ : ae_strongly_measurable f μ) (hν : ae_strongly_measurable f ν) :
  ae_strongly_measurable f (μ + ν) :=
ae_strongly_measurable_add_measure_iff.2 ⟨hμ, hν⟩

protected lemma Union [pseudo_metrizable_space β] {s : ι → set α}
  (h : ∀ i, ae_strongly_measurable f (μ.restrict (s i))) :
  ae_strongly_measurable f (μ.restrict (⋃ i, s i)) :=
(sum_measure h).mono_measure $ restrict_Union_le

@[simp] lemma _root_.ae_strongly_measurable_Union_iff [pseudo_metrizable_space β] {s : ι → set α} :
  ae_strongly_measurable f (μ.restrict (⋃ i, s i)) ↔
    ∀ i, ae_strongly_measurable f (μ.restrict (s i)) :=
⟨λ h i, h.mono_measure $ restrict_mono (subset_Union _ _) le_rfl, ae_strongly_measurable.Union⟩

@[simp] lemma _root_.ae_strongly_measurable_union_iff [pseudo_metrizable_space β] {s t : set α} :
  ae_strongly_measurable f (μ.restrict (s ∪ t)) ↔
    ae_strongly_measurable f (μ.restrict s) ∧ ae_strongly_measurable f (μ.restrict t) :=
by simp only [union_eq_Union, ae_strongly_measurable_Union_iff, bool.forall_bool, cond, and.comm]

lemma ae_strongly_measurable_uIoc_iff [linear_order α] [pseudo_metrizable_space β]
  {f : α → β} {a b : α} :
  ae_strongly_measurable f (μ.restrict $ uIoc a b) ↔
  ae_strongly_measurable f (μ.restrict $ Ioc a b) ∧
  ae_strongly_measurable f (μ.restrict $ Ioc b a) :=
by rw [uIoc_eq_union, ae_strongly_measurable_union_iff]

lemma smul_measure {R : Type*} [monoid R] [distrib_mul_action R ℝ≥0∞]
  [is_scalar_tower R ℝ≥0∞ ℝ≥0∞] (h : ae_strongly_measurable f μ) (c : R) :
  ae_strongly_measurable f (c • μ) :=
⟨h.mk f, h.strongly_measurable_mk, ae_smul_measure h.ae_eq_mk c⟩

section normed_space
variables {𝕜 : Type*} [nontrivially_normed_field 𝕜] [complete_space 𝕜]
variables {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]

lemma _root_.ae_strongly_measurable_smul_const_iff {f : α → 𝕜} {c : E} (hc : c ≠ 0) :
  ae_strongly_measurable (λ x, f x • c) μ ↔ ae_strongly_measurable f μ :=
(closed_embedding_smul_left hc).to_embedding.ae_strongly_measurable_comp_iff

end normed_space

section mul_action

variables {G : Type*} [group G] [mul_action G β]
  [has_continuous_const_smul G β]

lemma _root_.ae_strongly_measurable_const_smul_iff (c : G) :
  ae_strongly_measurable (λ x, c • f x) μ ↔ ae_strongly_measurable f μ :=
⟨λ h, by simpa only [inv_smul_smul] using h.const_smul' c⁻¹, λ h, h.const_smul c⟩

variables {G₀ : Type*} [group_with_zero G₀] [mul_action G₀ β]
  [has_continuous_const_smul G₀ β]

lemma _root_.ae_strongly_measurable_const_smul_iff₀ {c : G₀} (hc : c ≠ 0) :
  ae_strongly_measurable (λ x, c • f x) μ ↔ ae_strongly_measurable f μ :=
begin
  refine ⟨λ h, _, λ h, h.const_smul c⟩,
  convert h.const_smul' c⁻¹,
  simp [smul_smul, inv_mul_cancel hc]
end

end mul_action

section continuous_linear_map_nontrivially_normed_field

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
variables {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
variables {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
variables {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]

lemma _root_.strongly_measurable.apply_continuous_linear_map
  {m : measurable_space α} {φ : α → F →L[𝕜] E} (hφ : strongly_measurable φ) (v : F) :
  strongly_measurable (λ a, φ a v) :=
(continuous_linear_map.apply 𝕜 E v).continuous.comp_strongly_measurable hφ

lemma apply_continuous_linear_map {φ : α → F →L[𝕜] E}
  (hφ : ae_strongly_measurable φ μ) (v : F) :
  ae_strongly_measurable (λ a, φ a v) μ :=
(continuous_linear_map.apply 𝕜 E v).continuous.comp_ae_strongly_measurable hφ

lemma _root_.continuous_linear_map.ae_strongly_measurable_comp₂ (L : E →L[𝕜] F →L[𝕜] G)
  {f : α → E} {g : α → F}
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) :
  ae_strongly_measurable (λ x, L (f x) (g x)) μ :=
L.continuous₂.comp_ae_strongly_measurable $ hf.prod_mk hg

end continuous_linear_map_nontrivially_normed_field

lemma _root_.ae_strongly_measurable_with_density_iff {E : Type*} [normed_add_comm_group E]
  [normed_space ℝ E] {f : α → ℝ≥0} (hf : measurable f) {g : α → E} :
  ae_strongly_measurable g (μ.with_density (λ x, (f x : ℝ≥0∞))) ↔
    ae_strongly_measurable (λ x, (f x : ℝ) • g x) μ :=
begin
  split,
  { rintros ⟨g', g'meas, hg'⟩,
    have A : measurable_set {x : α | f x ≠ 0} := (hf (measurable_set_singleton 0)).compl,
    refine ⟨λ x, (f x : ℝ) • g' x, hf.coe_nnreal_real.strongly_measurable.smul g'meas, _⟩,
    apply @ae_of_ae_restrict_of_ae_restrict_compl _ _ _ {x | f x ≠ 0},
    { rw [eventually_eq, ae_with_density_iff hf.coe_nnreal_ennreal] at hg',
      rw ae_restrict_iff' A,
      filter_upwards [hg'] with a ha h'a,
      have : (f a : ℝ≥0∞) ≠ 0, by simpa only [ne.def, ennreal.coe_eq_zero] using h'a,
      rw ha this },
    { filter_upwards [ae_restrict_mem A.compl] with x hx,
      simp only [not_not, mem_set_of_eq, mem_compl_iff] at hx,
      simp [hx] } },
  { rintros ⟨g', g'meas, hg'⟩,
    refine ⟨λ x, (f x : ℝ)⁻¹ • g' x, hf.coe_nnreal_real.inv.strongly_measurable.smul g'meas, _⟩,
    rw [eventually_eq, ae_with_density_iff hf.coe_nnreal_ennreal],
    filter_upwards [hg'] with x hx h'x,
    rw [← hx, smul_smul, _root_.inv_mul_cancel, one_smul],
    simp only [ne.def, ennreal.coe_eq_zero] at h'x,
    simpa only [nnreal.coe_eq_zero, ne.def] using h'x }
end

end ae_strongly_measurable


/-! ## Almost everywhere finitely strongly measurable functions -/

namespace ae_fin_strongly_measurable

variables {m : measurable_space α} {μ : measure α} [topological_space β]
  {f g : α → β}

section mk
variables [has_zero β]

/-- A `fin_strongly_measurable` function such that `f =ᵐ[μ] hf.mk f`. See lemmas
`fin_strongly_measurable_mk` and `ae_eq_mk`. -/
protected noncomputable def mk (f : α → β) (hf : ae_fin_strongly_measurable f μ) : α → β := hf.some

lemma fin_strongly_measurable_mk (hf : ae_fin_strongly_measurable f μ) :
  fin_strongly_measurable (hf.mk f) μ :=
hf.some_spec.1

lemma ae_eq_mk (hf : ae_fin_strongly_measurable f μ) : f =ᵐ[μ] hf.mk f :=
hf.some_spec.2

protected lemma ae_measurable {β} [has_zero β] [measurable_space β] [topological_space β]
  [pseudo_metrizable_space β] [borel_space β]
  {f : α → β} (hf : ae_fin_strongly_measurable f μ) :
  ae_measurable f μ :=
⟨hf.mk f, hf.fin_strongly_measurable_mk.measurable, hf.ae_eq_mk⟩

end mk

section arithmetic

protected lemma mul [monoid_with_zero β] [has_continuous_mul β]
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

protected lemma const_smul {𝕜} [topological_space 𝕜] [add_monoid β] [monoid 𝕜]
  [distrib_mul_action 𝕜 β] [has_continuous_smul 𝕜 β]
  (hf : ae_fin_strongly_measurable f μ) (c : 𝕜) :
  ae_fin_strongly_measurable (c • f) μ :=
⟨c • hf.mk f, hf.fin_strongly_measurable_mk.const_smul c, hf.ae_eq_mk.const_smul c⟩

end arithmetic

section order
variables [has_zero β]

protected lemma sup [semilattice_sup β] [has_continuous_sup β]
  (hf : ae_fin_strongly_measurable f μ) (hg : ae_fin_strongly_measurable g μ) :
  ae_fin_strongly_measurable (f ⊔ g) μ :=
⟨hf.mk f ⊔ hg.mk g, hf.fin_strongly_measurable_mk.sup hg.fin_strongly_measurable_mk,
  hf.ae_eq_mk.sup hg.ae_eq_mk⟩

protected lemma inf [semilattice_inf β] [has_continuous_inf β]
  (hf : ae_fin_strongly_measurable f μ) (hg : ae_fin_strongly_measurable g μ) :
  ae_fin_strongly_measurable (f ⊓ g) μ :=
⟨hf.mk f ⊓ hg.mk g, hf.fin_strongly_measurable_mk.inf hg.fin_strongly_measurable_mk,
  hf.ae_eq_mk.inf hg.ae_eq_mk⟩

end order

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

variables {G : Type*} {p : ℝ≥0∞} {m m0 : measurable_space α} {μ : measure α}
  [seminormed_add_comm_group G] [measurable_space G] [borel_space G] [second_countable_topology G]
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

end second_countable_topology

lemma measurable_uncurry_of_continuous_of_measurable {α β ι : Type*} [topological_space ι]
  [metrizable_space ι] [measurable_space ι] [second_countable_topology ι] [opens_measurable_space ι]
  {mβ : measurable_space β} [topological_space β] [pseudo_metrizable_space β] [borel_space β]
  {m : measurable_space α} {u : ι → α → β}
  (hu_cont : ∀ x, continuous (λ i, u i x)) (h : ∀ i, measurable (u i)) :
  measurable (function.uncurry u) :=
begin
  obtain ⟨t_sf, ht_sf⟩ : ∃ t : ℕ → simple_func ι ι, ∀ j x,
    tendsto (λ n, u (t n j) x) at_top (𝓝 $ u j x),
  { have h_str_meas : strongly_measurable (id : ι → ι), from strongly_measurable_id,
    refine ⟨h_str_meas.approx, λ j x, _⟩,
    exact ((hu_cont x).tendsto j).comp (h_str_meas.tendsto_approx j), },
  let U := λ (n : ℕ) (p : ι × α), u (t_sf n p.fst) p.snd,
  have h_tendsto : tendsto U at_top (𝓝 (λ p, u p.fst p.snd)),
  { rw tendsto_pi_nhds,
    exact λ p, ht_sf p.fst p.snd, },
  refine measurable_of_tendsto_metrizable (λ n, _) h_tendsto,
  have h_meas : measurable (λ (p : (t_sf n).range × α), u ↑p.fst p.snd),
  { have : (λ (p : ↥((t_sf n).range) × α), u ↑(p.fst) p.snd)
        = (λ (p : α × ((t_sf n).range)), u ↑(p.snd) p.fst) ∘ prod.swap := rfl,
    rw [this, @measurable_swap_iff α ↥((t_sf n).range) β m],
    exact measurable_from_prod_countable (λ j, h j), },
  have : (λ p : ι × α, u (t_sf n p.fst) p.snd)
    = (λ p : ↥(t_sf n).range × α, u p.fst p.snd)
      ∘ (λ p : ι × α, (⟨t_sf n p.fst, simple_func.mem_range_self _ _⟩, p.snd)) := rfl,
  simp_rw [U, this],
  refine h_meas.comp (measurable.prod_mk _ measurable_snd),
  exact ((t_sf n).measurable.comp measurable_fst).subtype_mk,
end

lemma strongly_measurable_uncurry_of_continuous_of_strongly_measurable {α β ι : Type*}
  [topological_space ι] [metrizable_space ι] [measurable_space ι] [second_countable_topology ι]
  [opens_measurable_space ι] [topological_space β] [pseudo_metrizable_space β]
  [measurable_space α] {u : ι → α → β}
  (hu_cont : ∀ x, continuous (λ i, u i x)) (h : ∀ i, strongly_measurable (u i)) :
  strongly_measurable (function.uncurry u) :=
begin
  borelize β,
  obtain ⟨t_sf, ht_sf⟩ : ∃ t : ℕ → simple_func ι ι, ∀ j x,
    tendsto (λ n, u (t n j) x) at_top (𝓝 $ u j x),
  { have h_str_meas : strongly_measurable (id : ι → ι), from strongly_measurable_id,
    refine ⟨h_str_meas.approx, λ j x, _⟩,
    exact ((hu_cont x).tendsto j).comp (h_str_meas.tendsto_approx j), },
  let U := λ (n : ℕ) (p : ι × α), u (t_sf n p.fst) p.snd,
  have h_tendsto : tendsto U at_top (𝓝 (λ p, u p.fst p.snd)),
  { rw tendsto_pi_nhds,
    exact λ p, ht_sf p.fst p.snd, },
  refine strongly_measurable_of_tendsto _ (λ n, _) h_tendsto,
  have h_str_meas : strongly_measurable (λ (p : (t_sf n).range × α), u ↑p.fst p.snd),
  { refine strongly_measurable_iff_measurable_separable.2 ⟨_, _⟩,
    { have : (λ (p : ↥((t_sf n).range) × α), u ↑(p.fst) p.snd)
          = (λ (p : α × ((t_sf n).range)), u ↑(p.snd) p.fst) ∘ prod.swap := rfl,
      rw [this, measurable_swap_iff],
      exact measurable_from_prod_countable (λ j, (h j).measurable), },
    { have : is_separable (⋃ (i : (t_sf n).range), range (u i)) :=
        is_separable_Union (λ i, (h i).is_separable_range),
      apply this.mono,
      rintros _ ⟨⟨i, x⟩, rfl⟩,
      simp only [mem_Union, mem_range],
      exact ⟨i, x, rfl⟩ } },
  have : (λ p : ι × α, u (t_sf n p.fst) p.snd)
    = (λ p : ↥(t_sf n).range × α, u p.fst p.snd)
      ∘ (λ p : ι × α, (⟨t_sf n p.fst, simple_func.mem_range_self _ _⟩, p.snd)) := rfl,
  simp_rw [U, this],
  refine h_str_meas.comp_measurable (measurable.prod_mk _ measurable_snd),
  exact ((t_sf n).measurable.comp measurable_fst).subtype_mk,
end

end measure_theory

-- Guard against import creep
assert_not_exists inner_product_space
