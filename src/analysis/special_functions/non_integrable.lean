/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.special_functions.integrals
import analysis.calculus.fderiv_measurable

/-!
# Non integrable functions

In this file we prove that the derivative of a function that tends to infinity is not interval
integrable, see `interval_integral.not_integrable_has_deriv_at_of_tendsto_norm_at_top_filter` and
`interval_integral.not_integrable_has_deriv_at_of_tendsto_norm_at_top_punctured`.  Then we apply the
latter lemma to prove that the function `λ x, x⁻¹` is integrable on `a..b` if and only if `a = b` or
`0 ∉ [a, b]`.

## Tags

integrable function
-/

open_locale measure_theory topological_space interval nnreal ennreal
open measure_theory topological_space set filter asymptotics

namespace interval_integral

variables {E F : Type*} [normed_group E] [normed_space ℝ E] [measurable_space E] [borel_space E]
  [second_countable_topology E] [complete_space E] [normed_group F] [normed_space ℝ F]
  [measurable_space F] [borel_space F] [second_countable_topology F] [complete_space F]

/-- If `f` has derivative `f'` eventually along a nontrivial filter `l : filter ℝ` that is generated
by convex sets, the norm of `f` tends to infinity along `l`, then `f'` is not integrable on any
interval `a..b` such that `[a, b] ∈ l`. -/
lemma not_interval_integrable_of_tendsto_norm_at_top_of_deriv_is_O_filter {f : ℝ → E} {g : ℝ → F}
  {a b : ℝ} (l : filter ℝ) [ne_bot l] [tendsto_Ixx_class Icc l l] (hl : [a, b] ∈ l)
  (hd : ∀ᶠ x in l, differentiable_at ℝ f x) (hf : tendsto (λ x, ∥f x∥) l at_top)
  (hg : is_O (deriv f) g l) :
  ¬interval_integrable g volume a b :=
begin
  intro hgi,
  have : ∃ (C : ℝ) (hC₀ : 0 ≤ C) (s ∈ l), ∀ (x ∈ s) (y ∈ s), [x, y] ⊆ [a, b] ∧
    ∀ z ∈ [x, y], differentiable_at ℝ f z ∧ ∥deriv f z∥ ≤ C * ∥g z∥,
  { rcases hg.exists_nonneg with ⟨C, C₀, hC⟩,
    have h : ∀ᶠ x : ℝ × ℝ in l.prod l, ∀ y ∈ [x.1, x.2], (differentiable_at ℝ f y ∧
      ∥deriv f y∥ ≤ C * ∥g y∥) ∧ y ∈ [a, b],
      from (tendsto_fst.interval tendsto_snd).eventually ((hd.and hC.bound).and hl).lift'_powerset,
    rcases mem_prod_self_iff.1 h with ⟨s, hsl, hs⟩,
    simp only [prod_subset_iff, mem_set_of_eq] at hs,
    exact ⟨C, C₀, s, hsl, λ x hx y hy, ⟨λ z hz, (hs x hx y hy z hz).2,
      λ z hz, (hs x hx y hy z hz).1⟩⟩ },
  clear hl hd hg,
  choose C hC₀ s hsl hsub hfd hg,
  replace hgi : interval_integrable (λ x, C * ∥g x∥) volume a b, by convert hgi.norm.smul C,
  obtain ⟨c, hc, d, hd, hlt⟩ : ∃ (c ∈ s) (d ∈ s), ∥f c∥ + ∫ y in Ι a b, C * ∥g y∥ < ∥f d∥,
  { rcases filter.nonempty_of_mem hsl with ⟨c, hc⟩,
    have : ∀ᶠ x in l, ∥f c∥ + ∫ y in Ι a b, C * ∥g y∥ < ∥f x∥,
      from hf.eventually (eventually_gt_at_top _),
    exact ⟨c, hc, (this.and hsl).exists.imp (λ d hd, ⟨hd.2, hd.1⟩)⟩ },
  specialize hsub c hc d hd, specialize hfd c hc d hd,
  replace hg : ∀ x ∈ Ι c d, ∥deriv f x∥ ≤ C * ∥g x∥, from λ z hz, hg c hc d hd z ⟨hz.1.le, hz.2⟩,
  have hg_ae : ∀ᵐ x ∂(volume.restrict (Ι c d)), ∥deriv f x∥ ≤ C * ∥g x∥,
    from (ae_restrict_mem measurable_set_interval_oc).mono hg,
  have hsub' : Ι c d ⊆ Ι a b,
    from interval_oc_subset_interval_oc_of_interval_subset_interval hsub,
  have hfi : interval_integrable (deriv f) volume c d,
    from (hgi.mono_set hsub).mono_fun' (ae_measurable_deriv _ _) hg_ae,
  refine hlt.not_le (sub_le_iff_le_add'.1 _),
  calc ∥f d∥ - ∥f c∥ ≤ ∥f d - f c∥ : norm_sub_norm_le _ _
  ... = ∥∫ x in c..d, deriv f x∥ : congr_arg _ (integral_deriv_eq_sub hfd hfi).symm
  ... = ∥∫ x in Ι c d, deriv f x∥ : norm_integral_eq_norm_integral_Ioc _
  ... ≤ ∫ x in Ι c d, ∥deriv f x∥ : measure_theory.norm_integral_le_integral_norm _
  ... ≤ ∫ x in Ι c d, C * ∥g x∥ :
    set_integral_mono_on hfi.norm.def (hgi.def.mono_set hsub') measurable_set_interval_oc hg
  ... ≤ ∫ x in Ι a b, C * ∥g x∥ :
    set_integral_mono_set hgi.def (ae_of_all _ $ λ x, mul_nonneg hC₀ (norm_nonneg _))
      hsub'.eventually_le
end

/-- If `∥f x∥ → ∞` as `x → c` (more formally, along the filter `𝓝[≠] c`) and `[a, b] ∋ c` is a
nontrivial closed (unordered) interval, then the derivative `f'` of `f` is not interval integrable
on `a..b`. -/
lemma not_integrable_has_deriv_at_of_tendsto_norm_at_top_punctured {f f' : ℝ → E} {a b c : ℝ}
  (hne : a ≠ b) (hc : c ∈ [a, b]) (h_deriv : ∀ᶠ x in 𝓝[≠] c, has_deriv_at f (f' x) x)
  (h_infty : tendsto (λ x, ∥f x∥) (𝓝[≠] c) at_top) :
  ¬interval_integrable f' volume a b :=
begin
  wlog hlt : a < b := hne.lt_or_lt using [a b, b a] tactic.skip,
  { rw interval_of_le hlt.le at hc,
    rcases hc.1.eq_or_lt with (rfl|hac),
    { have : 𝓝[>] a ≤ 𝓝[≠] a, from nhds_within_mono _ (λ _, ne_of_gt),
      exact not_integrable_has_deriv_at_of_tendsto_norm_at_top_filter _
        (Icc_mem_nhds_within_Ioi ⟨min_le_left _ _, lt_max_iff.2 (or.inr hlt)⟩)
        (h_deriv.filter_mono this) (h_infty.mono_left this) },
    { have : 𝓝[<] c ≤ 𝓝[≠] c, from nhds_within_mono _ (λ _, ne_of_lt),
      exact λ h, not_integrable_has_deriv_at_of_tendsto_norm_at_top_filter _
        (Icc_mem_nhds_within_Iio ⟨min_lt_iff.2 (or.inl hac), le_max_right _ _⟩)
        (h_deriv.filter_mono this) (h_infty.mono_left this)
        (h.mono_set $ interval_subset_interval_left (Icc_subset_interval hc)) } },
  { exact λ hab hc h, this hab.symm (interval_swap a b ▸ hc) h.symm }
end

/-- The function `λ x, (x - c)⁻¹` is integrable on `a..b` if and only if `a = b` or `c ∉ [a, b]`. -/
@[simp] lemma interval_integrable_sub_inv_iff {a b c : ℝ} :
  interval_integrable (λ x, (x - c)⁻¹) volume a b ↔ a = b ∨ c ∉ [a, b] :=
begin
  split,
  { refine λ h, or_iff_not_imp_left.2 (λ hne h₀, _),
    have : ∀ᶠ x in 𝓝[≠] c, has_deriv_at (λ x, real.log (x - c)) (x - c)⁻¹ x,
    { refine eventually_nhds_with_of_forall (λ x, _),
      simpa only [sub_ne_zero, one_div] using ((has_deriv_at_id x).sub_const _).log },
    refine not_integrable_has_deriv_at_of_tendsto_norm_at_top_punctured hne h₀ this _ h,
    refine tendsto_abs_at_bot_at_top.comp (real.tendsto_log_nhds_within_zero.comp _),
    rw ← sub_self c,
    exact ((has_deriv_at_id c).sub_const c).tendsto_punctured_nhds one_ne_zero },
  { rintro (rfl|h₀),
    exacts [interval_integrable.refl,
      interval_integrable_inv (λ x hx, sub_ne_zero.2 $ ne_of_mem_of_not_mem hx h₀)
        (continuous_on_id.sub continuous_on_const)] }
end

/-- The function `λ x, x⁻¹` is integrable on `a..b` if and only if `a = b` or `0 ∉ [a, b]`. -/
@[simp] lemma interval_integrable_inv_iff {a b : ℝ} :
  interval_integrable (λ x, x⁻¹) volume a b ↔ a = b ∨ (0 : ℝ) ∉ [a, b] :=
by simp only [← interval_integrable_sub_inv_iff, sub_zero]

lemma not_integrable_of_sub_inv_is_O {a b c : ℝ} (hlt : a ≠ b) (hc : c ∈ [a, b]) {f : ℝ → E}
  (hf : is_O (λ x, (x - c)⁻¹) f (𝓝[≠] c)) : ¬interval_integrable f volume a b :=
begin
  rcases hf.bound with ⟨C, hC⟩,
end

end interval_integral
