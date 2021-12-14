/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.special_functions.integrals

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

open_locale measure_theory topological_space interval
open measure_theory topological_space set filter asymptotics

namespace interval_integral

variables {E : Type*} [normed_group E] [normed_space ℝ E] [measurable_space E] [borel_space E]
  [second_countable_topology E] [complete_space E]

/-- If `f` has derivative `f'` eventually along a nontrivial filter `l : filter ℝ` that is generated
by convex sets, the norm of `f` tends to infinity along `l`, then `f'` is not integrable on any
interval `a..b` such that `[a, b] ∈ l`. -/
lemma not_integrable_has_deriv_at_of_tendsto_norm_at_top_filter {f f' : ℝ → E} {a b : ℝ}
  (l : filter ℝ) [ne_bot l] [tendsto_Ixx_class Icc l l] (hl : [a, b] ∈ l)
  (hd : ∀ᶠ x in l, has_deriv_at f (f' x) x) (hf : tendsto (λ x, ∥f x∥) l at_top) :
  ¬interval_integrable f' volume a b :=
begin
  intro hfi,
  have h : ∀ᶠ x : ℝ × ℝ in l.prod l, ∀ y ∈ [x.1, x.2], has_deriv_at f (f' y) y ∧ y ∈ [a, b],
    from (tendsto_fst.interval tendsto_snd).eventually (hd.and hl).lift'_powerset,
  rcases mem_prod_self_iff.1 h with ⟨s, hsl, hs⟩,
  rcases filter.nonempty_of_mem hsl with ⟨c, hc⟩,
  rcases ((hf.eventually (eventually_gt_at_top (∥f c∥ + |∫ x in a..b, ∥f' x∥|))).and hsl).exists
    with ⟨d, hdf, hds : d ∈ s⟩,
  have hcd : [c, d] ⊆ [a, b],
    from interval_subset_interval ((hs (mk_mem_prod hc hc) _ left_mem_interval).2)
      ((hs (mk_mem_prod hds hds) _ left_mem_interval).2),
  have hcd' : Ι c d ⊆ Ι a b,
    from interval_oc_subset_interval_oc_of_interval_subset_interval hcd,
  refine hdf.not_le (sub_le_iff_le_add'.1 _),
  calc ∥f d∥ - ∥f c∥ ≤ ∥f d - f c∥ : norm_sub_norm_le _ _
  ... = ∥∫ x in d..c, f' x∥ :
    begin
      rw [integral_symm, norm_neg],
      refine congr_arg _ (integral_eq_sub_of_has_deriv_at (λ x hx, _) _).symm,
      exacts [(hs (mk_mem_prod hc hds) _ hx).1, hfi.mono hcd le_rfl]
    end
  ... ≤ |∫ x in d..c, ∥f' x∥| : norm_integral_le_abs_integral_norm
  ... ≤ |∫ x in a..b, ∥f' x∥| : abs_integral_mono_interval (interval_oc_swap c d ▸ hcd')
    (eventually_of_forall $ λ _, norm_nonneg _) hfi.norm
end

/-- If `∥f x∥ → ∞` as `x → c` (more formally, along the filter `𝓝[{c}ᶜ] c`) and `[a, b] ∋ c` is a
nontrivial closed (unordered) interval, then the derivative `f'` of `f` is not interval integrable
on `a..b`. -/
lemma not_integrable_has_deriv_at_of_tendsto_norm_at_top_punctured {f f' : ℝ → E} {a b c : ℝ}
  (hne : a ≠ b) (hc : c ∈ [a, b]) (h_deriv : ∀ᶠ x in 𝓝[{c}ᶜ] c, has_deriv_at f (f' x) x)
  (h_infty : tendsto (λ x, ∥f x∥) (𝓝[{c}ᶜ] c) at_top) :
  ¬interval_integrable f' volume a b :=
begin
  wlog hlt : a < b := hne.lt_or_lt using [a b, b a] tactic.skip,
  { rw interval_of_le hlt.le at hc,
    rcases hc.1.eq_or_lt with (rfl|hac),
    { have : 𝓝[Ioi a] a ≤ 𝓝[{a}ᶜ] a, from nhds_within_mono _ (λ _, ne_of_gt),
      exact not_integrable_has_deriv_at_of_tendsto_norm_at_top_filter _
        (Icc_mem_nhds_within_Ioi ⟨min_le_left _ _, lt_max_iff.2 (or.inr hlt)⟩)
        (h_deriv.filter_mono this) (h_infty.mono_left this) },
    { have : 𝓝[Iio c] c ≤ 𝓝[{c}ᶜ] c, from nhds_within_mono _ (λ _, ne_of_lt),
      exact λ h, not_integrable_has_deriv_at_of_tendsto_norm_at_top_filter _
        (Icc_mem_nhds_within_Iio ⟨min_lt_iff.2 (or.inl hac), le_max_right _ _⟩)
        (h_deriv.filter_mono this) (h_infty.mono_left this)
        (h.mono_set $ interval_subset_interval_left (Icc_subset_interval hc)) } },
  { exact λ hab hc h, this hab.symm (interval_swap a b ▸ hc) h.symm }
end

/-- The function `λ x, x⁻¹` is integrable on `a..b` if and only if `a = b` or `0 ∉ [a, b]`. -/
@[simp] lemma interval_integrable_inv_iff {a b : ℝ} :
  interval_integrable (λ x, x⁻¹) volume a b ↔ a = b ∨ (0 : ℝ) ∉ [a, b] :=
begin
  split,
  { refine λ h, or_iff_not_imp_left.2 (λ hne h₀, _),
    have : ∀ᶠ x in 𝓝[{0}ᶜ] (0 : ℝ), has_deriv_at real.log x⁻¹ x,
      from eventually_nhds_with_of_forall (λ x, real.has_deriv_at_log),
    refine not_integrable_has_deriv_at_of_tendsto_norm_at_top_punctured hne h₀ this _ h,
    exact tendsto_abs_at_bot_at_top.comp real.tendsto_log_nhds_within_zero },
  { rintro (rfl|h₀),
    exacts [interval_integrable.refl,
      interval_integrable_inv (λ x hx, ne_of_mem_of_not_mem hx h₀) continuous_on_id] }
end

end interval_integral
