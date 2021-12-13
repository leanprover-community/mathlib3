/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.special_functions.integrals

/-!
# Non integrable functions

In this file we prove that some functions (e.g., `λ x, x⁻¹`) are not interval integrable.
-/

open_locale measure_theory topological_space interval
open measure_theory topological_space set filter asymptotics

namespace interval_integral

variables {E : Type*} [normed_group E] [normed_space ℝ E] [measurable_space E] [borel_space E]
  [second_countable_topology E] [complete_space E]

lemma not_integrable_has_deriv_at_of_tendsto_norm_at_top_right {f f' : ℝ → E} {a b : ℝ}
  (hlt : a < b) (h_deriv : ∀ᶠ x in 𝓝[Ioi a] a, has_deriv_at f (f' x) x)
  (h_infty : tendsto (λ x, ∥f x∥) (𝓝[Ioi a] a) at_top) :
  ¬interval_integrable f' volume a b :=
begin
  intro h_int,
  obtain ⟨c, ⟨hac, hcb⟩, hc⟩ : ∃ c ∈ Ioo a b, ∀ x ∈ Ioc a c, has_deriv_at f (f' x) x,
    from (mem_nhds_within_Ioi_iff_exists_mem_Ioo_Ioc_subset hlt).1 h_deriv,
  obtain ⟨d, ⟨had, hdc⟩, hdf⟩ : ∃ d, d ∈ Ioo a c ∧ ∥f c∥ + ∫ x in a..b, ∥f' x∥ < ∥f d∥,
    from (eventually.and (Ioo_mem_nhds_within_Ioi (left_mem_Ico.2 hac)) $
      h_infty.eventually (eventually_gt_at_top _)).exists,
  obtain ⟨hc', hd'⟩ : c ∈ [a, b] ∧ d ∈ [a, b],
  { rw interval_of_le hlt.le, exact ⟨⟨hac.le, hcb.le⟩, had.le, (hdc.trans hcb).le⟩ },
  refine hdf.not_le (sub_le_iff_le_add'.1 _),
  calc ∥f d∥ - ∥f c∥ ≤ ∥f d - f c∥ : norm_sub_norm_le _ _
  ... = ∥∫ x in d..c, f' x∥ :
    begin
      rw [integral_symm, norm_neg],
      refine congr_arg _ (integral_eq_sub_of_has_deriv_at (λ x hx, hc _ _) _).symm,
      { rw interval_of_ge hdc.le at hx,
        exact ⟨had.trans_le hx.1, hx.2⟩ },
      { exact h_int.mono (interval_subset_interval hc' hd') le_rfl }
    end
  ... ≤ ∫ x in d..c, ∥f' x∥ : norm_integral_le_integral_norm hdc.le
  ... ≤ ∫ x in a..b, ∥f' x∥ :
    integral_mono_interval had.le hdc.le hcb.le (ae_of_all _ $ λ _, norm_nonneg _) h_int.norm
end

lemma not_integrable_has_deriv_at_of_tendsto_norm_at_top_left {f f' : ℝ → E} {a b : ℝ}
  (hlt : a < b) (h_deriv : ∀ᶠ x in 𝓝[Iio b] b, has_deriv_at f (f' x) x)
  (h_infty : tendsto (λ x, ∥f x∥) (𝓝[Iio b] b) at_top) :
  ¬interval_integrable f' volume a b :=
begin
  intro h_int,
  obtain ⟨c, ⟨hac, hcb⟩, hc⟩ : ∃ c ∈ Ioo a b, ∀ x ∈ Ico c b, has_deriv_at f (f' x) x,
    from (mem_nhds_within_Iio_iff_exists_mem_Ioo_Ico_subset hlt).1 h_deriv,
  obtain ⟨d, ⟨hcd, hdb⟩, hdf⟩ : ∃ d, d ∈ Ioo c b ∧ ∥f c∥ + ∫ x in a..b, ∥f' x∥ < ∥f d∥,
    from (eventually.and (Ioo_mem_nhds_within_Iio (right_mem_Ioc.2 hcb)) $
      h_infty.eventually (eventually_gt_at_top _)).exists,
  obtain ⟨hc', hd'⟩ : c ∈ [a, b] ∧ d ∈ [a, b],
  { rw interval_of_le hlt.le, exact ⟨⟨hac.le, hcb.le⟩, (hac.trans hcd).le, hdb.le⟩ },
  refine hdf.not_le (sub_le_iff_le_add'.1 _),
  calc ∥f d∥ - ∥f c∥ ≤ ∥f d - f c∥ : norm_sub_norm_le _ _
  ... = ∥∫ x in c..d, f' x∥ :
    begin
      refine congr_arg _ (integral_eq_sub_of_has_deriv_at (λ x hx, hc _ _) _).symm,
      { rw interval_of_le hcd.le at hx,
        exact ⟨hx.1, hx.2.trans_lt hdb⟩ },
      { exact h_int.mono (interval_subset_interval hc' hd') le_rfl }
    end
  ... ≤ ∫ x in c..d, ∥f' x∥ : norm_integral_le_integral_norm hcd.le
  ... ≤ ∫ x in a..b, ∥f' x∥ :
    integral_mono_interval hac.le hcd.le hdb.le (ae_of_all _ $ λ _, norm_nonneg _) h_int.norm
end

lemma not_integrable_has_deriv_at_of_tendsto_norm_at_top_punctured {f f' : ℝ → E} {a b c : ℝ}
  (hne : a ≠ b) (hc : c ∈ [a, b]) (h_deriv : ∀ᶠ x in 𝓝[{c}ᶜ] c, has_deriv_at f (f' x) x)
  (h_infty : tendsto (λ x, ∥f x∥) (𝓝[{c}ᶜ] c) at_top) :
  ¬interval_integrable f' volume a b :=
begin
  wlog hlt : a < b := hne.lt_or_lt using [a b, b a] tactic.skip,
  { rw interval_of_le hlt.le at hc,
    rcases hc.1.eq_or_lt with (rfl|hac),
    { have : 𝓝[Ioi a] a ≤ 𝓝[{a}ᶜ] a, from nhds_within_mono _ (λ _, ne_of_gt),
      exact not_integrable_has_deriv_at_of_tendsto_norm_at_top_right hlt
        (h_deriv.filter_mono this) (h_infty.mono_left this) },
    { have : 𝓝[Iio c] c ≤ 𝓝[{c}ᶜ] c, from nhds_within_mono _ (λ _, ne_of_lt),
      exact λ h, not_integrable_has_deriv_at_of_tendsto_norm_at_top_left hac
        (h_deriv.filter_mono this) (h_infty.mono_left this)
        (h.mono_set $ interval_subset_interval_left (Icc_subset_interval hc)) } },
  { exact λ hab hc h, this hab.symm (interval_swap a b ▸ hc) h.symm }
end

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
