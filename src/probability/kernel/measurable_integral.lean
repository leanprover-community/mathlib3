/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import probability.kernel.basic

/-!
# Measurability of the integral against a kernel

The Lebesgue integral of a measurable function against a kernel is measurable.

## Main statements

* `probability_theory.kernel.measurable_lintegral`: the function `a ↦ ∫⁻ b, f a b ∂(κ a)` is
  measurable, for an s-finite kernel `κ : kernel α β` and a function `f : α → β → ℝ≥0∞` such that
  `function.uncurry f` is measurable.


-/

open measure_theory probability_theory

open_locale measure_theory ennreal nnreal big_operators

namespace probability_theory.kernel

variables {α β ι : Type*} {mα : measurable_space α} {mβ : measurable_space β}

include mα mβ

/-- This is an auxiliary lemma for `measurable_prod_mk_mem`. -/
lemma measurable_prod_mk_mem_of_finite (κ : kernel α β) {t : set (α × β)} (ht : measurable_set t)
  (hκs : ∀ a, is_finite_measure (κ a)) :
  measurable (λ a, κ a {b | (a, b) ∈ t}) :=
begin
  -- `t` is a measurable set in the product `α × β`: we use that the product σ-algebra is generated
  -- by boxes to prove the result by induction.
  refine measurable_space.induction_on_inter generate_from_prod.symm is_pi_system_prod _ _ _ _ ht,
  { -- case `t = ∅`
    simp only [set.mem_empty_iff_false, set.set_of_false, measure_empty, measurable_const], },
  { -- case of a box: `t = t₁ ×ˢ t₂` for measurable sets `t₁` and `t₂`
    intros t' ht',
    simp only [set.mem_image2, set.mem_set_of_eq, exists_and_distrib_left] at ht',
    obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := ht',
    simp only [set.prod_mk_mem_set_prod_eq],
    classical,
    have h_eq_ite : (λ a, κ a {b : β | a ∈ t₁ ∧ b ∈ t₂}) = λ a, ite (a ∈ t₁) (κ a t₂) 0,
    { ext1 a,
      split_ifs,
      { simp only [h, true_and], refl, },
      { simp only [h, false_and, set.set_of_false, set.inter_empty, measure_empty], }, },
    rw h_eq_ite,
    exact measurable.ite ht₁ (kernel.measurable_coe κ ht₂) measurable_const },
  { -- we assume that the result is true for `t` and we prove it for `tᶜ`
    intros t' ht' h_meas,
    have h_eq_sdiff : ∀ a, {b : β | (a, b) ∈ t'ᶜ} = set.univ \ {b : β | (a, b) ∈ t'},
    { intro a,
      ext1 b,
      simp only [set.mem_compl_iff, set.mem_set_of_eq, set.mem_diff, set.mem_univ, true_and], },
    simp_rw h_eq_sdiff,
    have : (λ a, κ a (set.univ \ {b : β | (a, b) ∈ t'}))
      = (λ a, (κ a set.univ - κ a {b : β | (a, b) ∈ t'})),
    { ext1 a,
      rw [← set.diff_inter_self_eq_diff, set.inter_univ, measure_diff],
      { exact set.subset_univ _, },
      { exact (@measurable_prod_mk_left α β _ _ a) t' ht', },
      { exact measure_ne_top _ _, }, },
    rw this,
    exact measurable.sub (kernel.measurable_coe κ measurable_set.univ) h_meas, },
  { -- we assume that the result is true for a family of disjoint sets and prove it for their union
    intros f h_disj hf_meas hf,
    have h_Union : (λ a, κ a {b : β | (a, b) ∈ ⋃ i, f i}) = λ a, κ a (⋃ i, {b : β | (a, b) ∈ f i}),
    { ext1 a,
      congr' with b,
      simp only [set.mem_Union, set.supr_eq_Union, set.mem_set_of_eq],
      refl, },
    rw h_Union,
    have h_tsum : (λ a, κ a (⋃ i, {b : β | (a, b) ∈ f i})) = λ a, ∑' i, κ a {b : β | (a, b) ∈ f i},
    { ext1 a,
      rw measure_Union,
      { intros i j hij s hsi hsj b hbs,
        have habi : {(a, b)} ⊆ f i, by { rw set.singleton_subset_iff, exact hsi hbs, },
        have habj : {(a, b)} ⊆ f j, by { rw set.singleton_subset_iff, exact hsj hbs, },
        simpa only [set.bot_eq_empty, set.le_eq_subset, set.singleton_subset_iff,
          set.mem_empty_iff_false] using h_disj hij habi habj, },
      { exact λ i, (@measurable_prod_mk_left α β _ _ a) _ (hf_meas i), }, },
    rw h_tsum,
    exact measurable.ennreal_tsum hf, },
end

lemma measurable_prod_mk_mem (κ : kernel α β) [is_s_finite_kernel κ]
  {t : set (α × β)} (ht : measurable_set t) :
  measurable (λ a, κ a {b | (a, b) ∈ t}) :=
begin
  rw ← kernel_sum_seq κ,
  have : ∀ a, kernel.sum (seq κ) a {b : β | (a, b) ∈ t} = ∑' n, seq κ n a {b : β | (a, b) ∈ t},
    from λ a, kernel.sum_apply' _ _ (measurable_prod_mk_left ht),
  simp_rw this,
  refine measurable.ennreal_tsum (λ n, _),
  exact measurable_prod_mk_mem_of_finite (seq κ n) ht infer_instance,
end

lemma measurable_lintegral_indicator_const (κ : kernel α β) [is_s_finite_kernel κ]
  {t : set (α × β)} (ht : measurable_set t) (c : ℝ≥0∞) :
  measurable (λ a, ∫⁻ b, t.indicator (function.const (α × β) c) (a, b) ∂(κ a)) :=
begin
  simp_rw lintegral_indicator_const_comp measurable_prod_mk_left ht _,
  exact measurable.const_mul (measurable_prod_mk_mem _ ht) c,
end

/-- For an s-finite kernel `κ` and a function `f : α → β → ℝ≥0∞` which is measurable when seen as a
map from `α × β` (hypothesis `measurable (function.uncurry f)`), the integral
`a ↦ ∫⁻ b, f a b ∂(κ a)` is measurable. -/
theorem measurable_lintegral (κ : kernel α β) [is_s_finite_kernel κ]
  {f : α → β → ℝ≥0∞} (hf : measurable (function.uncurry f)) :
  measurable (λ a, ∫⁻ b, f a b ∂(κ a)) :=
begin
  let F : ℕ → simple_func (α × β) ℝ≥0∞ := simple_func.eapprox (function.uncurry f),
  have h : ∀ a, (⨆ n, F n a) = function.uncurry f a,
    from simple_func.supr_eapprox_apply (function.uncurry f) hf,
  simp only [prod.forall, function.uncurry_apply_pair] at h,
  simp_rw ← h,
  have : ∀ a, ∫⁻ b, (⨆ n, F n (a, b)) ∂(κ a) = ⨆ n, ∫⁻ b, F n (a, b) ∂(κ a),
  { intro a,
    rw lintegral_supr,
    { exact λ n, (F n).measurable.comp measurable_prod_mk_left, },
    { exact λ i j hij b, simple_func.monotone_eapprox (function.uncurry f) hij _, }, },
  simp_rw this,
  refine measurable_supr (λ n, simple_func.induction _ _ (F n)),
  { intros c t ht,
    simp only [simple_func.const_zero, simple_func.coe_piecewise, simple_func.coe_const,
      simple_func.coe_zero, set.piecewise_eq_indicator],
    exact measurable_lintegral_indicator_const κ ht c, },
  { intros g₁ g₂ h_disj hm₁ hm₂,
    simp only [simple_func.coe_add, pi.add_apply],
    have h_add : (λ a, ∫⁻ b, g₁ (a, b) + g₂ (a, b) ∂(κ a))
      = (λ a, ∫⁻ b, g₁ (a, b) ∂(κ a)) + (λ a, ∫⁻ b, g₂ (a, b) ∂(κ a)),
    { ext1 a,
      rw [pi.add_apply, lintegral_add_left (g₁.measurable.comp measurable_prod_mk_left)], },
    rw h_add,
    exact measurable.add hm₁ hm₂, },
end

lemma measurable_lintegral' (κ : kernel α β) [is_s_finite_kernel κ]
  {f : β → ℝ≥0∞} (hf : measurable f) :
  measurable (λ a, ∫⁻ b, f b ∂(κ a)) :=
measurable_lintegral κ (hf.comp measurable_snd)

lemma measurable_set_lintegral (κ : kernel α β) [is_s_finite_kernel κ]
  {f : α → β → ℝ≥0∞} (hf : measurable (function.uncurry f)) {s : set β} (hs : measurable_set s) :
  measurable (λ a, ∫⁻ b in s, f a b ∂(κ a)) :=
by { simp_rw ← lintegral_restrict κ hs, exact measurable_lintegral _ hf }

lemma measurable_set_lintegral' (κ : kernel α β) [is_s_finite_kernel κ]
  {f : β → ℝ≥0∞} (hf : measurable f) {s : set β} (hs : measurable_set s) :
  measurable (λ a, ∫⁻ b in s, f b ∂(κ a)) :=
measurable_set_lintegral κ (hf.comp measurable_snd) hs

end probability_theory.kernel
