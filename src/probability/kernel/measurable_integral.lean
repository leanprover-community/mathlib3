/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import probability.kernel.basic

/-!
# Measurability of the integral against a kernel

The Lebesgue integral of a measurable function against a kernel is measurable. The Bochner integral
is strongly measurable.

## Main statements

* `probability_theory.measurable.lintegral_kernel_prod_right`: the function `a ↦ ∫⁻ b, f a b ∂(κ a)`
  is measurable, for an s-finite kernel `κ : kernel α β` and a function `f : α → β → ℝ≥0∞` such that
  `uncurry f` is measurable.
* `measure_theory.strongly_measurable.integral_kernel_prod_right`: the function
  `a ↦ ∫ b, f a b ∂(κ a)` is measurable, for an s-finite kernel `κ : kernel α β` and a function
  `f : α → β → E` such that `uncurry f` is measurable.

-/

open measure_theory probability_theory function set filter

open_locale measure_theory ennreal topology

variables {α β γ : Type*} {mα : measurable_space α} {mβ : measurable_space β}
  {mγ : measurable_space γ}
  {κ : kernel α β} {η : kernel (α × β) γ} {a : α}

namespace probability_theory
namespace kernel

/-- This is an auxiliary lemma for `measurable_kernel_prod_mk_left`. -/
lemma measurable_kernel_prod_mk_left_of_finite {t : set (α × β)} (ht : measurable_set t)
  (hκs : ∀ a, is_finite_measure (κ a)) :
  measurable (λ a, κ a (prod.mk a ⁻¹' t)) :=
begin
  -- `t` is a measurable set in the product `α × β`: we use that the product σ-algebra is generated
  -- by boxes to prove the result by induction.
  refine measurable_space.induction_on_inter generate_from_prod.symm is_pi_system_prod _ _ _ _ ht,
  { -- case `t = ∅`
    simp only [preimage_empty, measure_empty, measurable_const], },
  { -- case of a box: `t = t₁ ×ˢ t₂` for measurable sets `t₁` and `t₂`
    intros t' ht',
    simp only [set.mem_image2, set.mem_set_of_eq, exists_and_distrib_left] at ht',
    obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := ht',
    classical,
    simp_rw mk_preimage_prod_right_eq_if,
    have h_eq_ite : (λ a, κ a (ite (a ∈ t₁) t₂ ∅)) = λ a, ite (a ∈ t₁) (κ a t₂) 0,
    { ext1 a,
      split_ifs,
      exacts [rfl, measure_empty], },
    rw h_eq_ite,
    exact measurable.ite ht₁ (kernel.measurable_coe κ ht₂) measurable_const },
  { -- we assume that the result is true for `t` and we prove it for `tᶜ`
    intros t' ht' h_meas,
    have h_eq_sdiff : ∀ a, (prod.mk a ⁻¹' t'ᶜ) = set.univ \ (prod.mk a ⁻¹' t'),
    { intro a,
      ext1 b,
      simp only [mem_compl_iff, mem_preimage, mem_diff, mem_univ, true_and], },
    simp_rw h_eq_sdiff,
    have : (λ a, κ a (set.univ \ (prod.mk a ⁻¹' t')))
      = (λ a, (κ a set.univ - κ a (prod.mk a ⁻¹' t'))),
    { ext1 a,
      rw [← set.diff_inter_self_eq_diff, set.inter_univ, measure_diff (set.subset_univ _)],
      { exact (@measurable_prod_mk_left α β _ _ a) t' ht', },
      { exact measure_ne_top _ _, }, },
    rw this,
    exact measurable.sub (kernel.measurable_coe κ measurable_set.univ) h_meas, },
  { -- we assume that the result is true for a family of disjoint sets and prove it for their union
    intros f h_disj hf_meas hf,
    have h_Union : (λ a, κ a (prod.mk a ⁻¹' ⋃ i, f i)) = λ a, κ a (⋃ i, prod.mk a ⁻¹' f i),
    { ext1 a,
      congr' with b,
      simp only [mem_Union, mem_preimage], },
    rw h_Union,
    have h_tsum : (λ a, κ a (⋃ i, prod.mk a ⁻¹' f i)) = λ a, ∑' i, κ a (prod.mk a ⁻¹' f i),
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

lemma measurable_kernel_prod_mk_left [is_s_finite_kernel κ]
  {t : set (α × β)} (ht : measurable_set t) :
  measurable (λ a, κ a (prod.mk a ⁻¹' t)) :=
begin
  rw ← kernel_sum_seq κ,
  have : ∀ a, kernel.sum (seq κ) a (prod.mk a ⁻¹' t) = ∑' n, seq κ n a (prod.mk a ⁻¹' t),
    from λ a, kernel.sum_apply' _ _ (measurable_prod_mk_left ht),
  simp_rw this,
  refine measurable.ennreal_tsum (λ n, _),
  exact measurable_kernel_prod_mk_left_of_finite ht infer_instance,
end

lemma measurable_kernel_prod_mk_left' [is_s_finite_kernel η]
  {s : set (β × γ)} (hs : measurable_set s) (a : α) :
  measurable (λ b, η (a, b) (prod.mk b ⁻¹' s)) :=
begin
  have : ∀ b, prod.mk b ⁻¹' s = {c | ((a, b), c) ∈ {p : (α × β) × γ | (p.1.2, p.2) ∈ s}},
  { intro b, refl, },
  simp_rw this,
  refine (measurable_kernel_prod_mk_left _).comp measurable_prod_mk_left,
  exact (measurable_fst.snd.prod_mk measurable_snd) hs,
end

lemma measurable_kernel_prod_mk_right [is_s_finite_kernel κ]
  {s : set (β × α)} (hs : measurable_set s) :
  measurable (λ y, κ y ((λ x, (x, y)) ⁻¹' s)) :=
measurable_kernel_prod_mk_left (measurable_set_swap_iff.mpr hs)

end kernel

open probability_theory.kernel

section lintegral

variables [is_s_finite_kernel κ] [is_s_finite_kernel η]

/-- Auxiliary lemma for `measurable.lintegral_kernel_prod_right`. -/
lemma kernel.measurable_lintegral_indicator_const {t : set (α × β)} (ht : measurable_set t)
  (c : ℝ≥0∞) :
  measurable (λ a, ∫⁻ b, t.indicator (function.const (α × β) c) (a, b) ∂(κ a)) :=
begin
  simp_rw lintegral_indicator_const_comp measurable_prod_mk_left ht _,
  exact measurable.const_mul (measurable_kernel_prod_mk_left ht) c,
end

/-- For an s-finite kernel `κ` and a function `f : α → β → ℝ≥0∞` which is measurable when seen as a
map from `α × β` (hypothesis `measurable (uncurry f)`), the integral `a ↦ ∫⁻ b, f a b ∂(κ a)` is
measurable. -/
theorem measurable.lintegral_kernel_prod_right {f : α → β → ℝ≥0∞} (hf : measurable (uncurry f)) :
  measurable (λ a, ∫⁻ b, f a b ∂(κ a)) :=
begin
  let F : ℕ → simple_func (α × β) ℝ≥0∞ := simple_func.eapprox (uncurry f),
  have h : ∀ a, (⨆ n, F n a) = uncurry f a,
    from simple_func.supr_eapprox_apply (uncurry f) hf,
  simp only [prod.forall, uncurry_apply_pair] at h,
  simp_rw ← h,
  have : ∀ a, ∫⁻ b, (⨆ n, F n (a, b)) ∂(κ a) = ⨆ n, ∫⁻ b, F n (a, b) ∂(κ a),
  { intro a,
    rw lintegral_supr,
    { exact λ n, (F n).measurable.comp measurable_prod_mk_left, },
    { exact λ i j hij b, simple_func.monotone_eapprox (uncurry f) hij _, }, },
  simp_rw this,
  refine measurable_supr (λ n, simple_func.induction _ _ (F n)),
  { intros c t ht,
    simp only [simple_func.const_zero, simple_func.coe_piecewise, simple_func.coe_const,
      simple_func.coe_zero, set.piecewise_eq_indicator],
    exact kernel.measurable_lintegral_indicator_const ht c, },
  { intros g₁ g₂ h_disj hm₁ hm₂,
    simp only [simple_func.coe_add, pi.add_apply],
    have h_add : (λ a, ∫⁻ b, g₁ (a, b) + g₂ (a, b) ∂(κ a))
      = (λ a, ∫⁻ b, g₁ (a, b) ∂(κ a)) + (λ a, ∫⁻ b, g₂ (a, b) ∂(κ a)),
    { ext1 a,
      rw [pi.add_apply, lintegral_add_left (g₁.measurable.comp measurable_prod_mk_left)], },
    rw h_add,
    exact measurable.add hm₁ hm₂, },
end

lemma measurable.lintegral_kernel_prod_right' {f : (α × β) → ℝ≥0∞} (hf : measurable f) :
  measurable (λ a, ∫⁻ b, f (a, b) ∂(κ a)) :=
begin
  refine measurable.lintegral_kernel_prod_right _,
  have : uncurry (λ (a : α) (b : β), f (a, b)) = f,
  { ext x, rw [← @prod.mk.eta _ _ x, uncurry_apply_pair], },
  rwa this,
end

lemma measurable.lintegral_kernel_prod_right'' {f : β × γ → ℝ≥0∞} (hf : measurable f) :
  measurable (λ x, ∫⁻ y, f (x, y) ∂(η (a, x))) :=
begin
  change measurable ((λ x, ∫⁻ y, (λ u : (α × β) × γ, f (u.1.2, u.2)) (x, y) ∂(η x))
    ∘ (λ x, (a, x))),
  refine (measurable.lintegral_kernel_prod_right' _).comp measurable_prod_mk_left,
  exact hf.comp (measurable_fst.snd.prod_mk measurable_snd),
end

lemma measurable.set_lintegral_kernel_prod_right
  {f : α → β → ℝ≥0∞} (hf : measurable (uncurry f)) {s : set β} (hs : measurable_set s) :
  measurable (λ a, ∫⁻ b in s, f a b ∂(κ a)) :=
by { simp_rw ← lintegral_restrict κ hs, exact hf.lintegral_kernel_prod_right }

lemma measurable.lintegral_kernel_prod_left' {f : β × α → ℝ≥0∞} (hf : measurable f) :
  measurable (λ y, ∫⁻ x, f (x, y) ∂(κ y)) :=
(measurable_swap_iff.mpr hf).lintegral_kernel_prod_right'

lemma measurable.lintegral_kernel_prod_left
  {f : β → α → ℝ≥0∞} (hf : measurable (uncurry f)) :
  measurable (λ y, ∫⁻ x, f x y ∂(κ y)) :=
hf.lintegral_kernel_prod_left'

lemma measurable.set_lintegral_kernel_prod_left
  {f : β → α → ℝ≥0∞} (hf : measurable (uncurry f)) {s : set β} (hs : measurable_set s) :
  measurable (λ b, ∫⁻ a in s, f a b ∂(κ b)) :=
by { simp_rw ← lintegral_restrict κ hs, exact hf.lintegral_kernel_prod_left }

lemma measurable.lintegral_kernel {f : β → ℝ≥0∞} (hf : measurable f) :
  measurable (λ a, ∫⁻ b, f b ∂(κ a)) :=
measurable.lintegral_kernel_prod_right (hf.comp measurable_snd)

lemma measurable.set_lintegral_kernel
  {f : β → ℝ≥0∞} (hf : measurable f) {s : set β} (hs : measurable_set s) :
  measurable (λ a, ∫⁻ b in s, f b ∂(κ a)) :=
measurable.set_lintegral_kernel_prod_right (hf.comp measurable_snd) hs

end lintegral

variables {E : Type*} [normed_add_comm_group E] [is_s_finite_kernel κ] [is_s_finite_kernel η]

lemma measurable_set_kernel_integrable ⦃f : α → β → E⦄ (hf : strongly_measurable (uncurry f)) :
  measurable_set {x | integrable (f x) (κ x)} :=
begin
  simp_rw [integrable, hf.of_uncurry_left.ae_strongly_measurable, true_and],
  exact measurable_set_lt (measurable.lintegral_kernel_prod_right hf.ennnorm) measurable_const
end

end probability_theory

open probability_theory probability_theory.kernel

namespace measure_theory

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]
  [is_s_finite_kernel κ] [is_s_finite_kernel η]

lemma strongly_measurable.integral_kernel_prod_right
  ⦃f : α → β → E⦄ (hf : strongly_measurable (uncurry f)) :
  strongly_measurable (λ x, ∫ y, f x y ∂(κ x)) :=
begin
  classical,
  borelize E,
  haveI : topological_space.separable_space (range (uncurry f) ∪ {0} : set E) :=
    hf.separable_space_range_union_singleton,
  let s : ℕ → simple_func (α × β) E := simple_func.approx_on _ hf.measurable
    (range (uncurry f) ∪ {0}) 0 (by simp),
  let s' : ℕ → α → simple_func β E := λ n x, (s n).comp (prod.mk x) measurable_prod_mk_left,
  let f' : ℕ → α → E := λ n, {x | integrable (f x) (κ x)}.indicator
    (λ x, (s' n x).integral (κ x)),
  have hf' : ∀ n, strongly_measurable (f' n),
  { intro n, refine strongly_measurable.indicator _ (measurable_set_kernel_integrable hf),
    have : ∀ x, (s' n x).range.filter (λ x, x ≠ 0) ⊆ (s n).range,
    { intros x, refine finset.subset.trans (finset.filter_subset _ _) _, intro y,
      simp_rw [simple_func.mem_range], rintro ⟨z, rfl⟩, exact ⟨(x, z), rfl⟩ },
    simp only [simple_func.integral_eq_sum_of_subset (this _)],
    refine finset.strongly_measurable_sum _ (λ x _, _),
    refine (measurable.ennreal_to_real _).strongly_measurable.smul_const _,
    simp only [simple_func.coe_comp, preimage_comp] {single_pass := tt},
    apply measurable_kernel_prod_mk_left,
    exact (s n).measurable_set_fiber x },
  have h2f' : tendsto f' at_top (𝓝 (λ (x : α), ∫ (y : β), f x y ∂(κ x))),
  { rw [tendsto_pi_nhds], intro x,
    by_cases hfx : integrable (f x) (κ x),
    { have : ∀ n, integrable (s' n x) (κ x),
      { intro n, apply (hfx.norm.add hfx.norm).mono' (s' n x).ae_strongly_measurable,
        apply eventually_of_forall, intro y,
        simp_rw [s', simple_func.coe_comp], exact simple_func.norm_approx_on_zero_le _ _ (x, y) n },
      simp only [f', hfx, simple_func.integral_eq_integral _ (this _), indicator_of_mem,
        mem_set_of_eq],
      refine tendsto_integral_of_dominated_convergence (λ y, ‖f x y‖ + ‖f x y‖)
        (λ n, (s' n x).ae_strongly_measurable) (hfx.norm.add hfx.norm) _ _,
      { exact λ n, eventually_of_forall (λ y, simple_func.norm_approx_on_zero_le _ _ (x, y) n) },
      { refine eventually_of_forall (λ y, simple_func.tendsto_approx_on _ _ _),
        apply subset_closure,
        simp [-uncurry_apply_pair], } },
    { simp [f', hfx, integral_undef], } },
  exact strongly_measurable_of_tendsto _ hf' h2f',
end

lemma strongly_measurable.integral_kernel_prod_right'
  ⦃f : α × β → E⦄ (hf : strongly_measurable f) :
  strongly_measurable (λ x, ∫ y, f (x, y) ∂(κ x)) :=
by { rw [← uncurry_curry f] at hf, exact hf.integral_kernel_prod_right }

lemma strongly_measurable.integral_kernel_prod_right''
  {f : β × γ → E} (hf : strongly_measurable f) :
  strongly_measurable (λ x, ∫ y, f (x, y) ∂(η (a, x))) :=
begin
  change strongly_measurable ((λ x, ∫ y, (λ u : (α × β) × γ, f (u.1.2, u.2)) (x, y) ∂(η x))
    ∘ (λ x, (a, x))),
  refine strongly_measurable.comp_measurable _ measurable_prod_mk_left,
  refine measure_theory.strongly_measurable.integral_kernel_prod_right' _,
  exact hf.comp_measurable (measurable_fst.snd.prod_mk measurable_snd),
end

lemma strongly_measurable.integral_kernel_prod_left
  ⦃f : β → α → E⦄ (hf : strongly_measurable (uncurry f)) :
  strongly_measurable (λ y, ∫ x, f x y ∂(κ y)) :=
(hf.comp_measurable measurable_swap).integral_kernel_prod_right'

lemma strongly_measurable.integral_kernel_prod_left'
  ⦃f : β × α → E⦄ (hf : strongly_measurable f) :
  strongly_measurable (λ y, ∫ x, f (x, y) ∂(κ y)) :=
(hf.comp_measurable measurable_swap).integral_kernel_prod_right'

lemma strongly_measurable.integral_kernel_prod_left''
  {f : γ × β → E} (hf : strongly_measurable f) :
  strongly_measurable (λ y, ∫ x, f (x, y) ∂(η (a, y))) :=
begin
  change strongly_measurable ((λ y, ∫ x, (λ u : γ × (α × β), f (u.1, u.2.2)) (x, y) ∂(η y))
    ∘ (λ x, (a, x))),
  refine strongly_measurable.comp_measurable _ measurable_prod_mk_left,
  refine measure_theory.strongly_measurable.integral_kernel_prod_left' _,
  exact hf.comp_measurable (measurable_fst.prod_mk measurable_snd.snd),
end

end measure_theory
