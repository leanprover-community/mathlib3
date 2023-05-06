/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.measure.giry_monad
import dynamics.ergodic.measure_preserving
import measure_theory.integral.set_integral
import measure_theory.measure.open_pos
import probability.kernel.composition

/-!
# Draft
-/

noncomputable theory
open_locale classical topology ennreal measure_theory
open set function real ennreal
open measure_theory measurable_space measure_theory.measure
open topological_space (hiding generate_from)
open filter (hiding prod_eq map)
open probability_theory
open_locale probability_theory

variables {α α' β β' γ E : Type*}
variables [measurable_space α] [measurable_space α'] [measurable_space β] [measurable_space β']
variables [measurable_space γ]
variables {μ μ' : measure α} {ν ν' : measure β} {τ : measure γ}
variables [normed_add_comm_group E]

lemma kernel.measurable_prod_mk_mem' (η : kernel (α × β) γ) [kernel.is_s_finite_kernel η]
  {s : set (β × γ)} (hs : measurable_set s) (a : α) :
  measurable (λ b, η (a, b) {c : γ | (b, c) ∈ s}) :=
begin
  have : ∀ b, {c : γ | (b, c) ∈ s} = {c | ((a, b), c) ∈ {p : (α × β) × γ | (p.1.2, p.2) ∈ s}},
  { intro b, refl, },
  simp_rw this,
  refine (kernel.measurable_prod_mk_mem η _).comp measurable_prod_mk_left,
  exact (measurable_fst.snd.prod_mk measurable_snd) hs,
end

lemma measurable_kernel_prod_mk_left {κ : kernel α β} [kernel.is_s_finite_kernel κ]
  {s : set (α × β)} (hs : measurable_set s) :
  measurable (λ x, κ x (prod.mk x ⁻¹' s)) :=
kernel.measurable_prod_mk_mem κ hs

lemma measurable_kernel_prod_mk_right {κ : kernel β α} [kernel.is_s_finite_kernel κ]
  {s : set (α × β)} (hs : measurable_set s) :
  measurable (λ y, κ y ((λ x, (x, y)) ⁻¹' s)) :=
measurable_kernel_prod_mk_left (measurable_set_swap_iff.mpr hs)

theorem kernel.measurable_lintegral'' (κ : kernel α β) [kernel.is_s_finite_kernel κ]
  {f : (α × β) → ℝ≥0∞} (hf : measurable f) :
  measurable (λ a, ∫⁻ b, f (a, b) ∂(κ a)) :=
kernel.measurable_lintegral κ
begin
  have : function.uncurry (λ (a : α) (b : β), f (a, b)) = f,
  { ext x, rw [← @prod.mk.eta _ _ x, function.uncurry_apply_pair], },
  rwa this,
end

lemma measurable.lintegral_kernel_prod_right' {κ : kernel α β} [kernel.is_s_finite_kernel κ] :
  ∀ {f : α × β → ℝ≥0∞} (hf : measurable f), measurable (λ x, ∫⁻ y, f (x, y) ∂(κ x)) :=
begin
  exact λ f hf, kernel.measurable_lintegral'' κ hf,
end

lemma measurable.lintegral_kernel_prod_right'' {η : kernel (α × β) γ} {a : α}
  [kernel.is_s_finite_kernel η] :
  ∀ {f : β × γ → ℝ≥0∞} (hf : measurable f), measurable (λ x, ∫⁻ y, f (x, y) ∂(η (a, x))) :=
begin
  intros f hf,
  change measurable ((λ x, ∫⁻ y, (λ u : (α × β) × γ, f (u.1.2, u.2)) (x, y) ∂(η x))
    ∘ (λ x, (a, x))),
  refine (measurable.lintegral_kernel_prod_right' _).comp measurable_prod_mk_left,
  exact hf.comp (measurable_fst.snd.prod_mk measurable_snd),
end

lemma measurable.lintegral_kernel_prod_right {κ : kernel α β} [kernel.is_s_finite_kernel κ]
  {f : α → β → ℝ≥0∞} (hf : measurable (uncurry f)) : measurable (λ x, ∫⁻ y, f x y ∂(κ x)) :=
hf.lintegral_kernel_prod_right'

lemma measurable.lintegral_kernel_prod_left' {κ : kernel β α} [kernel.is_s_finite_kernel κ]
  {f : α × β → ℝ≥0∞}
  (hf : measurable f) : measurable (λ y, ∫⁻ x, f (x, y) ∂(κ y)) :=
(measurable_swap_iff.mpr hf).lintegral_kernel_prod_right'

lemma measurable.lintegral_kernel_prod_left {κ : kernel β α} [kernel.is_s_finite_kernel κ]
  {f : α → β → ℝ≥0∞} (hf : measurable (uncurry f)) :
  measurable (λ y, ∫⁻ x, f x y ∂(κ y)) :=
hf.lintegral_kernel_prod_left'

lemma measurable_set_kernel_integrable {κ : kernel α β} [kernel.is_s_finite_kernel κ] ⦃f : α → β → E⦄
  (hf : strongly_measurable (uncurry f)) : measurable_set {x | integrable (f x) (κ x)} :=
begin
  simp_rw [integrable, hf.of_uncurry_left.ae_strongly_measurable, true_and],
  exact measurable_set_lt (measurable.lintegral_kernel_prod_right hf.ennnorm) measurable_const
end

section
variables [normed_space ℝ E] [complete_space E]

lemma measure_theory.strongly_measurable.integral_kernel_prod_right
  {κ : kernel α β} [kernel.is_s_finite_kernel κ] ⦃f : α → β → E⦄
  (hf : strongly_measurable (uncurry f)) : strongly_measurable (λ x, ∫ y, f x y ∂(κ x)) :=
begin
  borelize E,
  haveI : separable_space (range (uncurry f) ∪ {0} : set E) :=
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

lemma measure_theory.strongly_measurable.integral_kernel_prod_right'
  {κ : kernel α β} [kernel.is_s_finite_kernel κ] ⦃f : α × β → E⦄
  (hf : strongly_measurable f) :
  strongly_measurable (λ x, ∫ y, f (x, y) ∂(κ x)) :=
by { rw [← uncurry_curry f] at hf, exact hf.integral_kernel_prod_right }

lemma measure_theory.strongly_measurable.integral_kernel_prod_right'' {η : kernel (α × β) γ}
  [kernel.is_s_finite_kernel η] {a : α} {f : β × γ → E}
  (hf : strongly_measurable f) :
  strongly_measurable (λ x, ∫ y, f (x, y) ∂(η (a, x))) :=
begin
  change strongly_measurable ((λ x, ∫ y, (λ u : (α × β) × γ, f (u.1.2, u.2)) (x, y) ∂(η x))
    ∘ (λ x, (a, x))),
  refine strongly_measurable.comp_measurable _ measurable_prod_mk_left,
  refine measure_theory.strongly_measurable.integral_kernel_prod_right' _,
  exact hf.comp_measurable (measurable_fst.snd.prod_mk measurable_snd),
end

lemma measure_theory.strongly_measurable.integral_kernel_prod_left
  {κ : kernel β α} [kernel.is_s_finite_kernel κ] ⦃f : α → β → E⦄
  (hf : strongly_measurable (uncurry f)) : strongly_measurable (λ y, ∫ x, f x y ∂(κ y)) :=
(hf.comp_measurable measurable_swap).integral_kernel_prod_right'

lemma measure_theory.strongly_measurable.integral_kernel_prod_left'
  {κ : kernel β α} [kernel.is_s_finite_kernel κ] ⦃f : α × β → E⦄
  (hf : strongly_measurable f) : strongly_measurable (λ y, ∫ x, f (x, y) ∂(κ y)) :=
(hf.comp_measurable measurable_swap).integral_kernel_prod_right'

end

/-! ### The product measure -/

namespace measure_theory

lemma ae_kernel_lt_top {κ : kernel α β} [kernel.is_s_finite_kernel κ]
  {η : kernel (α × β) γ} [kernel.is_s_finite_kernel η]
  {s : set (β × γ)} (hs : measurable_set s) (a : α)
  (h2s : (κ ⊗ₖ η) a s ≠ ∞) :
  ∀ᵐ b ∂(κ a), η (a, b) (prod.mk b ⁻¹' s) < ∞ :=
begin
  rw kernel.comp_prod_apply _ _ _ hs at h2s,
  exact ae_lt_top (kernel.measurable_prod_mk_mem' _ hs a) h2s,
end

lemma integrable_kernel_prod_mk_left {κ : kernel α β} [kernel.is_s_finite_kernel κ]
  {η : kernel (α × β) γ} [kernel.is_s_finite_kernel η]
  (a : α)
  {s : set (β × γ)} (hs : measurable_set s) (h2s : (κ ⊗ₖ η) a s ≠ ∞) :
  integrable (λ b, (η (a, b) (prod.mk b ⁻¹' s)).to_real) (κ a) :=
begin
  refine ⟨(kernel.measurable_prod_mk_mem' _ hs a).ennreal_to_real.ae_measurable.ae_strongly_measurable,
    _⟩,
  simp_rw [has_finite_integral, ennnorm_eq_of_real to_real_nonneg],
  convert h2s.lt_top using 1,
  rw kernel.comp_prod_apply _ _ _ hs,
  apply lintegral_congr_ae,
  refine (ae_kernel_lt_top hs a h2s).mp _,
  apply eventually_of_forall,
  intros x hx,
  rw [lt_top_iff_ne_top] at hx,
  simp only,
  rw of_real_to_real hx,
  refl,
end

lemma kernel_comp_prod_null {κ : kernel α β} [kernel.is_s_finite_kernel κ]
  {η : kernel (α × β) γ} [kernel.is_s_finite_kernel η] (a : α)
  {s : set (β × γ)} (hs : measurable_set s) :
  (κ ⊗ₖ η) a s = 0 ↔ (λ b, η (a, b) (prod.mk b ⁻¹' s)) =ᵐ[κ a] 0 :=
begin
  rw [kernel.comp_prod_apply _ _ _ hs,
    lintegral_eq_zero_iff (kernel.measurable_prod_mk_mem' η hs a)],
  refl,
end

lemma kernel_ae_null_of_comp_prod_null {κ : kernel α β} [kernel.is_s_finite_kernel κ]
  {η : kernel (α × β) γ} [kernel.is_s_finite_kernel η]
  {s : set (β × γ)} {a : α}
  (h : (κ ⊗ₖ η) a s = 0) :
  (λ b, η (a, b) (prod.mk b ⁻¹' s)) =ᵐ[κ a] 0 :=
begin
  obtain ⟨t, hst, mt, ht⟩ := exists_measurable_superset_of_null h,
  simp_rw [kernel_comp_prod_null a mt] at ht,
  rw [eventually_le_antisymm_iff],
  exact ⟨eventually_le.trans_eq
    (eventually_of_forall $ λ x, (measure_mono (preimage_mono hst) : _)) ht,
    eventually_of_forall $ λ x, zero_le _⟩
end

lemma ae_ae_of_ae_comp_prod {κ : kernel α β} [kernel.is_s_finite_kernel κ]
  {η : kernel (α × β) γ} [kernel.is_s_finite_kernel η] {a : α}
  {p : β × γ → Prop} (h : ∀ᵐ bc ∂((κ ⊗ₖ η) a), p bc) :
  ∀ᵐ b ∂(κ a), ∀ᵐ c ∂(η (a, b)), p (b, c) :=
kernel_ae_null_of_comp_prod_null h

variables [sigma_finite μ]

/-! ### The product of specific measures -/

lemma comp_prod_restrict {κ : kernel α β} [kernel.is_s_finite_kernel κ]
  {η : kernel (α × β) γ} [kernel.is_s_finite_kernel η]
  {s : set β} {t : set γ} (hs : measurable_set s) (ht : measurable_set t) :
  (kernel.restrict κ hs) ⊗ₖ (kernel.restrict η ht) = kernel.restrict (κ ⊗ₖ η) (hs.prod ht) :=
begin
  ext a u hu : 2,
  rw [kernel.comp_prod_apply _ _ _ hu, kernel.restrict_apply' _ _ _ hu,
    kernel.comp_prod_apply _ _ _ (hu.inter (hs.prod ht))],
  simp only [kernel.restrict_apply, measure.restrict_apply' ht, mem_inter_iff,
    prod_mk_mem_set_prod_eq],
  have : ∀ b, η (a, b) {c : γ | (b, c) ∈ u ∧ b ∈ s ∧ c ∈ t}
    = s.indicator (λ b, η (a, b) ({c : γ | (b, c) ∈ u} ∩ t)) b,
  { intro b,
    rw indicator_apply,
    split_ifs with h,
    { simp only [h, true_and],
      refl, },
    { simp only [h, false_and, and_false, set_of_false, measure_empty], }, },
  simp_rw this,
  rw lintegral_indicator _ hs,
end

lemma kernel.restrict_univ {κ : kernel α β} :
  kernel.restrict κ measurable_set.univ = κ :=
by { ext1 a, rw [kernel.restrict_apply, measure.restrict_univ], }

lemma restrict_comp_prod_eq_comp_prod_univ {κ : kernel α β} [kernel.is_s_finite_kernel κ]
  {η : kernel (α × β) γ} [kernel.is_s_finite_kernel η]
  {s : set β} (hs : measurable_set s) :
  (kernel.restrict κ hs) ⊗ₖ η = kernel.restrict (κ ⊗ₖ η) (hs.prod measurable_set.univ) :=
by { rw ← comp_prod_restrict, congr, exact kernel.restrict_univ.symm, }

end measure_theory

open measure_theory

section

/-- The Bochner integral is a.e.-measurable.
  This shows that the integrand of (the right-hand-side of) Fubini's theorem is a.e.-measurable. -/
lemma measure_theory.ae_strongly_measurable.integral_kernel_prod_right'
  {κ : kernel α β} [kernel.is_s_finite_kernel κ]
  {η : kernel (α × β) γ} [kernel.is_s_finite_kernel η]
  {a : α}
  [normed_space ℝ E] [complete_space E]
  ⦃f : β × γ → E⦄ (hf : ae_strongly_measurable f ((κ ⊗ₖ η) a)) :
  ae_strongly_measurable (λ x, ∫ y, f (x, y) ∂(η (a, x))) (κ a) :=
⟨λ x, ∫ y, hf.mk f (x, y) ∂(η (a, x)), hf.strongly_measurable_mk.integral_kernel_prod_right'',
  by { filter_upwards [ae_ae_of_ae_comp_prod hf.ae_eq_mk] with _ hx using integral_congr_ae hx }⟩

lemma measure_theory.ae_strongly_measurable.comp_prod_mk_left
  {κ : kernel α β} [kernel.is_s_finite_kernel κ]
  {η : kernel (α × β) γ} [kernel.is_s_finite_kernel η]
  {a : α}
  {δ : Type*} [topological_space δ] {f : β × γ → δ}
  (hf : ae_strongly_measurable f ((κ ⊗ₖ η) a)) :
  ∀ᵐ x ∂(κ a), ae_strongly_measurable (λ y, f (x, y)) (η (a , x)) :=
begin
  filter_upwards [ae_ae_of_ae_comp_prod hf.ae_eq_mk] with x hx,
  exact ⟨λ y, hf.mk f (x, y), hf.strongly_measurable_mk.comp_measurable measurable_prod_mk_left, hx⟩
end

end

namespace measure_theory

/-! ### The Lebesgue integral on a product -/

lemma kernel.lintegral_comp_prod''
  {κ : kernel α β} [kernel.is_s_finite_kernel κ]
  {η : kernel (α × β) γ} [kernel.is_s_finite_kernel η]
  {a : α}
  (f : β × γ → ℝ≥0∞) (hf : ae_measurable f ((κ ⊗ₖ η) a)) :
  ∫⁻ z, f z ∂((κ ⊗ₖ η) a) = ∫⁻ x, ∫⁻ y, f (x, y) ∂(η (a, x)) ∂(κ a) :=
begin
  have A : ∫⁻ z, f z ∂((κ ⊗ₖ η) a) = ∫⁻ z, hf.mk f z ∂((κ ⊗ₖ η) a) :=
    lintegral_congr_ae hf.ae_eq_mk,
  have B : ∫⁻ x, ∫⁻ y, f (x, y) ∂(η (a, x)) ∂(κ a) = ∫⁻ x, ∫⁻ y, hf.mk f (x, y) ∂(η (a, x)) ∂(κ a),
  { apply lintegral_congr_ae,
    filter_upwards [ae_ae_of_ae_comp_prod hf.ae_eq_mk] with _ ha using lintegral_congr_ae ha, },
  rw [A, B, kernel.lintegral_comp_prod],
  exact hf.measurable_mk,
end

/-! ### Integrability on a product -/
section

lemma has_finite_integral_comp_prod_iff
  {κ : kernel α β} [kernel.is_s_finite_kernel κ]
  {η : kernel (α × β) γ} [kernel.is_s_finite_kernel η]
  {a : α}
  ⦃f : β × γ → E⦄ (h1f : strongly_measurable f) :
  has_finite_integral f ((κ ⊗ₖ η) a)
    ↔ (∀ᵐ x ∂(κ a), has_finite_integral (λ y, f (x, y)) (η (a, x))) ∧
      has_finite_integral (λ x, ∫ y, ‖f (x, y)‖ ∂(η (a, x))) (κ a) :=
begin
  simp only [has_finite_integral],
  rw kernel.lintegral_comp_prod _ _ _ h1f.ennnorm,
  have : ∀ x, ∀ᵐ y ∂(η (a, x)), 0 ≤ ‖f (x, y)‖ := λ x, eventually_of_forall (λ y, norm_nonneg _),
  simp_rw [integral_eq_lintegral_of_nonneg_ae (this _)
    (h1f.norm.comp_measurable measurable_prod_mk_left).ae_strongly_measurable,
    ennnorm_eq_of_real to_real_nonneg, of_real_norm_eq_coe_nnnorm],
  -- this fact is probably too specialized to be its own lemma
  have : ∀ {p q r : Prop} (h1 : r → p), (r ↔ p ∧ q) ↔ (p → (r ↔ q)) :=
  λ p q r h1, by rw [← and.congr_right_iff, and_iff_right_of_imp h1],
  rw [this],
  { intro h2f, rw lintegral_congr_ae,
    refine h2f.mp _, apply eventually_of_forall, intros x hx, dsimp only,
    rw [of_real_to_real], rw [← lt_top_iff_ne_top], exact hx },
  { intro h2f, refine ae_lt_top _ h2f.ne, exact h1f.ennnorm.lintegral_kernel_prod_right'' },
end

lemma has_finite_integral_comp_prod_iff'
  {κ : kernel α β} [kernel.is_s_finite_kernel κ]
  {η : kernel (α × β) γ} [kernel.is_s_finite_kernel η]
  {a : α}
  ⦃f : β × γ → E⦄ (h1f : ae_strongly_measurable f ((κ ⊗ₖ η) a)) :
  has_finite_integral f ((κ ⊗ₖ η) a)
    ↔ (∀ᵐ x ∂(κ a), has_finite_integral (λ y, f (x, y)) (η (a, x))) ∧
      has_finite_integral (λ x, ∫ y, ‖f (x, y)‖ ∂(η (a, x))) (κ a) :=
begin
  rw [has_finite_integral_congr h1f.ae_eq_mk,
    has_finite_integral_comp_prod_iff h1f.strongly_measurable_mk],
  apply and_congr,
  { apply eventually_congr,
    filter_upwards [ae_ae_of_ae_comp_prod h1f.ae_eq_mk.symm],
    assume x hx,
    exact has_finite_integral_congr hx },
  { apply has_finite_integral_congr,
    filter_upwards [ae_ae_of_ae_comp_prod h1f.ae_eq_mk.symm] with _ hx
      using integral_congr_ae (eventually_eq.fun_comp hx _), },
end

lemma integrable_comp_prod_iff
  {κ : kernel α β} [kernel.is_s_finite_kernel κ]
  {η : kernel (α × β) γ} [kernel.is_s_finite_kernel η]
  {a : α}
  ⦃f : β × γ → E⦄ (h1f : ae_strongly_measurable f ((κ ⊗ₖ η) a)) :
  integrable f ((κ ⊗ₖ η) a) ↔
    (∀ᵐ x ∂(κ a), integrable (λ y, f (x, y)) (η (a, x)))
    ∧ integrable (λ x, ∫ y, ‖f (x, y)‖ ∂(η (a, x))) (κ a) :=
by simp only [integrable, has_finite_integral_comp_prod_iff' h1f,
  h1f.norm.integral_kernel_prod_right', h1f, h1f.comp_prod_mk_left, eventually_and, true_and]

lemma integrable.comp_prod_right_ae
  {κ : kernel α β} [kernel.is_s_finite_kernel κ]
  {η : kernel (α × β) γ} [kernel.is_s_finite_kernel η]
  {a : α}
  ⦃f : β × γ → E⦄ (hf : integrable f ((κ ⊗ₖ η) a)) :
  ∀ᵐ x ∂(κ a), integrable (λ y, f (x, y)) (η (a, x)) :=
((integrable_comp_prod_iff hf.ae_strongly_measurable).mp hf).1

lemma integrable.integral_norm_comp_prod_left
  {κ : kernel α β} [kernel.is_s_finite_kernel κ]
  {η : kernel (α × β) γ} [kernel.is_s_finite_kernel η]
  {a : α}
  ⦃f : β × γ → E⦄ (hf : integrable f ((κ ⊗ₖ η) a)) :
  integrable (λ x, ∫ y, ‖f (x, y)‖ ∂(η (a, x))) (κ a) :=
((integrable_comp_prod_iff hf.ae_strongly_measurable).mp hf).2

end

variables [normed_space ℝ E] [complete_space E]

lemma integrable.integral_comp_prod_left
  {κ : kernel α β} [kernel.is_s_finite_kernel κ]
  {η : kernel (α × β) γ} [kernel.is_s_finite_kernel η]
  {a : α}
  ⦃f : β × γ → E⦄ (hf : integrable f ((κ ⊗ₖ η) a)) :
  integrable (λ x, ∫ y, f (x, y) ∂(η (a, x))) (κ a) :=
integrable.mono hf.integral_norm_comp_prod_left
  hf.ae_strongly_measurable.integral_kernel_prod_right' $
  eventually_of_forall $ λ x, (norm_integral_le_integral_norm _).trans_eq $
  (norm_of_nonneg $ integral_nonneg_of_ae $ eventually_of_forall $
  λ y, (norm_nonneg (f (x, y)) : _)).symm

/-! ### The Bochner integral on a product -/

variables {κ : kernel α β} [kernel.is_s_finite_kernel κ]
  {η : kernel (α × β) γ} [kernel.is_s_finite_kernel η]
  {a : α}
  {E' : Type*} [normed_add_comm_group E'] [complete_space E'] [normed_space ℝ E']

lemma kernel.integral_fn_integral_add ⦃f g : β × γ → E⦄ (F : E → E')
  (hf : integrable f ((κ ⊗ₖ η) a)) (hg : integrable g ((κ ⊗ₖ η) a)) :
  ∫ x, F (∫ y, f (x, y) + g (x, y) ∂(η (a, x))) ∂(κ a)
    = ∫ x, F (∫ y, f (x, y) ∂(η (a, x)) + ∫ y, g (x, y) ∂(η (a, x))) ∂(κ a) :=
begin
  refine integral_congr_ae _,
  filter_upwards [hf.comp_prod_right_ae, hg.comp_prod_right_ae] with _ h2f h2g,
  simp [integral_add h2f h2g],
end

lemma kernel.integral_fn_integral_sub ⦃f g : β × γ → E⦄ (F : E → E')
  (hf : integrable f ((κ ⊗ₖ η) a)) (hg : integrable g ((κ ⊗ₖ η) a)) :
  ∫ x, F (∫ y, f (x, y) - g (x, y) ∂(η (a, x))) ∂(κ a)
    = ∫ x, F (∫ y, f (x, y) ∂(η (a, x)) - ∫ y, g (x, y) ∂(η (a, x))) ∂(κ a) :=
begin
  refine integral_congr_ae _,
  filter_upwards [hf.comp_prod_right_ae, hg.comp_prod_right_ae] with _ h2f h2g,
  simp [integral_sub h2f h2g],
end

lemma kernel.lintegral_fn_integral_sub ⦃f g : β × γ → E⦄
  (F : E → ℝ≥0∞) (hf : integrable f ((κ ⊗ₖ η) a)) (hg : integrable g ((κ ⊗ₖ η) a)) :
  ∫⁻ x, F (∫ y, f (x, y) - g (x, y) ∂(η (a, x))) ∂(κ a)
    = ∫⁻ x, F (∫ y, f (x, y) ∂(η (a, x)) - ∫ y, g (x, y) ∂(η (a, x))) ∂(κ a) :=
begin
  refine lintegral_congr_ae _,
  filter_upwards [hf.comp_prod_right_ae, hg.comp_prod_right_ae] with _ h2f h2g,
  simp [integral_sub h2f h2g],
end

lemma kernel.integral_integral_add ⦃f g : β × γ → E⦄
  (hf : integrable f ((κ ⊗ₖ η) a)) (hg : integrable g ((κ ⊗ₖ η) a)) :
  ∫ x, ∫ y, f (x, y) + g (x, y) ∂(η (a, x)) ∂(κ a)
    = ∫ x, ∫ y, f (x, y) ∂(η (a, x)) ∂(κ a) + ∫ x, ∫ y, g (x, y) ∂(η (a, x)) ∂(κ a) :=
(kernel.integral_fn_integral_add id hf hg).trans $
  integral_add hf.integral_comp_prod_left hg.integral_comp_prod_left

lemma kernel.integral_integral_add' ⦃f g : β × γ → E⦄
  (hf : integrable f ((κ ⊗ₖ η) a)) (hg : integrable g ((κ ⊗ₖ η) a)) :
  ∫ x, ∫ y, (f + g) (x, y) ∂(η (a, x)) ∂(κ a)
    = ∫ x, ∫ y, f (x, y) ∂(η (a, x)) ∂(κ a) + ∫ x, ∫ y, g (x, y) ∂(η (a, x)) ∂(κ a) :=
kernel.integral_integral_add hf hg

lemma kernel.integral_integral_sub ⦃f g : β × γ → E⦄
  (hf : integrable f ((κ ⊗ₖ η) a)) (hg : integrable g ((κ ⊗ₖ η) a)) :
  ∫ x, ∫ y, f (x, y) - g (x, y) ∂(η (a, x)) ∂(κ a)
    = ∫ x, ∫ y, f (x, y) ∂(η (a, x)) ∂(κ a) - ∫ x, ∫ y, g (x, y) ∂(η (a, x)) ∂(κ a) :=
(kernel.integral_fn_integral_sub id hf hg).trans $
  integral_sub hf.integral_comp_prod_left hg.integral_comp_prod_left

lemma kernel.integral_integral_sub' ⦃f g : β × γ → E⦄
  (hf : integrable f ((κ ⊗ₖ η) a)) (hg : integrable g ((κ ⊗ₖ η) a)) :
  ∫ x, ∫ y, (f - g) (x, y) ∂(η (a, x)) ∂(κ a)
    = ∫ x, ∫ y, f (x, y) ∂(η (a, x)) ∂(κ a) - ∫ x, ∫ y, g (x, y) ∂(η (a, x)) ∂(κ a) :=
kernel.integral_integral_sub hf hg

lemma kernel.continuous_integral_integral :
  continuous (λ (f : α × β →₁[(κ ⊗ₖ η) a] E), ∫ x, ∫ y, f (x, y) ∂(η (a, x)) ∂(κ a)) :=
begin
  rw [continuous_iff_continuous_at], intro g,
  refine tendsto_integral_of_L1 _ (L1.integrable_coe_fn g).integral_comp_prod_left
    (eventually_of_forall $ λ h, (L1.integrable_coe_fn h).integral_comp_prod_left) _,
  simp_rw [← kernel.lintegral_fn_integral_sub (λ x, (‖x‖₊ : ℝ≥0∞)) (L1.integrable_coe_fn _)
    (L1.integrable_coe_fn g)],
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _ (λ i, zero_le _) _,
  { exact λ i, ∫⁻ x, ∫⁻ y, ‖i (x, y) - g (x, y)‖₊ ∂(η (a, x)) ∂(κ a) },
  swap, { exact λ i, lintegral_mono (λ x, ennnorm_integral_le_lintegral_ennnorm _) },
  show tendsto (λ (i : β × γ →₁[(κ ⊗ₖ η) a] E),
    ∫⁻ x, ∫⁻ (y : γ), ‖i (x, y) - g (x, y)‖₊ ∂(η (a, x)) ∂(κ a)) (𝓝 g) (𝓝 0),
  have : ∀ (i : α × β →₁[(κ ⊗ₖ η) a] E), measurable (λ z, (‖i z - g z‖₊ : ℝ≥0∞)) :=
  λ i, ((Lp.strongly_measurable i).sub (Lp.strongly_measurable g)).ennnorm,
  simp_rw [← kernel.lintegral_comp_prod _ _ _ (this _), ← L1.of_real_norm_sub_eq_lintegral,
    ← of_real_zero],
  refine (continuous_of_real.tendsto 0).comp _,
  rw [← tendsto_iff_norm_tendsto_zero], exact tendsto_id
end

lemma integral_comp_prod : ∀ (f : β × γ → E) (hf : integrable f ((κ ⊗ₖ η) a)),
  ∫ z, f z ∂((κ ⊗ₖ η) a) = ∫ x, ∫ y, f (x, y) ∂(η (a, x)) ∂(κ a) :=
begin
  apply integrable.induction,
  { intros c s hs h2s,
    simp_rw [integral_indicator hs, ← indicator_comp_right,
      function.comp, integral_indicator (measurable_prod_mk_left hs),
      set_integral_const, integral_smul_const],
    congr' 1,
    rw integral_to_real,
    rotate,
    { exact (kernel.measurable_prod_mk_mem' _ hs _).ae_measurable, },
    { exact (ae_kernel_lt_top hs _ h2s.ne), },
    rw kernel.comp_prod_apply _ _ _ hs,
    refl, },
  { intros f g hfg i_f i_g hf hg,
    simp_rw [integral_add' i_f i_g, kernel.integral_integral_add' i_f i_g, hf, hg] },
  { exact is_closed_eq continuous_integral kernel.continuous_integral_integral },
  { intros f g hfg i_f hf, convert hf using 1,
    { exact integral_congr_ae hfg.symm },
    { refine integral_congr_ae _,
      refine (ae_ae_of_ae_comp_prod hfg).mp _,
      apply eventually_of_forall, intros x hfgx,
      exact integral_congr_ae (ae_eq_symm hfgx) } }
end

lemma set_integral_comp_prod (f : β × γ → E) {s : set β} {t : set γ}
  (hs : measurable_set s) (ht : measurable_set t)
  (hf : integrable_on f (s ×ˢ t) ((κ ⊗ₖ η) a)) :
  ∫ z in s ×ˢ t, f z ∂((κ ⊗ₖ η) a) = ∫ x in s, ∫ y in t, f (x, y) ∂(η (a, x)) ∂(κ a) :=
begin
  rw [← kernel.restrict_apply (κ ⊗ₖ η) (hs.prod ht), ← comp_prod_restrict, integral_comp_prod],
  { simp_rw kernel.restrict_apply, },
  { rw [comp_prod_restrict, kernel.restrict_apply], exact hf, },
end

end measure_theory
