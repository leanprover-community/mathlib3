/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.constructions.prod.basic
import measure_theory.integral.set_integral

/-!
# Integration with respect to the product measure

In this file we prove Fubini's theorem.

## Main results

* `measure_theory.integrable_prod_iff` states that a binary function is integrable iff both
  * `y ↦ f (x, y)` is integrable for almost every `x`, and
  * the function `x ↦ ∫ ‖f (x, y)‖ dy` is integrable.
* `measure_theory.integral_prod`: Fubini's theorem. It states that for a integrable function
  `α × β → E` (where `E` is a second countable Banach space) we have
  `∫ z, f z ∂(μ.prod ν) = ∫ x, ∫ y, f (x, y) ∂ν ∂μ`. This theorem has the same variants as
  Tonelli's theorem (see `measure_theory.lintegral_prod`). The lemma
  `measure_theory.integrable.integral_prod_right` states that the inner integral of the right-hand
  side is integrable.

## Tags

product measure, Fubini's theorem, Fubini-Tonelli theorem
-/

noncomputable theory
open_locale classical topology ennreal measure_theory
open set function real ennreal
open measure_theory measurable_space measure_theory.measure
open topological_space
open filter (hiding prod_eq map)

variables {α α' β β' γ E : Type*}

variables [measurable_space α] [measurable_space α'] [measurable_space β] [measurable_space β']
variables [measurable_space γ]
variables {μ μ' : measure α} {ν ν' : measure β} {τ : measure γ}
variables [normed_add_comm_group E]

/-! ### Measurability

Before we define the product measure, we can talk about the measurability of operations on binary
functions. We show that if `f` is a binary measurable function, then the function that integrates
along one of the variables (using either the Lebesgue or Bochner integral) is measurable.
-/

lemma measurable_set_integrable [sigma_finite ν] ⦃f : α → β → E⦄
  (hf : strongly_measurable (uncurry f)) : measurable_set {x | integrable (f x) ν} :=
begin
  simp_rw [integrable, hf.of_uncurry_left.ae_strongly_measurable, true_and],
  exact measurable_set_lt (measurable.lintegral_prod_right hf.ennnorm) measurable_const
end

section
variables [normed_space ℝ E] [complete_space E]

/-- The Bochner integral is measurable. This shows that the integrand of (the right-hand-side of)
  Fubini's theorem is measurable.
  This version has `f` in curried form. -/
lemma measure_theory.strongly_measurable.integral_prod_right [sigma_finite ν] ⦃f : α → β → E⦄
  (hf : strongly_measurable (uncurry f)) : strongly_measurable (λ x, ∫ y, f x y ∂ν) :=
begin
  borelize E,
  haveI : separable_space (range (uncurry f) ∪ {0} : set E) :=
    hf.separable_space_range_union_singleton,
  let s : ℕ → simple_func (α × β) E := simple_func.approx_on _ hf.measurable
    (range (uncurry f) ∪ {0}) 0 (by simp),
  let s' : ℕ → α → simple_func β E := λ n x, (s n).comp (prod.mk x) measurable_prod_mk_left,
  let f' : ℕ → α → E := λ n, {x | integrable (f x) ν}.indicator
    (λ x, (s' n x).integral ν),
  have hf' : ∀ n, strongly_measurable (f' n),
  { intro n, refine strongly_measurable.indicator _ (measurable_set_integrable hf),
    have : ∀ x, (s' n x).range.filter (λ x, x ≠ 0) ⊆ (s n).range,
    { intros x, refine finset.subset.trans (finset.filter_subset _ _) _, intro y,
      simp_rw [simple_func.mem_range], rintro ⟨z, rfl⟩, exact ⟨(x, z), rfl⟩ },
    simp only [simple_func.integral_eq_sum_of_subset (this _)],
    refine finset.strongly_measurable_sum _ (λ x _, _),
    refine (measurable.ennreal_to_real _).strongly_measurable.smul_const _,
    simp only [simple_func.coe_comp, preimage_comp] {single_pass := tt},
    apply measurable_measure_prod_mk_left,
    exact (s n).measurable_set_fiber x },
  have h2f' : tendsto f' at_top (𝓝 (λ (x : α), ∫ (y : β), f x y ∂ν)),
  { rw [tendsto_pi_nhds], intro x,
    by_cases hfx : integrable (f x) ν,
    { have : ∀ n, integrable (s' n x) ν,
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
  exact strongly_measurable_of_tendsto _ hf' h2f'
end

/-- The Bochner integral is measurable. This shows that the integrand of (the right-hand-side of)
  Fubini's theorem is measurable. -/
lemma measure_theory.strongly_measurable.integral_prod_right' [sigma_finite ν] ⦃f : α × β → E⦄
  (hf : strongly_measurable f) : strongly_measurable (λ x, ∫ y, f (x, y) ∂ν) :=
by { rw [← uncurry_curry f] at hf, exact hf.integral_prod_right }

/-- The Bochner integral is measurable. This shows that the integrand of (the right-hand-side of)
  the symmetric version of Fubini's theorem is measurable.
  This version has `f` in curried form. -/
lemma measure_theory.strongly_measurable.integral_prod_left [sigma_finite μ] ⦃f : α → β → E⦄
  (hf : strongly_measurable (uncurry f)) : strongly_measurable (λ y, ∫ x, f x y ∂μ) :=
(hf.comp_measurable measurable_swap).integral_prod_right'

/-- The Bochner integral is measurable. This shows that the integrand of (the right-hand-side of)
  the symmetric version of Fubini's theorem is measurable. -/
lemma measure_theory.strongly_measurable.integral_prod_left' [sigma_finite μ] ⦃f : α × β → E⦄
  (hf : strongly_measurable f) : strongly_measurable (λ y, ∫ x, f (x, y) ∂μ) :=
(hf.comp_measurable measurable_swap).integral_prod_right'

end

/-! ### The product measure -/

namespace measure_theory

namespace measure

variables [sigma_finite ν]

lemma integrable_measure_prod_mk_left {s : set (α × β)}
  (hs : measurable_set s) (h2s : (μ.prod ν) s ≠ ∞) :
  integrable (λ x, (ν (prod.mk x ⁻¹' s)).to_real) μ :=
begin
  refine ⟨(measurable_measure_prod_mk_left hs).ennreal_to_real.ae_measurable.ae_strongly_measurable,
    _⟩,
  simp_rw [has_finite_integral, ennnorm_eq_of_real to_real_nonneg],
  convert h2s.lt_top using 1, simp_rw [prod_apply hs], apply lintegral_congr_ae,
  refine (ae_measure_lt_top hs h2s).mp _, apply eventually_of_forall, intros x hx,
  rw [lt_top_iff_ne_top] at hx, simp [of_real_to_real, hx],
end

end measure

open measure

end measure_theory

open measure_theory.measure

section

lemma measure_theory.ae_strongly_measurable.prod_swap
  {γ : Type*} [topological_space γ] [sigma_finite μ] [sigma_finite ν] {f : β × α → γ}
  (hf : ae_strongly_measurable f (ν.prod μ)) :
  ae_strongly_measurable (λ (z : α × β), f z.swap) (μ.prod ν) :=
by { rw ← prod_swap at hf, exact hf.comp_measurable measurable_swap }

lemma measure_theory.ae_strongly_measurable.fst {γ} [topological_space γ] [sigma_finite ν]
  {f : α → γ} (hf : ae_strongly_measurable f μ) :
  ae_strongly_measurable (λ (z : α × β), f z.1) (μ.prod ν) :=
hf.comp_quasi_measure_preserving quasi_measure_preserving_fst

lemma measure_theory.ae_strongly_measurable.snd {γ} [topological_space γ] [sigma_finite ν]
  {f : β → γ} (hf : ae_strongly_measurable f ν) :
  ae_strongly_measurable (λ (z : α × β), f z.2) (μ.prod ν) :=
hf.comp_quasi_measure_preserving quasi_measure_preserving_snd

/-- The Bochner integral is a.e.-measurable.
  This shows that the integrand of (the right-hand-side of) Fubini's theorem is a.e.-measurable. -/
lemma measure_theory.ae_strongly_measurable.integral_prod_right' [sigma_finite ν]
  [normed_space ℝ E] [complete_space E]
  ⦃f : α × β → E⦄ (hf : ae_strongly_measurable f (μ.prod ν)) :
  ae_strongly_measurable (λ x, ∫ y, f (x, y) ∂ν) μ :=
⟨λ x, ∫ y, hf.mk f (x, y) ∂ν, hf.strongly_measurable_mk.integral_prod_right',
  by { filter_upwards [ae_ae_of_ae_prod hf.ae_eq_mk] with _ hx using integral_congr_ae hx }⟩

lemma measure_theory.ae_strongly_measurable.prod_mk_left
  {γ : Type*} [sigma_finite ν] [topological_space γ] {f : α × β → γ}
  (hf : ae_strongly_measurable f (μ.prod ν)) : ∀ᵐ x ∂μ, ae_strongly_measurable (λ y, f (x, y)) ν :=
begin
  filter_upwards [ae_ae_of_ae_prod hf.ae_eq_mk] with x hx,
  exact ⟨λ y, hf.mk f (x, y), hf.strongly_measurable_mk.comp_measurable measurable_prod_mk_left, hx⟩
end

end

namespace measure_theory

variables [sigma_finite ν]

/-! ### Integrability on a product -/
section

lemma integrable.swap [sigma_finite μ] ⦃f : α × β → E⦄
  (hf : integrable f (μ.prod ν)) : integrable (f ∘ prod.swap) (ν.prod μ) :=
⟨hf.ae_strongly_measurable.prod_swap,
  (lintegral_prod_swap _ hf.ae_strongly_measurable.ennnorm : _).le.trans_lt hf.has_finite_integral⟩

lemma integrable_swap_iff [sigma_finite μ] ⦃f : α × β → E⦄ :
  integrable (f ∘ prod.swap) (ν.prod μ) ↔ integrable f (μ.prod ν) :=
⟨λ hf, by { convert hf.swap, ext ⟨x, y⟩, refl }, λ hf, hf.swap⟩

lemma has_finite_integral_prod_iff ⦃f : α × β → E⦄ (h1f : strongly_measurable f) :
  has_finite_integral f (μ.prod ν) ↔ (∀ᵐ x ∂ μ, has_finite_integral (λ y, f (x, y)) ν) ∧
    has_finite_integral (λ x, ∫ y, ‖f (x, y)‖ ∂ν) μ :=
begin
  simp only [has_finite_integral, lintegral_prod_of_measurable _ h1f.ennnorm],
  have : ∀ x, ∀ᵐ y ∂ν, 0 ≤ ‖f (x, y)‖ := λ x, eventually_of_forall (λ y, norm_nonneg _),
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
  { intro h2f, refine ae_lt_top _ h2f.ne, exact h1f.ennnorm.lintegral_prod_right' },
end

lemma has_finite_integral_prod_iff' ⦃f : α × β → E⦄ (h1f : ae_strongly_measurable f (μ.prod ν)) :
  has_finite_integral f (μ.prod ν) ↔ (∀ᵐ x ∂ μ, has_finite_integral (λ y, f (x, y)) ν) ∧
    has_finite_integral (λ x, ∫ y, ‖f (x, y)‖ ∂ν) μ :=
begin
  rw [has_finite_integral_congr h1f.ae_eq_mk,
    has_finite_integral_prod_iff h1f.strongly_measurable_mk],
  apply and_congr,
  { apply eventually_congr,
    filter_upwards [ae_ae_of_ae_prod h1f.ae_eq_mk.symm],
    assume x hx,
    exact has_finite_integral_congr hx },
  { apply has_finite_integral_congr,
    filter_upwards [ae_ae_of_ae_prod h1f.ae_eq_mk.symm] with _ hx
      using integral_congr_ae (eventually_eq.fun_comp hx _), },
  { apply_instance, },
end

/-- A binary function is integrable if the function `y ↦ f (x, y)` is integrable for almost every
  `x` and the function `x ↦ ∫ ‖f (x, y)‖ dy` is integrable. -/
lemma integrable_prod_iff ⦃f : α × β → E⦄ (h1f : ae_strongly_measurable f (μ.prod ν)) :
  integrable f (μ.prod ν) ↔
    (∀ᵐ x ∂ μ, integrable (λ y, f (x, y)) ν) ∧ integrable (λ x, ∫ y, ‖f (x, y)‖ ∂ν) μ :=
by simp [integrable, h1f, has_finite_integral_prod_iff', h1f.norm.integral_prod_right',
         h1f.prod_mk_left]

/-- A binary function is integrable if the function `x ↦ f (x, y)` is integrable for almost every
  `y` and the function `y ↦ ∫ ‖f (x, y)‖ dx` is integrable. -/
lemma integrable_prod_iff' [sigma_finite μ] ⦃f : α × β → E⦄
  (h1f : ae_strongly_measurable f (μ.prod ν)) :
  integrable f (μ.prod ν) ↔
    (∀ᵐ y ∂ ν, integrable (λ x, f (x, y)) μ) ∧ integrable (λ y, ∫ x, ‖f (x, y)‖ ∂μ) ν :=
by { convert integrable_prod_iff (h1f.prod_swap) using 1, rw [integrable_swap_iff] }

lemma integrable.prod_left_ae [sigma_finite μ] ⦃f : α × β → E⦄
  (hf : integrable f (μ.prod ν)) : ∀ᵐ y ∂ ν, integrable (λ x, f (x, y)) μ :=
((integrable_prod_iff' hf.ae_strongly_measurable).mp hf).1

lemma integrable.prod_right_ae [sigma_finite μ] ⦃f : α × β → E⦄
  (hf : integrable f (μ.prod ν)) : ∀ᵐ x ∂ μ, integrable (λ y, f (x, y)) ν :=
hf.swap.prod_left_ae

lemma integrable.integral_norm_prod_left ⦃f : α × β → E⦄
  (hf : integrable f (μ.prod ν)) : integrable (λ x, ∫ y, ‖f (x, y)‖ ∂ν) μ :=
((integrable_prod_iff hf.ae_strongly_measurable).mp hf).2

lemma integrable.integral_norm_prod_right [sigma_finite μ] ⦃f : α × β → E⦄
  (hf : integrable f (μ.prod ν)) : integrable (λ y, ∫ x, ‖f (x, y)‖ ∂μ) ν :=
hf.swap.integral_norm_prod_left

lemma integrable_prod_mul {L : Type*} [is_R_or_C L]
  {f : α → L} {g : β → L} (hf : integrable f μ) (hg : integrable g ν) :
  integrable (λ (z : α × β), f z.1 * g z.2) (μ.prod ν) :=
begin
  refine (integrable_prod_iff _).2 ⟨_, _⟩,
  { exact hf.1.fst.mul hg.1.snd },
  { exact eventually_of_forall (λ x, hg.const_mul (f x)) },
  { simpa only [norm_mul, integral_mul_left] using hf.norm.mul_const _ }
end

end

variables [normed_space ℝ E] [complete_space E]

lemma integrable.integral_prod_left ⦃f : α × β → E⦄
  (hf : integrable f (μ.prod ν)) : integrable (λ x, ∫ y, f (x, y) ∂ν) μ :=
integrable.mono hf.integral_norm_prod_left hf.ae_strongly_measurable.integral_prod_right' $
  eventually_of_forall $ λ x, (norm_integral_le_integral_norm _).trans_eq $
  (norm_of_nonneg $ integral_nonneg_of_ae $ eventually_of_forall $
  λ y, (norm_nonneg (f (x, y)) : _)).symm

lemma integrable.integral_prod_right [sigma_finite μ] ⦃f : α × β → E⦄
  (hf : integrable f (μ.prod ν)) : integrable (λ y, ∫ x, f (x, y) ∂μ) ν :=
hf.swap.integral_prod_left

/-! ### The Bochner integral on a product -/

variables [sigma_finite μ]

lemma integral_prod_swap (f : α × β → E)
  (hf : ae_strongly_measurable f (μ.prod ν)) : ∫ z, f z.swap ∂(ν.prod μ) = ∫ z, f z ∂(μ.prod ν) :=
begin
  rw ← prod_swap at hf,
  rw [← integral_map measurable_swap.ae_measurable hf, prod_swap]
end

variables {E' : Type*} [normed_add_comm_group E'] [complete_space E'] [normed_space ℝ E']

/-! Some rules about the sum/difference of double integrals. They follow from `integral_add`, but
  we separate them out as separate lemmas, because they involve quite some steps. -/

/-- Integrals commute with addition inside another integral. `F` can be any function. -/
lemma integral_fn_integral_add ⦃f g : α × β → E⦄ (F : E → E')
  (hf : integrable f (μ.prod ν)) (hg : integrable g (μ.prod ν)) :
  ∫ x, F (∫ y, f (x, y) + g (x, y) ∂ν) ∂μ = ∫ x, F (∫ y, f (x, y) ∂ν + ∫ y, g (x, y) ∂ν) ∂μ :=
begin
  refine integral_congr_ae _,
  filter_upwards [hf.prod_right_ae, hg.prod_right_ae] with _ h2f h2g,
  simp [integral_add h2f h2g],
end

/-- Integrals commute with subtraction inside another integral.
  `F` can be any measurable function. -/
lemma integral_fn_integral_sub ⦃f g : α × β → E⦄ (F : E → E')
  (hf : integrable f (μ.prod ν)) (hg : integrable g (μ.prod ν)) :
  ∫ x, F (∫ y, f (x, y) - g (x, y) ∂ν) ∂μ = ∫ x, F (∫ y, f (x, y) ∂ν - ∫ y, g (x, y) ∂ν) ∂μ :=
begin
  refine integral_congr_ae _,
  filter_upwards [hf.prod_right_ae, hg.prod_right_ae] with _ h2f h2g,
  simp [integral_sub h2f h2g],
end

/-- Integrals commute with subtraction inside a lower Lebesgue integral.
  `F` can be any function. -/
lemma lintegral_fn_integral_sub ⦃f g : α × β → E⦄
  (F : E → ℝ≥0∞) (hf : integrable f (μ.prod ν)) (hg : integrable g (μ.prod ν)) :
  ∫⁻ x, F (∫ y, f (x, y) - g (x, y) ∂ν) ∂μ = ∫⁻ x, F (∫ y, f (x, y) ∂ν - ∫ y, g (x, y) ∂ν) ∂μ :=
begin
  refine lintegral_congr_ae _,
  filter_upwards [hf.prod_right_ae, hg.prod_right_ae] with _ h2f h2g,
  simp [integral_sub h2f h2g],
end

/-- Double integrals commute with addition. -/
lemma integral_integral_add ⦃f g : α × β → E⦄
  (hf : integrable f (μ.prod ν)) (hg : integrable g (μ.prod ν)) :
  ∫ x, ∫ y, f (x, y) + g (x, y) ∂ν ∂μ = ∫ x, ∫ y, f (x, y) ∂ν ∂μ + ∫ x, ∫ y, g (x, y) ∂ν ∂μ :=
(integral_fn_integral_add id hf hg).trans $
  integral_add hf.integral_prod_left hg.integral_prod_left

/-- Double integrals commute with addition. This is the version with `(f + g) (x, y)`
  (instead of `f (x, y) + g (x, y)`) in the LHS. -/
lemma integral_integral_add' ⦃f g : α × β → E⦄
  (hf : integrable f (μ.prod ν)) (hg : integrable g (μ.prod ν)) :
  ∫ x, ∫ y, (f + g) (x, y) ∂ν ∂μ = ∫ x, ∫ y, f (x, y) ∂ν ∂μ + ∫ x, ∫ y, g (x, y) ∂ν ∂μ :=
integral_integral_add hf hg

/-- Double integrals commute with subtraction. -/
lemma integral_integral_sub ⦃f g : α × β → E⦄
  (hf : integrable f (μ.prod ν)) (hg : integrable g (μ.prod ν)) :
  ∫ x, ∫ y, f (x, y) - g (x, y) ∂ν ∂μ = ∫ x, ∫ y, f (x, y) ∂ν ∂μ - ∫ x, ∫ y, g (x, y) ∂ν ∂μ :=
(integral_fn_integral_sub id hf hg).trans $
  integral_sub hf.integral_prod_left hg.integral_prod_left

/-- Double integrals commute with subtraction. This is the version with `(f - g) (x, y)`
  (instead of `f (x, y) - g (x, y)`) in the LHS. -/
lemma integral_integral_sub' ⦃f g : α × β → E⦄
  (hf : integrable f (μ.prod ν)) (hg : integrable g (μ.prod ν)) :
  ∫ x, ∫ y, (f - g) (x, y) ∂ν ∂μ = ∫ x, ∫ y, f (x, y) ∂ν ∂μ - ∫ x, ∫ y, g (x, y) ∂ν ∂μ :=
integral_integral_sub hf hg

/-- The map that sends an L¹-function `f : α × β → E` to `∫∫f` is continuous. -/
lemma continuous_integral_integral :
  continuous (λ (f : α × β →₁[μ.prod ν] E), ∫ x, ∫ y, f (x, y) ∂ν ∂μ) :=
begin
  rw [continuous_iff_continuous_at], intro g,
  refine tendsto_integral_of_L1 _ (L1.integrable_coe_fn g).integral_prod_left
    (eventually_of_forall $ λ h, (L1.integrable_coe_fn h).integral_prod_left) _,
  simp_rw [← lintegral_fn_integral_sub (λ x, (‖x‖₊ : ℝ≥0∞)) (L1.integrable_coe_fn _)
    (L1.integrable_coe_fn g)],
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _ (λ i, zero_le _) _,
  { exact λ i, ∫⁻ x, ∫⁻ y, ‖i (x, y) - g (x, y)‖₊ ∂ν ∂μ },
  swap, { exact λ i, lintegral_mono (λ x, ennnorm_integral_le_lintegral_ennnorm _) },
  show tendsto (λ (i : α × β →₁[μ.prod ν] E),
    ∫⁻ x, ∫⁻ (y : β), ‖i (x, y) - g (x, y)‖₊ ∂ν ∂μ) (𝓝 g) (𝓝 0),
  have : ∀ (i : α × β →₁[μ.prod ν] E), measurable (λ z, (‖i z - g z‖₊ : ℝ≥0∞)) :=
  λ i, ((Lp.strongly_measurable i).sub (Lp.strongly_measurable g)).ennnorm,
  simp_rw [← lintegral_prod_of_measurable _ (this _), ← L1.of_real_norm_sub_eq_lintegral,
    ← of_real_zero],
  refine (continuous_of_real.tendsto 0).comp _,
  rw [← tendsto_iff_norm_tendsto_zero], exact tendsto_id
end

/-- **Fubini's Theorem**: For integrable functions on `α × β`,
  the Bochner integral of `f` is equal to the iterated Bochner integral.
  `integrable_prod_iff` can be useful to show that the function in question in integrable.
  `measure_theory.integrable.integral_prod_right` is useful to show that the inner integral
  of the right-hand side is integrable. -/
lemma integral_prod : ∀ (f : α × β → E) (hf : integrable f (μ.prod ν)),
  ∫ z, f z ∂(μ.prod ν) = ∫ x, ∫ y, f (x, y) ∂ν ∂μ :=
begin
  apply integrable.induction,
  { intros c s hs h2s,
    simp_rw [integral_indicator hs, ← indicator_comp_right,
      function.comp, integral_indicator (measurable_prod_mk_left hs),
      set_integral_const, integral_smul_const,
      integral_to_real (measurable_measure_prod_mk_left hs).ae_measurable
      (ae_measure_lt_top hs h2s.ne), prod_apply hs] },
  { intros f g hfg i_f i_g hf hg,
    simp_rw [integral_add' i_f i_g, integral_integral_add' i_f i_g, hf, hg] },
  { exact is_closed_eq continuous_integral continuous_integral_integral },
  { intros f g hfg i_f hf, convert hf using 1,
    { exact integral_congr_ae hfg.symm },
    { refine integral_congr_ae _,
      refine (ae_ae_of_ae_prod hfg).mp _,
      apply eventually_of_forall, intros x hfgx,
      exact integral_congr_ae (ae_eq_symm hfgx) } }
end

/-- Symmetric version of **Fubini's Theorem**: For integrable functions on `α × β`,
  the Bochner integral of `f` is equal to the iterated Bochner integral.
  This version has the integrals on the right-hand side in the other order. -/
lemma integral_prod_symm (f : α × β → E) (hf : integrable f (μ.prod ν)) :
  ∫ z, f z ∂(μ.prod ν) = ∫ y, ∫ x, f (x, y) ∂μ ∂ν :=
by { simp_rw [← integral_prod_swap f hf.ae_strongly_measurable], exact integral_prod _ hf.swap }

/-- Reversed version of **Fubini's Theorem**. -/
lemma integral_integral {f : α → β → E} (hf : integrable (uncurry f) (μ.prod ν)) :
  ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ z, f z.1 z.2 ∂(μ.prod ν) :=
(integral_prod _ hf).symm

/-- Reversed version of **Fubini's Theorem** (symmetric version). -/
lemma integral_integral_symm {f : α → β → E} (hf : integrable (uncurry f) (μ.prod ν)) :
  ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ z, f z.2 z.1 ∂(ν.prod μ) :=
(integral_prod_symm _ hf.swap).symm

/-- Change the order of Bochner integration. -/
lemma integral_integral_swap ⦃f : α → β → E⦄ (hf : integrable (uncurry f) (μ.prod ν)) :
  ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ y, ∫ x, f x y ∂μ ∂ν :=
(integral_integral hf).trans (integral_prod_symm _ hf)

/-- **Fubini's Theorem** for set integrals. -/
lemma set_integral_prod (f : α × β → E) {s : set α} {t : set β}
  (hf : integrable_on f (s ×ˢ t) (μ.prod ν)) :
  ∫ z in s ×ˢ t, f z ∂(μ.prod ν) = ∫ x in s, ∫ y in t, f (x, y) ∂ν ∂μ :=
begin
  simp only [← measure.prod_restrict s t, integrable_on] at hf ⊢,
  exact integral_prod f hf
end

lemma integral_prod_mul {L : Type*} [is_R_or_C L] (f : α → L) (g : β → L) :
  ∫ z, f z.1 * g z.2 ∂(μ.prod ν) = (∫ x, f x ∂μ) * (∫ y, g y ∂ν) :=
begin
  by_cases h : integrable (λ (z : α × β), f z.1 * g z.2) (μ.prod ν),
  { rw integral_prod _ h,
    simp_rw [integral_mul_left, integral_mul_right] },
  have H : ¬(integrable f μ) ∨ ¬(integrable g ν),
  { contrapose! h,
    exact integrable_prod_mul h.1 h.2 },
  cases H;
  simp [integral_undef h, integral_undef H],
end

lemma set_integral_prod_mul {L : Type*} [is_R_or_C L]
  (f : α → L) (g : β → L) (s : set α) (t : set β) :
  ∫ z in s ×ˢ t, f z.1 * g z.2 ∂(μ.prod ν) = (∫ x in s, f x ∂μ) * (∫ y in t, g y ∂ν) :=
by simp only [← measure.prod_restrict s t, integrable_on, integral_prod_mul]

end measure_theory
