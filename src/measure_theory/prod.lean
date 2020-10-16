/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.giry_monad
import measure_theory.set_integral

/-!
# The product measure

In this file we define and prove properties about the binary product measure. If `α` and `β` have
σ-finite measures `μ` resp. `ν` then `α × β` can be equipped with a σ-finite measure `μ.prod ν` that
satisfies `(μ.prod ν) s = ∫⁻ x, ν {y | (x, y) ∈ s} ∂μ`.
We also have `(μ.prod ν) (s.prod t) = μ s * ν t`, i.e. the measure of a rectangle is the product of
the measures of the sides.

We also prove Tonelli's theorem and Fubini's theorem.

## Main definition

* `measure_theory.measure.prod`: The product of two measures.

## Main results

* `measure_theory.measure.prod_apply` states `μ.prod ν s = ∫⁻ x, ν {y | (x, y) ∈ s} ∂μ`
  for measurable `s`. `measure_theory.measure.prod_apply_symm` is the reversed version.
* `measure_theory.measure.prod_prod` states `μ.prod ν (s.prod t) = μ s * ν t` for measurable sets
  `s` and `t`.
* `measure_theory.lintegral_prod`: Tonelli's theorem. It states that for a measurable function
  `α × β → ennreal` we have `∫⁻ z, f z ∂(μ.prod ν) = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ`. The version
  for functions `α → β → ennreal` is reversed, and called `lintegral_lintegral`. Both versions have
  a variant with `_symm` appended, where the order of integration is reversed.
  The lemma `measurable.lintegral_prod_right'` states that the inner integral of the right-hand side
  is measurable.
* `measure_theory.integrable_prod_iff` states that a binary function is integrable iff both
  * `y ↦ f (x, y)` is integrable for almost every `x`, and
  * the function `x ↦ ∫ ∥f (x, y)∥ dy` is integrable.
* `measure_theory.integral_prod`: Fubini's theorem. It states that for a integrable function
  `α × β → E` (where `E` is a second countable Banach space) we have
  `∫ z, f z ∂(μ.prod ν) = ∫ x, ∫ y, f (x, y) ∂ν ∂μ`. This theorem has the same variants as
  Tonelli's theorem. The lemma `measure_theory.integrable.integral_prod_right` states that the
  inner integral of the right-hand side is integrable.

## Implementation Notes

Many results are proven twice, once for functions in curried form (`α → β → γ`) and one for
functions in uncurried form (`α × β → γ`). The former often has an assumption
`measurable (uncurry f)`, which could be inconvenient to discharge, but for the latter it is more
common that the function has to be given explicitly, since Lean cannot synthesize the function by
itself. We name the lemmas about the uncurried form with a prime.
Tonelli's theorem and Fubini's theorem have a different naming scheme, since the version for the
uncurried version is reversed.

## Tags

product measure, Fubini's theorem, Tonelli's theorem, Fubini-Tonelli theorem
-/

section mul_zero_class
open set
variables {α β : Type*} [mul_zero_class β] {s t : set α} {f g : α → β} {a : α}

lemma indicator_mul_left (s : set α) (f g : α → β) :
  indicator s (λa, f a * g a) a = indicator s f a * g a :=
by { simp only [indicator], split_ifs, { refl }, rw [zero_mul] }

lemma indicator_mul_right (s : set α) (f g : α → β) :
  indicator s (λa, f a * g a) a = f a * indicator s g a :=
by { simp only [indicator], split_ifs, { refl }, rw [mul_zero] }

end mul_zero_class


noncomputable theory
open_locale classical topological_space
open set function real ennreal
open measure_theory measurable_space measure_theory.measure
open topological_space (hiding generate_from)
open filter (hiding prod_eq map)

variables {α β E : Type*} [measurable_space α] [measurable_space β]
variables {μ : measure α} {ν : measure β}
variables [normed_group E] [measurable_space E]

/-! ### Measurability

Before we define the product measure, we can talk about the measurability of operations on binary
functions. We show that if `f` is a binary measurable function, then the function that integrates
along one of the variables (using either the Lebesgue or Bochner integral) is measurable.
-/

/-- The product σ-algebra is generated from boxes, i.e. `s.prod t` for sets `s : set α` and
  `t : set β`. -/
lemma generate_from_prod :
  generate_from (image2 set.prod { s : set α | is_measurable s } { t : set β | is_measurable t }) =
  prod.measurable_space :=
begin
  apply le_antisymm,
  { apply generate_from_le, rintro _ ⟨s, t, hs, ht, rfl⟩, rw [prod_eq],
    exact (measurable_fst hs).inter (measurable_snd ht) },
  { refine sup_le _ _; rintro _ ⟨s, hs, rfl⟩; apply is_measurable_generate_from,
    exact ⟨s, univ, hs, is_measurable.univ, prod_univ⟩,
    exact ⟨univ, s, is_measurable.univ, hs, univ_prod⟩ }
end

/-- Boxes form a π-system. -/
lemma is_pi_system_prod :
  is_pi_system (image2 set.prod { s : set α | is_measurable s } { t : set β | is_measurable t }) :=
by { rintro _ _ ⟨s₁, t₁, hs₁, ht₁, rfl⟩ ⟨s₂, t₂, hs₂, ht₂, rfl⟩ _, rw [prod_inter_prod],
     exact mem_image2_of_mem (hs₁.inter hs₂) (ht₁.inter ht₂) }

/-- If `ν` is a finite measure, and `s ⊆ α × β` is measurable, then `x ↦ ν { y | (x, y) ∈ s }` is
  a measurable function. `measurable_measure_prod_mk_left` is strictly more general. -/
lemma measurable_measure_prod_mk_left_finite [finite_measure ν] {s : set (α × β)}
  (hs : is_measurable s) : measurable (λ x, ν (prod.mk x ⁻¹' s)) :=
begin
  refine induction_on_inter generate_from_prod.symm is_pi_system_prod _ _ _ _ hs,
  { simp [measurable_zero, const_def] },
  { rintro _ ⟨s, t, hs, ht, rfl⟩, simp only [mk_preimage_prod_right_eq_if, measure_if],
    exact measurable_const.indicator hs },
  { intros t ht h2t,
    simp_rw [preimage_compl, measure_compl (measurable_prod_mk_left ht) (measure_lt_top ν _)],
    exact measurable_const.ennreal_sub h2t },
  { intros f h1f h2f h3f, simp_rw [preimage_Union],
    have : ∀ b, ν (⋃ i, prod.mk b ⁻¹' f i) = ∑' i, ν (prod.mk b ⁻¹' f i) :=
      λ b, measure_Union (λ i j hij, disjoint.preimage _ (h1f i j hij))
        (λ i, measurable_prod_mk_left (h2f i)),
    simp_rw [this], apply measurable.ennreal_tsum h3f },
end

/-- If `ν` is a σ-finite measure, and `s ⊆ α × β` is measurable, then `x ↦ ν { y | (x, y) ∈ s }` is
  a measurable function. -/
lemma measurable_measure_prod_mk_left [sigma_finite ν] {s : set (α × β)}
  (hs : is_measurable s) : measurable (λ x, ν (prod.mk x ⁻¹' s)) :=
begin
  have : ∀ x, is_measurable (prod.mk x ⁻¹' s) := λ x, measurable_prod_mk_left hs,
  simp only [← @supr_restrict_spanning_sets _ _ ν, this],
  apply measurable_supr, intro i,
  haveI : fact _ := measure_spanning_sets_lt_top ν i,
  exact measurable_measure_prod_mk_left_finite hs
end

/-- If `μ` is a σ-finite measure, and `s ⊆ α × β` is measurable, then `y ↦ μ { x | (x, y) ∈ s }` is
  a measurable function. -/
lemma measurable_measure_prod_mk_right {μ : measure α} [sigma_finite μ] {s : set (α × β)}
  (hs : is_measurable s) : measurable (λ y, μ ((λ x, (x, y)) ⁻¹' s)) :=
measurable_measure_prod_mk_left (is_measurable_swap_iff.mpr hs)

lemma measurable.map_prod_mk_left [sigma_finite ν] : measurable (λ x : α, map (prod.mk x) ν) :=
begin
  apply measurable_of_measurable_coe, intros s hs,
  simp_rw [map_apply measurable_prod_mk_left hs],
  exact measurable_measure_prod_mk_left hs
end

lemma measurable.map_prod_mk_right {μ : measure α} [sigma_finite μ] :
  measurable (λ y : β, map (λ x : α, (x, y)) μ) :=
begin
  apply measurable_of_measurable_coe, intros s hs,
  simp_rw [map_apply measurable_prod_mk_right hs],
  exact measurable_measure_prod_mk_right hs
end

/-- The Lebesgue intergral is measurable. This shows that the integrand of (the right-hand-side of)
  Tonelli's theorem is measurable. -/
lemma measurable.lintegral_prod_right' [sigma_finite ν] :
  ∀ {f : α × β → ennreal} (hf : measurable f), measurable (λ x, ∫⁻ y, f (x, y) ∂ν) :=
begin
  have m := @measurable_prod_mk_left,
  refine measurable.ennreal_induction _ _ _,
  { intros c s hs, simp only [← indicator_comp_right],
    suffices : measurable (λ x, c * ν (prod.mk x ⁻¹' s)),
    { simpa [lintegral_indicator _ (m hs)] },
    exact measurable_const.ennreal_mul (measurable_measure_prod_mk_left hs) },
  { rintro f g - hf hg h2f h2g, simp_rw [pi.add_apply, lintegral_add (hf.comp m) (hg.comp m)],
    exact h2f.add h2g },
  { intros f hf h2f h3f,
    have := measurable_supr h3f,
    have : ∀ x, monotone (λ n y, f n (x, y)) := λ x i j hij y, h2f hij (x, y),
    simpa [lintegral_supr (λ n, (hf n).comp m), this] }
end

/-- The Lebesgue intergral is measurable. This shows that the integrand of (the right-hand-side of)
  Tonelli's theorem is measurable.
  This version has the argument `f` in curried form. -/
lemma measurable.lintegral_prod_right [sigma_finite ν] {f : α → β → ennreal}
  (hf : measurable (uncurry f)) : measurable (λ x, ∫⁻ y, f x y ∂ν) :=
hf.lintegral_prod_right'

/-- The Lebesgue intergral is measurable. This shows that the integrand of (the right-hand-side of)
  the symmetric version of Tonelli's theorem is measurable. -/
lemma measurable.lintegral_prod_left' [sigma_finite μ] {f : α × β → ennreal}
  (hf : measurable f) : measurable (λ y, ∫⁻ x, f (x, y) ∂μ) :=
(measurable_swap_iff.mpr hf).lintegral_prod_right'

/-- The Lebesgue intergral is measurable. This shows that the integrand of (the right-hand-side of)
  the symmetric version of Tonelli's theorem is measurable.
  This version has the argument `f` in curried form. -/
lemma measurable.lintegral_prod_left [sigma_finite μ] {f : α → β → ennreal}
  (hf : measurable (uncurry f)) : measurable (λ y, ∫⁻ x, f x y ∂μ) :=
hf.lintegral_prod_left'

lemma is_measurable_integrable [sigma_finite ν] [opens_measurable_space E] ⦃f : α → β → E⦄
  (hf : measurable (uncurry f)) : is_measurable { x | integrable (f x) ν } :=
begin
  simp_rw [integrable, hf.of_uncurry_left, true_and],
  exact is_measurable_lt (measurable.lintegral_prod_right hf.ennnorm) measurable_const
end

section
variables [second_countable_topology E] [normed_space ℝ E]
  [complete_space E] [borel_space E]

/-- The Bochner intergral is measurable. This shows that the integrand of (the right-hand-side of)
  Fubini's theorem is measurable.
  This version has `f` in curried form. -/
lemma measurable.integral_prod_right [sigma_finite ν] ⦃f : α → β → E⦄
  (hf : measurable (uncurry f)) : measurable (λ x, ∫ y, f x y ∂ν) :=
begin
  let s : ℕ → simple_func (α × β) E := simple_func.approx_on _ hf univ _ (mem_univ 0),
  let s' : ℕ → α → simple_func β E := λ n x, (s n).comp (prod.mk x) measurable_prod_mk_left,
  let f' : ℕ → α → E := λ n, {x | integrable (f x) ν}.indicator
    (λ x, (s' n x).integral ν),
  have hf' : ∀ n, measurable (f' n),
  { intro n, refine measurable.indicator _ (is_measurable_integrable hf),
    have : ∀ x, (s' n x).range.filter (λ x, x ≠ 0) ⊆
      (s n).range,
    { intros x, refine finset.subset.trans (finset.filter_subset _) _, intro y,
      simp_rw [simple_func.mem_range], rintro ⟨z, rfl⟩, exact ⟨(x, z), rfl⟩ },
    simp only [simple_func.integral_eq_sum_of_subset (this _)],
    refine finset.measurable_sum _ _, intro x,
    refine (measurable.to_real _).smul measurable_const,
    simp only [simple_func.coe_comp, preimage_comp] {single_pass := tt},
    apply measurable_measure_prod_mk_left,
    exact (s n).is_measurable_fiber x },
  have h2f' : tendsto f' at_top (𝓝 (λ (x : α), ∫ (y : β), f x y ∂ν)),
  { rw [tendsto_pi], intro x,
    by_cases hfx : integrable (f x) ν,
    { have : ∀ n, integrable (s' n x) ν,
      { intro n, apply (hfx.norm.add hfx.norm).mono' (s' n x).measurable,
        apply eventually_of_forall, intro y,
        simp_rw [s', simple_func.coe_comp], exact simple_func.norm_approx_on_zero_le _ _ (x, y) n },
      simp only [f', hfx, simple_func.integral_eq_integral _ (this _), indicator_of_mem,
        mem_set_of_eq],
      refine tendsto_integral_of_dominated_convergence (λ y, ∥f x y∥ + ∥f x y∥)
        (λ n, (s' n x).measurable) hf.of_uncurry_left (hfx.norm.add hfx.norm) _ _,
      { exact λ n, eventually_of_forall (λ y, simple_func.norm_approx_on_zero_le _ _ (x, y) n) },
      { exact eventually_of_forall (λ y, simple_func.tendsto_approx_on _ _ (by simp)) } },
    { simpa [f', hfx, integral_undef] using @tendsto_const_nhds _ _ _ (0 : E) _, }
     },
  exact measurable_of_tendsto_metric hf' h2f'
end

/-- The Bochner intergral is measurable. This shows that the integrand of (the right-hand-side of)
  Fubini's theorem is measurable. -/
lemma measurable.integral_prod_right' [sigma_finite ν] ⦃f : α × β → E⦄
  (hf : measurable f) : measurable (λ x, ∫ y, f (x, y) ∂ν) :=
by { rw [← uncurry_curry f] at hf, exact hf.integral_prod_right }

/-- The Bochner intergral is measurable. This shows that the integrand of (the right-hand-side of)
  the symmetric version of Fubini's theorem is measurable.
  This version has `f` in curried form. -/
lemma measurable.integral_prod_left [sigma_finite μ] ⦃f : α → β → E⦄
  (hf : measurable (uncurry f)) : measurable (λ y, ∫ x, f x y ∂μ) :=
(hf.comp measurable_swap).integral_prod_right'

/-- The Bochner intergral is measurable. This shows that the integrand of (the right-hand-side of)
  the symmetric version of Fubini's theorem is measurable. -/
lemma measurable.integral_prod_left' [sigma_finite μ] ⦃f : α × β → E⦄
  (hf : measurable f) : measurable (λ y, ∫ x, f (x, y) ∂μ) :=
(hf.comp measurable_swap).integral_prod_right'

end

/-! ### The product measure -/

namespace measure_theory

namespace measure

/-- The binary product of measures. They are defined for arbitrary measures, but we basically
  prove all properties under the assumption that at least one of them is σ-finite. -/
protected def prod (μ : measure α) (ν : measure β) : measure (α × β) :=
bind μ $ λ x : α, map (prod.mk x) ν

instance prod.measure_space {α β} [measure_space α] [measure_space β] : measure_space (α × β) :=
{ volume := volume.prod volume }

variables {μ ν} [sigma_finite ν]

lemma prod_apply {s : set (α × β)} (hs : is_measurable s) :
  μ.prod ν s = ∫⁻ x, ν (prod.mk x ⁻¹' s) ∂μ :=
by simp_rw [measure.prod, bind_apply hs measurable.map_prod_mk_left,
  map_apply measurable_prod_mk_left hs]

@[simp] lemma prod_prod {s : set α} {t : set β}
  (hs : is_measurable s) (ht : is_measurable t) : μ.prod ν (s.prod t) = μ s * ν t :=
by simp_rw [prod_apply (hs.prod ht), mk_preimage_prod_right_eq_if, measure_if,
  lintegral_indicator _ hs, lintegral_const, restrict_apply is_measurable.univ,
  univ_inter, mul_comm]

lemma ae_measure_lt_top {s : set (α × β)} (hs : is_measurable s)
  (h2s : (μ.prod ν) s < ⊤) : ∀ᵐ x ∂μ, ν (prod.mk x ⁻¹' s) < ⊤ :=
by { simp_rw [prod_apply hs] at h2s, refine ae_lt_top (measurable_measure_prod_mk_left hs) h2s }

lemma integrable_measure_prod_mk_left {s : set (α × β)}
  (hs : is_measurable s) (h2s : (μ.prod ν) s < ⊤) :
  integrable (λ x, (ν (prod.mk x ⁻¹' s)).to_real) μ :=
begin
  refine ⟨(measurable_measure_prod_mk_left hs).to_real, _⟩,
  simp_rw [has_finite_integral, ennnorm_eq_of_real to_real_nonneg],
  convert h2s using 1, simp_rw [prod_apply hs], apply lintegral_congr_ae,
  refine (ae_measure_lt_top hs h2s).mp _, apply eventually_of_forall, intros x hx,
  rw [lt_top_iff_ne_top] at hx, simp [of_real_to_real, hx],
end

/-- Note: the assumption `hs` cannot be dropped. For a counterexample, see
  Walter Rudin *Real and Complex Analysis*, example (c) in section 8.9. -/
lemma measure_prod_null {s : set (α × β)}
  (hs : is_measurable s) : μ.prod ν s = 0 ↔ (λ x, ν (prod.mk x ⁻¹' s)) =ᵐ[μ] 0 :=
by simp_rw [prod_apply hs, lintegral_eq_zero_iff (measurable_measure_prod_mk_left hs)]

/-- Note: the converse is not true without assuming that `s` is measurable. For a counterexample,
  see Walter Rudin *Real and Complex Analysis*, example (c) in section 8.9. -/
lemma measure_ae_null_of_prod_null {s : set (α × β)}
  (h : μ.prod ν s = 0) : (λ x, ν (prod.mk x ⁻¹' s)) =ᵐ[μ] 0 :=
begin
  obtain ⟨t, hst, mt, ht⟩ := exists_is_measurable_superset_of_measure_eq_zero h,
  simp_rw [measure_prod_null mt] at ht,
  rw [eventually_le_antisymm_iff],
  exact ⟨eventually_le.trans_eq
    (eventually_of_forall $ λ x, (measure_mono (preimage_mono hst) : _)) ht,
    eventually_of_forall $ λ x, zero_le _⟩
end

/-- Note: the converse is not true. For a counterexample, see
  Walter Rudin *Real and Complex Analysis*, example (c) in section 8.9. -/
lemma ae_ae_of_ae_prod {p : α × β → Prop} (h : ∀ᵐ z ∂μ.prod ν, p z) :
  ∀ᵐ x ∂ μ, ∀ᵐ y ∂ ν, p (x, y) :=
measure_ae_null_of_prod_null h

variables [sigma_finite μ]

instance prod.sigma_finite : sigma_finite (μ.prod ν) :=
⟨⟨λ n, (spanning_sets μ n).prod (spanning_sets ν n),
  λ n, (is_measurable_spanning_sets μ n).prod (is_measurable_spanning_sets ν n),
  λ n, by { simp_rw [prod_prod (is_measurable_spanning_sets μ n) (is_measurable_spanning_sets ν n)],
    exact mul_lt_top (measure_spanning_sets_lt_top μ n) (measure_spanning_sets_lt_top ν n) },
  by { simp_rw [Union_prod_of_monotone (monotone_spanning_sets μ) (monotone_spanning_sets ν),
    Union_spanning_sets, univ_prod_univ] }⟩⟩

/- Note: This proof would be shorter if `sigma_finite` was not `Prop`-valued, since we use that
  the sets given in the instance of `sigma_finite` is a π-system. -/
/-- Measures on a product space are equal if they are equal on rectangles. -/
lemma prod_unique {μν₁ μν₂ : measure (α × β)}
  (h₁ : ∀ s t, is_measurable s → is_measurable t → μν₁ (s.prod t) = μ s * ν t)
  (h₂ : ∀ s t, is_measurable s → is_measurable t → μν₂ (s.prod t) = μ s * ν t) : μν₁ = μν₂ :=
begin
  refine ext_of_generate_from_of_Union _
    (λ i, (spanning_sets μ i).prod (spanning_sets ν i))
    generate_from_prod.symm is_pi_system_prod _ _ _ _,
  { rw [Union_prod_of_monotone (monotone_spanning_sets μ) (monotone_spanning_sets ν)],
    simp_rw [Union_spanning_sets, univ_prod_univ] },
  { intro i, apply mem_image2_of_mem; apply is_measurable_spanning_sets },
  { intro i, rw [h₁], apply mul_lt_top; apply measure_spanning_sets_lt_top,
    all_goals { apply is_measurable_spanning_sets } },
  { rintro _ ⟨s, t, hs, ht, rfl⟩, simp * at * }
end

lemma prod_eq {μν : measure (α × β)}
  (h : ∀ s t, is_measurable s → is_measurable t → μν (s.prod t) = μ s * ν t) : μ.prod ν = μν :=
prod_unique (λ s t hs ht, prod_prod hs ht) h

lemma prod_swap : map prod.swap (μ.prod ν) = ν.prod μ :=
begin
  refine (prod_eq _).symm,
  intros s t hs ht,
  simp_rw [map_apply measurable_swap (hs.prod ht), preimage_swap_prod, prod_prod ht hs, mul_comm]
end

lemma prod_apply_symm {s : set (α × β)} (hs : is_measurable s) :
  μ.prod ν s = ∫⁻ y, μ ((λ x, (x, y)) ⁻¹' s) ∂ν :=
by { rw [← prod_swap, map_apply measurable_swap hs],
     simp only [prod_apply (measurable_swap hs)], refl }

/-! ### The product of specific measures -/

lemma prod_restrict {s : set α} {t : set β} (hs : is_measurable s) (ht : is_measurable t) :
  (μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s.prod t) :=
begin
  refine prod_eq (λ s' t' hs' ht', _),
  simp_rw [restrict_apply (hs'.prod ht'), prod_inter_prod, prod_prod (hs'.inter hs) (ht'.inter ht),
    restrict_apply hs', restrict_apply ht']
end

lemma prod_dirac (y : β) : μ.prod (dirac y) = map (λ x, (x, y)) μ :=
begin
  refine prod_eq (λ s t hs ht, _),
  simp_rw [map_apply measurable_prod_mk_right (hs.prod ht), mk_preimage_prod_left_eq_if, measure_if,
    dirac_apply _ ht, ← indicator_mul_right _ (λ x, μ s), pi.one_apply, mul_one]
end

lemma dirac_prod (x : α) : (dirac x).prod ν = map (prod.mk x) ν :=
begin
  refine prod_eq (λ s t hs ht, _),
  simp_rw [map_apply measurable_prod_mk_left (hs.prod ht), mk_preimage_prod_right_eq_if, measure_if,
    dirac_apply _ hs, ← indicator_mul_left _ _ (λ x, μ s), pi.one_apply, mul_one]
end

lemma dirac_prod_dirac {x : α} {y : β} : (dirac x).prod (dirac y) = dirac (x, y) :=
by rw [prod_dirac, map_dirac measurable_prod_mk_right]

lemma prod_sum {ι : Type*} [fintype ι] (ν : ι → measure β) [∀ i, sigma_finite (ν i)] :
  μ.prod (sum ν) = sum (λ i, μ.prod (ν i)) :=
begin
  refine prod_eq (λ s t hs ht, _),
  simp_rw [sum_apply _ (hs.prod ht), sum_apply _ ht, prod_prod hs ht, tsum_fintype, finset.mul_sum]
end

lemma sum_prod {ι : Type*} [fintype ι] (μ : ι → measure α) [∀ i, sigma_finite (μ i)] :
  (sum μ).prod ν = sum (λ i, (μ i).prod ν) :=
begin
  refine prod_eq (λ s t hs ht, _),
  simp_rw [sum_apply _ (hs.prod ht), sum_apply _ hs, prod_prod hs ht, tsum_fintype, finset.sum_mul]
end

lemma prod_add (ν' : measure β) [sigma_finite ν'] : μ.prod (ν + ν') = μ.prod ν + μ.prod ν' :=
by { refine prod_eq (λ s t hs ht, _), simp_rw [add_apply, prod_prod hs ht, left_distrib] }

lemma add_prod (μ' : measure α) [sigma_finite μ'] : (μ + μ').prod ν = μ.prod ν + μ'.prod ν :=
by { refine prod_eq (λ s t hs ht, _), simp_rw [add_apply, prod_prod hs ht, right_distrib] }

end measure

open measure_theory.measure

/-! ### The Lebesgue integral on a product -/

variables [sigma_finite ν]

lemma lintegral_prod_swap [sigma_finite μ] (f : α × β → ennreal)
  (hf : measurable f) : ∫⁻ z, f z.swap ∂(ν.prod μ) = ∫⁻ z, f z ∂(μ.prod ν) :=
by rw [← lintegral_map hf measurable_swap, prod_swap]

/-- Tonelli's Theorem: For `ennreal`-valued measurable functions on `α × β`,
  the integral of `f` is equal to the iterated integral. -/
lemma lintegral_prod :
  ∀ (f : α × β → ennreal) (hf : measurable f), ∫⁻ z, f z ∂(μ.prod ν) = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ :=
begin
  have m := @measurable_prod_mk_left,
  refine measurable.ennreal_induction _ _ _,
  { intros c s hs, simp only [← indicator_comp_right],
    simp [lintegral_indicator, m hs, hs, lintegral_const_mul, measurable_measure_prod_mk_left hs,
      prod_apply] },
  { rintro f g - hf hg h2f h2g,
    simp [lintegral_add, measurable.lintegral_prod_right', hf.comp m, hg.comp m,
      hf, hg, h2f, h2g] },
  { intros f hf h2f h3f,
    have kf : ∀ x n, measurable (λ y, f n (x, y)) := λ x n, (hf n).comp m,
    have k2f : ∀ x, monotone (λ n y, f n (x, y)) := λ x i j hij y, h2f hij (x, y),
    have lf : ∀ n, measurable (λ x, ∫⁻ y, f n (x, y) ∂ν) := λ n, (hf n).lintegral_prod_right',
    have l2f : monotone (λ n x, ∫⁻ y, f n (x, y) ∂ν) := λ i j hij x, lintegral_mono (k2f x hij),
    simp only [lintegral_supr hf h2f, lintegral_supr (kf _), k2f, lintegral_supr lf l2f, h3f] },
end

/-- The symmetric verion of Tonelli's Theorem: For `ennreal`-valued measurable functions on `α × β`,
  the integral of `f` is equal to the iterated integral, in reverse order. -/
lemma lintegral_prod_symm [sigma_finite μ] (f : α × β → ennreal)
  (hf : measurable f) : ∫⁻ z, f z ∂(μ.prod ν) = ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν :=
by { simp_rw [← lintegral_prod_swap f hf], exact lintegral_prod _ (hf.comp measurable_swap) }

/-- The reversed version of Tonelli's Theorem. In this version `f` is in curried form, which makes
  it easier for the elaborator to figure out `f` automatically. -/
lemma lintegral_lintegral ⦃f : α → β → ennreal⦄
  (hf : measurable (uncurry f)) :
  ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ z, f z.1 z.2 ∂(μ.prod ν) :=
(lintegral_prod _ hf).symm

/-- The reversed version of Tonelli's Theorem (symmetric version). In this version `f` is in curried
  form, which makes it easier for the elaborator to figure out `f` automatically. -/
lemma lintegral_lintegral_symm [sigma_finite μ] ⦃f : α → β → ennreal⦄
  (hf : measurable (uncurry f)) :
  ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ z, f z.2 z.1 ∂(ν.prod μ) :=
(lintegral_prod_symm _ (hf.comp measurable_swap)).symm

/-- Change the order of Lebesgue integration. -/
lemma lintegral_lintegral_swap [sigma_finite μ] ⦃f : α → β → ennreal⦄
  (hf : measurable (uncurry f)) :
  ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ y, ∫⁻ x, f x y ∂μ ∂ν :=
(lintegral_lintegral hf).trans (lintegral_prod_symm _ hf)

/-! ### Integrability on a product -/
section

variables [opens_measurable_space E]

lemma integrable.swap [sigma_finite μ] ⦃f : α × β → E⦄
  (hf : integrable f (μ.prod ν)) : integrable (f ∘ prod.swap) (ν.prod μ) :=
⟨hf.measurable.comp measurable_swap,
  (lintegral_prod_swap _ hf.measurable.ennnorm : _).le.trans_lt hf.has_finite_integral⟩

lemma integrable_swap_iff [sigma_finite μ] ⦃f : α × β → E⦄ :
  integrable (f ∘ prod.swap) (ν.prod μ) ↔ integrable f (μ.prod ν) :=
⟨λ hf, by { convert hf.swap, ext ⟨x, y⟩, refl }, λ hf, hf.swap⟩

lemma has_finite_integral_prod_iff ⦃f : α × β → E⦄ (h1f : measurable f) :
  (∀ᵐ x ∂ μ, has_finite_integral (λ y, f (x, y)) ν) ∧
    has_finite_integral (λ x, ∫ y, ∥f (x, y)∥ ∂ν) μ ↔ has_finite_integral f (μ.prod ν) :=
begin
  simp only [has_finite_integral, lintegral_prod _ h1f.ennnorm],
  have : ∀ x, ∀ᵐ y ∂ν, 0 ≤ ∥f (x, y)∥ := λ x, eventually_of_forall (λ y, norm_nonneg _),
  simp_rw [integral_eq_lintegral_of_nonneg_ae (this _) (h1f.norm.comp measurable_prod_mk_left),
    ennnorm_eq_of_real to_real_nonneg, of_real_norm_eq_coe_nnnorm],
  -- this fact is probably too specialized to be its own lemma
  have : ∀ {p q r : Prop} (h1 : r → p), (p ∧ q ↔ r) ↔ (p → (q ↔ r)) :=
  λ p q r h1, by rw [← and.congr_right_iff, and_iff_right_of_imp h1],
  rw [this],
  { intro h2f, rw lintegral_congr_ae,
    refine h2f.mp _, apply eventually_of_forall, intros x hx, dsimp only,
    rw [of_real_to_real], rw [← lt_top_iff_ne_top], exact hx },
  { intro h2f, refine ae_lt_top _ h2f, exact h1f.ennnorm.lintegral_prod_right' },
end

/-- A binary function is integrable if the function `y ↦ f (x, y)` is integrable for almost every
  `x` and the function `x ↦ ∫ ∥f (x, y)∥ dy` is integrable. -/
lemma integrable_prod_iff ⦃f : α × β → E⦄ (h1f : measurable f) :
  (∀ᵐ x ∂ μ, integrable (λ y, f (x, y)) ν) ∧ integrable (λ x, ∫ y, ∥f (x, y)∥ ∂ν) μ ↔
  integrable f (μ.prod ν) :=
by simp only [integrable, h1f, h1f.comp measurable_prod_mk_left, h1f.norm.integral_prod_right',
  true_and, has_finite_integral_prod_iff]

/-- A binary function is integrable if the function `x ↦ f (x, y)` is integrable for almost every
  `y` and the function `y ↦ ∫ ∥f (x, y)∥ dx` is integrable. -/
lemma integrable_prod_iff' [sigma_finite μ] ⦃f : α × β → E⦄ (h1f : measurable f) :
  (∀ᵐ y ∂ ν, integrable (λ x, f (x, y)) μ) ∧ integrable (λ y, ∫ x, ∥f (x, y)∥ ∂μ) ν ↔
  integrable f (μ.prod ν) :=
by { convert integrable_prod_iff (h1f.comp measurable_swap) using 1, rw [integrable_swap_iff],
  apply_instance }

lemma integrable.prod_left_ae [sigma_finite μ] ⦃f : α × β → E⦄
  (hf : integrable f (μ.prod ν)) : ∀ᵐ y ∂ ν, integrable (λ x, f (x, y)) μ :=
((integrable_prod_iff' hf.measurable).mpr hf).1

lemma integrable.prod_right_ae [sigma_finite μ] ⦃f : α × β → E⦄
  (hf : integrable f (μ.prod ν)) : ∀ᵐ x ∂ μ, integrable (λ y, f (x, y)) ν :=
hf.swap.prod_left_ae

lemma integrable.integral_norm_prod_left ⦃f : α × β → E⦄
  (hf : integrable f (μ.prod ν)) : integrable (λ x, ∫ y, ∥f (x, y)∥ ∂ν) μ :=
((integrable_prod_iff hf.measurable).mpr hf).2

lemma integrable.integral_norm_prod_right [sigma_finite μ] ⦃f : α × β → E⦄
  (hf : integrable f (μ.prod ν)) : integrable (λ y, ∫ x, ∥f (x, y)∥ ∂μ) ν :=
hf.swap.integral_norm_prod_left

end

variables [second_countable_topology E] [normed_space ℝ E]
  [complete_space E] [borel_space E]

lemma integrable.integral_prod_left ⦃f : α × β → E⦄
  (hf : integrable f (μ.prod ν)) : integrable (λ x, ∫ y, f (x, y) ∂ν) μ :=
integrable.mono hf.integral_norm_prod_left hf.measurable.integral_prod_right' $
  eventually_of_forall $ λ x, (norm_integral_le_integral_norm _).trans_eq $
  (norm_of_nonneg $ integral_nonneg_of_ae $ eventually_of_forall $ λ y, (norm_nonneg _ : _)).symm

lemma integrable.integral_prod_right [sigma_finite μ] ⦃f : α × β → E⦄
  (hf : integrable f (μ.prod ν)) : integrable (λ y, ∫ x, f (x, y) ∂μ) ν :=
hf.swap.integral_prod_left

/-! ### The Bochner integral on a product -/

variables [sigma_finite μ]

lemma integral_prod_swap (f : α × β → E)
  (hf : measurable f) : ∫ z, f z.swap ∂(ν.prod μ) = ∫ z, f z ∂(μ.prod ν) :=
by rw [← integral_map measurable_swap hf, prod_swap]

variables {E' : Type*} [measurable_space E'] [normed_group E'] [borel_space E'] [complete_space E']
  [normed_space ℝ E'] [second_countable_topology E']

/-! Some rules about the sum/difference of double integrals. They follow from `integral_add`, but
  we separate them out as separate lemmas, because they involve quite some steps. -/

/-- Integrals commute with addition inside another integral. `F` can be any measurable function. -/
lemma integral_fn_integral_add ⦃f g : α × β → E⦄
  {F : E → E'} (hF : measurable F)
  (hf : integrable f (μ.prod ν))
  (hg : integrable g (μ.prod ν)) :
  ∫ x, F (∫ y, f (x, y) + g (x, y) ∂ν) ∂μ = ∫ x, F (∫ y, f (x, y) ∂ν + ∫ y, g (x, y) ∂ν) ∂μ :=
begin
  refine integral_congr_ae
    (hF.comp (hf.add hg).measurable.integral_prod_right')
    (hF.comp (hf.measurable.integral_prod_right'.add hg.measurable.integral_prod_right')) _,
  filter_upwards [hf.prod_right_ae, hg.prod_right_ae], dsimp only [mem_set_of_eq],
  intros x h2f h2g, simp [integral_add h2f h2g],
end

/-- Integrals commute with subtraction inside another integral.
  `F` can be any measurable function. -/
lemma integral_fn_integral_sub ⦃f g : α × β → E⦄
  {F : E → E'} (hF : measurable F)
  (hf : integrable f (μ.prod ν))
  (hg : integrable g (μ.prod ν)) :
  ∫ x, F (∫ y, f (x, y) - g (x, y) ∂ν) ∂μ = ∫ x, F (∫ y, f (x, y) ∂ν - ∫ y, g (x, y) ∂ν) ∂μ :=
begin
  refine integral_congr_ae
    (hF.comp (hf.sub hg).measurable.integral_prod_right')
    (hF.comp (hf.measurable.integral_prod_right'.sub hg.measurable.integral_prod_right')) _,
  filter_upwards [hf.prod_right_ae, hg.prod_right_ae], dsimp only [mem_set_of_eq],
  intros x h2f h2g, simp [integral_sub h2f h2g]
end

/-- Integrals commute with subtraction inside a lower Lebesgue integral.
  `F` can be any function. -/
lemma lintegral_fn_integral_sub ⦃f g : α × β → E⦄
  (F : E → ennreal) (hf : integrable f (μ.prod ν)) (hg : integrable g (μ.prod ν)) :
  ∫⁻ x, F (∫ y, f (x, y) - g (x, y) ∂ν) ∂μ = ∫⁻ x, F (∫ y, f (x, y) ∂ν - ∫ y, g (x, y) ∂ν) ∂μ :=
begin
  refine lintegral_congr_ae _,
  filter_upwards [hf.prod_right_ae, hg.prod_right_ae], dsimp only [mem_set_of_eq],
  intros x h2f h2g, simp [integral_sub h2f h2g]
end

/-- Double integrals commute with addition. -/
lemma integral_integral_add ⦃f g : α × β → E⦄
  (hf : integrable f (μ.prod ν))
  (hg : integrable g (μ.prod ν)) :
  ∫ x, ∫ y, f (x, y) + g (x, y) ∂ν ∂μ = ∫ x, ∫ y, f (x, y) ∂ν ∂μ + ∫ x, ∫ y, g (x, y) ∂ν ∂μ :=
(integral_fn_integral_add measurable_id hf hg).trans $
  integral_add hf.integral_prod_left hg.integral_prod_left

/-- Double integrals commute with addition. This is the version with `(f + g) (x, y)`
  (instead of `f (x, y) + g (x, y)`) in the LHS. -/
lemma integral_integral_add' ⦃f g : α × β → E⦄
  (hf : integrable f (μ.prod ν))
  (hg : integrable g (μ.prod ν)) :
  ∫ x, ∫ y, (f + g) (x, y) ∂ν ∂μ = ∫ x, ∫ y, f (x, y) ∂ν ∂μ + ∫ x, ∫ y, g (x, y) ∂ν ∂μ :=
integral_integral_add hf hg

/-- Double integrals commute with subtraction. -/
lemma integral_integral_sub ⦃f g : α × β → E⦄
  (hf : integrable f (μ.prod ν))
  (hg : integrable g (μ.prod ν)) :
  ∫ x, ∫ y, f (x, y) - g (x, y) ∂ν ∂μ = ∫ x, ∫ y, f (x, y) ∂ν ∂μ - ∫ x, ∫ y, g (x, y) ∂ν ∂μ :=
(integral_fn_integral_sub measurable_id hf hg).trans $
  integral_sub hf.integral_prod_left hg.integral_prod_left

/-- Double integrals commute with subtraction. This is the version with `(f - g) (x, y)`
  (instead of `f (x, y) - g (x, y)`) in the LHS. -/
lemma integral_integral_sub' ⦃f g : α × β → E⦄
  (hf : integrable f (μ.prod ν))
  (hg : integrable g (μ.prod ν)) :
  ∫ x, ∫ y, (f - g) (x, y) ∂ν ∂μ = ∫ x, ∫ y, f (x, y) ∂ν ∂μ - ∫ x, ∫ y, g (x, y) ∂ν ∂μ :=
integral_integral_sub hf hg

/-- The map that sends an L¹-function `f : α × β → E` to `∫∫f` is continuous. -/
lemma continuous_integral_integral :
  continuous (λ (f : α × β →₁[μ.prod ν] E), ∫ x, ∫ y, f (x, y) ∂ν ∂μ) :=
begin
  rw [continuous_iff_continuous_at], intro g,
  refine tendsto_integral_of_l1 _ g.integrable.integral_prod_left
    (eventually_of_forall $ λ h, h.integrable.integral_prod_left) _,
  simp_rw [edist_eq_coe_nnnorm_sub,
    ← lintegral_fn_integral_sub (λ x, (nnnorm x : ennreal)) (l1.integrable _) g.integrable],
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _ (λ i, zero_le _) _,
  { exact λ i, ∫⁻ x, ∫⁻ y, nnnorm (i (x, y) - g (x, y)) ∂ν ∂μ },
  swap, { exact λ i, lintegral_mono (λ x, ennnorm_integral_le_lintegral_ennnorm _) },
  show tendsto (λ (i : α × β →₁[μ.prod ν] E),
    ∫⁻ x, ∫⁻ (y : β), nnnorm (i (x, y) - g (x, y)) ∂ν ∂μ) (𝓝 g) (𝓝 0),
  have : ∀ (i : α × β →₁[μ.prod ν] E), measurable (λ z, (nnnorm (i z - g z) : ennreal)) :=
  λ i, (i.measurable.sub g.measurable).ennnorm,
  simp_rw [← lintegral_prod _ (this _), ← l1.of_real_norm_sub_eq_lintegral, ← of_real_zero],
  refine (continuous_of_real.tendsto 0).comp _,
  rw [← tendsto_iff_norm_tendsto_zero], exact tendsto_id
end

/-- Fubini's Theorem: For integrable functions on `α × β`,
  the Bochner integral of `f` is equal to the iterated Bochner integral.
  `integrable_prod_iff` can be useful to show that the function in question in integrable.
  `measure_theory.integrable.integral_prod_right` is useful to show that the inner integral
  of the right-hand side is integrable. -/
lemma integral_prod : ∀ (f : α × β → E) (hf : integrable f (μ.prod ν)),
  ∫ z, f z ∂(μ.prod ν) = ∫ x, ∫ y, f (x, y) ∂ν ∂μ :=
begin
  apply integrable.induction,
  { intros c s hs h2s, simp_rw [integral_indicator measurable_const hs, ← indicator_comp_right,
      function.comp, integral_indicator measurable_const (measurable_prod_mk_left hs),
      set_integral_const, integral_smul_const,
      integral_to_real (measurable_measure_prod_mk_left hs) (ae_measure_lt_top hs h2s),
      prod_apply hs] },
  { intros f g hfg i_f i_g hf hg,
    simp_rw [integral_add' i_f i_g, integral_integral_add' i_f i_g, hf, hg] },
  { exact is_closed_eq continuous_integral continuous_integral_integral },
  { intros f g hfg i_f m_g hf, convert hf using 1,
    { exact integral_congr_ae m_g i_f.measurable hfg.symm },
    { refine integral_congr_ae m_g.integral_prod_right' i_f.measurable.integral_prod_right' _,
      rw [eventually_eq] at hfg, refine (ae_ae_of_ae_prod hfg).mp _,
      apply eventually_of_forall, intros x hfgx,
      refine integral_congr_ae (m_g.comp measurable_prod_mk_left)
        (i_f.measurable.comp measurable_prod_mk_left) (ae_eq_symm hfgx) } }
end

/-- Symmetric version of Fubini's Theorem: For integrable functions on `α × β`,
  the Bochner integral of `f` is equal to the iterated Bochner integral.
  This version has the integrals on the right-hand side in the other order. -/
lemma integral_prod_symm (f : α × β → E) (hf : integrable f (μ.prod ν)) :
  ∫ z, f z ∂(μ.prod ν) = ∫ y, ∫ x, f (x, y) ∂μ ∂ν :=
by { simp_rw [← integral_prod_swap f hf.measurable], exact integral_prod _ hf.swap }

/-- Reversed version of Fubini's Theorem. -/
lemma integral_integral {f : α → β → E} (hf : integrable (uncurry f) (μ.prod ν)) :
  ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ z, f z.1 z.2 ∂(μ.prod ν) :=
(integral_prod _ hf).symm

/-- Reversed version of Fubini's Theorem (symmetric version). -/
lemma integral_integral_symm {f : α → β → E} (hf : integrable (uncurry f) (μ.prod ν)) :
  ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ z, f z.2 z.1 ∂(ν.prod μ) :=
(integral_prod_symm _ hf.swap).symm

/-- Change the order of Bochner integration. -/
lemma integral_integral_swap ⦃f : α → β → E⦄ (hf : integrable (uncurry f) (μ.prod ν)) :
  ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ y, ∫ x, f x y ∂μ ∂ν :=
(integral_integral hf).trans (integral_prod_symm _ hf)

end measure_theory
