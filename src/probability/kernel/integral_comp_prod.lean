/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import probability.kernel.composition
import measure_theory.integral.set_integral

/-!
# Bochner integral of a function against the composition-product of two kernels

We prove properties of the composition-product of two kernels. If `κ` is an s-finite kernel from
`α` to `β` and `η` is an s-finite kernel from `α × β` to `γ`, we can form their composition-product
`κ ⊗ₖ η : kernel α (β × γ)`. We proved in `probability.kernel.lintegral_comp_prod` that it verifies
`∫⁻ bc, f bc ∂((κ ⊗ₖ η) a) = ∫⁻ b, ∫⁻ c, f (b, c) ∂(η (a, b)) ∂(κ a)`. In this file, we prove the
same equality for the Bochner integral.

## Main statements

* `probability_theory.integral_comp_prod`: the integral against the composition-product is
  `∫ z, f z ∂((κ ⊗ₖ η) a) = ∫ x, ∫ y, f (x, y) ∂(η (a, x)) ∂(κ a)`

## Implementation details

This file is to a large extent a copy of part of `measure_theory.constructions.prod`. The product of
two measures is a particular case of composition-product of kernels and it turns out that once the
measurablity of the Lebesgue integral of a kernel is proved, almost all proofs about integrals
against products of measures extend with minimal modifications to the composition-product of two
kernels.
-/

noncomputable theory
open_locale topology ennreal measure_theory probability_theory
open set function real ennreal measure_theory filter probability_theory probability_theory.kernel

variables {α β γ E : Type*}
  {mα : measurable_space α} {mβ : measurable_space β} {mγ : measurable_space γ}
  [normed_add_comm_group E]
  {κ : kernel α β} [is_s_finite_kernel κ]
  {η : kernel (α × β) γ} [is_s_finite_kernel η]
  {a : α}

namespace probability_theory

lemma has_finite_integral_prod_mk_left (a : α) {s : set (β × γ)} (h2s : (κ ⊗ₖ η) a s ≠ ∞) :
  has_finite_integral (λ b, (η (a, b) (prod.mk b ⁻¹' s)).to_real) (κ a) :=
begin
  let t := to_measurable ((κ ⊗ₖ η) a) s,
  simp_rw [has_finite_integral, ennnorm_eq_of_real to_real_nonneg],
  calc ∫⁻ b, ennreal.of_real (η (a, b) (prod.mk b ⁻¹' s)).to_real ∂(κ a)
      ≤ ∫⁻ b, η (a, b) (prod.mk b ⁻¹' t) ∂(κ a) :
      begin
        refine lintegral_mono_ae _,
        filter_upwards [ae_kernel_lt_top a h2s] with b hb,
        rw of_real_to_real hb.ne,
        exact measure_mono (preimage_mono (subset_to_measurable _ _)),
      end
  ... ≤ (κ ⊗ₖ η) a t : le_comp_prod_apply _ _ _ _
  ... = (κ ⊗ₖ η) a s : measure_to_measurable s
  ... < ⊤ : h2s.lt_top,
end

lemma integrable_kernel_prod_mk_left (a : α)
  {s : set (β × γ)} (hs : measurable_set s) (h2s : (κ ⊗ₖ η) a s ≠ ∞) :
  integrable (λ b, (η (a, b) (prod.mk b ⁻¹' s)).to_real) (κ a) :=
begin
  split,
  { exact (measurable_kernel_prod_mk_left' hs a).ennreal_to_real.ae_strongly_measurable },
  { exact has_finite_integral_prod_mk_left a h2s, },
end

lemma _root_.measure_theory.ae_strongly_measurable.integral_kernel_prod_right'
  [normed_space ℝ E] [complete_space E]
  ⦃f : β × γ → E⦄ (hf : ae_strongly_measurable f ((κ ⊗ₖ η) a)) :
  ae_strongly_measurable (λ x, ∫ y, f (x, y) ∂(η (a, x))) (κ a) :=
⟨λ x, ∫ y, hf.mk f (x, y) ∂(η (a, x)), hf.strongly_measurable_mk.integral_kernel_prod_right'',
  by { filter_upwards [ae_ae_of_ae_comp_prod hf.ae_eq_mk] with _ hx using integral_congr_ae hx }⟩

lemma _root_.measure_theory.ae_strongly_measurable.comp_prod_mk_left
  {δ : Type*} [topological_space δ] {f : β × γ → δ}
  (hf : ae_strongly_measurable f ((κ ⊗ₖ η) a)) :
  ∀ᵐ x ∂(κ a), ae_strongly_measurable (λ y, f (x, y)) (η (a, x)) :=
by filter_upwards [ae_ae_of_ae_comp_prod hf.ae_eq_mk] with x hx using
  ⟨λ y, hf.mk f (x, y), hf.strongly_measurable_mk.comp_measurable measurable_prod_mk_left, hx⟩

/-! ### Integrability -/

lemma has_finite_integral_comp_prod_iff ⦃f : β × γ → E⦄ (h1f : strongly_measurable f) :
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
  have : ∀ {p q r : Prop} (h1 : r → p), (r ↔ p ∧ q) ↔ (p → (r ↔ q)) :=
  λ p q r h1, by rw [← and.congr_right_iff, and_iff_right_of_imp h1],
  rw [this],
  { intro h2f, rw lintegral_congr_ae,
    refine h2f.mp _, apply eventually_of_forall, intros x hx, dsimp only,
    rw [of_real_to_real], rw [← lt_top_iff_ne_top], exact hx },
  { intro h2f, refine ae_lt_top _ h2f.ne, exact h1f.ennnorm.lintegral_kernel_prod_right'' },
end

lemma has_finite_integral_comp_prod_iff' ⦃f : β × γ → E⦄
  (h1f : ae_strongly_measurable f ((κ ⊗ₖ η) a)) :
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

lemma integrable_comp_prod_iff ⦃f : β × γ → E⦄ (hf : ae_strongly_measurable f ((κ ⊗ₖ η) a)) :
  integrable f ((κ ⊗ₖ η) a) ↔
    (∀ᵐ x ∂(κ a), integrable (λ y, f (x, y)) (η (a, x)))
    ∧ integrable (λ x, ∫ y, ‖f (x, y)‖ ∂(η (a, x))) (κ a) :=
by simp only [integrable, has_finite_integral_comp_prod_iff' hf,
  hf.norm.integral_kernel_prod_right', hf, hf.comp_prod_mk_left, eventually_and, true_and]

lemma _root_.measure_theory.integrable.comp_prod_right_ae
  ⦃f : β × γ → E⦄ (hf : integrable f ((κ ⊗ₖ η) a)) :
  ∀ᵐ x ∂(κ a), integrable (λ y, f (x, y)) (η (a, x)) :=
((integrable_comp_prod_iff hf.ae_strongly_measurable).mp hf).1

lemma _root_.measure_theory.integrable.integral_norm_comp_prod_left
  ⦃f : β × γ → E⦄ (hf : integrable f ((κ ⊗ₖ η) a)) :
  integrable (λ x, ∫ y, ‖f (x, y)‖ ∂(η (a, x))) (κ a) :=
((integrable_comp_prod_iff hf.ae_strongly_measurable).mp hf).2

lemma _root_.measure_theory.integrable.integral_comp_prod_left [normed_space ℝ E] [complete_space E]
  ⦃f : β × γ → E⦄ (hf : integrable f ((κ ⊗ₖ η) a)) :
  integrable (λ x, ∫ y, f (x, y) ∂(η (a, x))) (κ a) :=
integrable.mono hf.integral_norm_comp_prod_left
  hf.ae_strongly_measurable.integral_kernel_prod_right' $
  eventually_of_forall $ λ x, (norm_integral_le_integral_norm _).trans_eq $
  (norm_of_nonneg $ integral_nonneg_of_ae $ eventually_of_forall $
  λ y, (norm_nonneg (f (x, y)) : _)).symm

/-! ### Bochner integral -/

variables [normed_space ℝ E] [complete_space E]
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
  rw [← tendsto_iff_norm_tendsto_zero],
  exact tendsto_id
end

lemma integral_comp_prod : ∀ {f : β × γ → E} (hf : integrable f ((κ ⊗ₖ η) a)),
  ∫ z, f z ∂((κ ⊗ₖ η) a) = ∫ x, ∫ y, f (x, y) ∂(η (a, x)) ∂(κ a) :=
begin
  apply integrable.induction,
  { intros c s hs h2s,
    simp_rw [integral_indicator hs, ← indicator_comp_right,
      function.comp, integral_indicator (measurable_prod_mk_left hs),
      measure_theory.set_integral_const, integral_smul_const],
    congr' 1,
    rw integral_to_real,
    rotate,
    { exact (kernel.measurable_kernel_prod_mk_left' hs _).ae_measurable, },
    { exact (ae_kernel_lt_top a h2s.ne), },
    rw kernel.comp_prod_apply _ _ _ hs,
    refl, },
  { intros f g hfg i_f i_g hf hg,
    simp_rw [integral_add' i_f i_g, kernel.integral_integral_add' i_f i_g, hf, hg] },
  { exact is_closed_eq continuous_integral kernel.continuous_integral_integral },
  { intros f g hfg i_f hf,
    convert hf using 1,
    { exact integral_congr_ae hfg.symm },
    { refine integral_congr_ae _,
      refine (ae_ae_of_ae_comp_prod hfg).mp (eventually_of_forall _),
      exact λ x hfgx, integral_congr_ae (ae_eq_symm hfgx) } }
end

lemma set_integral_comp_prod {f : β × γ → E} {s : set β} {t : set γ}
  (hs : measurable_set s) (ht : measurable_set t) (hf : integrable_on f (s ×ˢ t) ((κ ⊗ₖ η) a)) :
  ∫ z in s ×ˢ t, f z ∂((κ ⊗ₖ η) a) = ∫ x in s, ∫ y in t, f (x, y) ∂(η (a, x)) ∂(κ a) :=
begin
  rw [← kernel.restrict_apply (κ ⊗ₖ η) (hs.prod ht), ← comp_prod_restrict, integral_comp_prod],
  { simp_rw kernel.restrict_apply, },
  { rw [comp_prod_restrict, kernel.restrict_apply], exact hf, },
end

lemma set_integral_comp_prod_univ_right (f : β × γ → E) {s : set β}
  (hs : measurable_set s) (hf : integrable_on f (s ×ˢ univ) ((κ ⊗ₖ η) a)) :
  ∫ z in s ×ˢ univ, f z ∂((κ ⊗ₖ η) a) = ∫ x in s, ∫ y, f (x, y) ∂(η (a, x)) ∂(κ a) :=
by simp_rw [set_integral_comp_prod hs measurable_set.univ hf, measure.restrict_univ]

lemma set_integral_comp_prod_univ_left (f : β × γ → E) {t : set γ}
  (ht : measurable_set t) (hf : integrable_on f (univ ×ˢ t) ((κ ⊗ₖ η) a)) :
  ∫ z in univ ×ˢ t, f z ∂((κ ⊗ₖ η) a) = ∫ x, ∫ y in t, f (x, y) ∂(η (a, x)) ∂(κ a) :=
by simp_rw [set_integral_comp_prod measurable_set.univ ht hf, measure.restrict_univ]

end probability_theory
