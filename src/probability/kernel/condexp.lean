/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import probability.kernel.disintegration
import probability.notation
import probability.kernel.integral_comp_prod

/-!
# Kernel associated with a conditional expectation

## Main definitions

* `foo_bar`

## Main statements

* `foo_bar_unique`

## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/


open measure_theory set filter


open_locale nnreal ennreal measure_theory topology probability_theory

namespace probability_theory

lemma integral_cond_kernel_fst {α F : Type*} {mα : measurable_space α} (ρ : measure (α × ℝ))
  [is_finite_measure ρ]
  [normed_add_comm_group F] [normed_space ℝ F] [complete_space F]
  {f : α × ℝ → F} (hf : integrable f ρ)
  {s : set (α × ℝ)} (hs : measurable_set s) :
  ∫ a, ∫ x, f (a, x) ∂(cond_kernel ρ) a ∂ρ.fst = ∫ ω, f ω ∂ρ :=
begin
  nth_rewrite 1 measure_eq_comp_prod ρ,
  have hf' :
    integrable f ((kernel.const unit ρ.fst ⊗ₖ kernel.prod_mk_left (cond_kernel ρ) unit) ()),
  { rwa measure_eq_comp_prod ρ at hf, },
  rw [integral_comp_prod _ hf', kernel.const_apply],
  simp_rw kernel.prod_mk_left_apply,
end

lemma restrict_fst {α β : Type*} {mα : measurable_space α} {mβ : measurable_space β}
  {μ : measure (α × β)} {s : set α} (hs : measurable_set s) :
  μ.fst.restrict s = (μ.restrict (s ×ˢ univ)).fst :=
begin
  ext1 t ht,
  rw [measure.fst_apply _ ht, measure.restrict_apply ht,
    measure.restrict_apply (measurable_fst ht), measure.fst_apply _ (ht.inter hs), prod_univ,
    preimage_inter],
end

lemma fst_comp_prod {α β γ : Type*} {mα : measurable_space α} {mβ : measurable_space β}
  {mγ : measurable_space γ}
  {κ : kernel α β} {η : kernel (α × β) γ} [kernel.is_s_finite_kernel κ]
  [kernel.is_s_finite_kernel η] :
  kernel.fst (κ ⊗ₖ η) = κ :=
begin
  ext a s hs : 2,
  rw kernel.fst_apply' _ _ hs,
  rw kernel.comp_prod_apply,
  swap, { exact (measurable_fst hs), },
  simp only [mem_set_of_eq],
  rw ← lintegral_add_compl _ hs,
  rw ← add_zero (κ a s),
  congr,
  { sorry, },
  { sorry, },
end

lemma set_integral_cond_kernel_fst {α F : Type*} {mα : measurable_space α} (ρ : measure (α × ℝ))
  [is_finite_measure ρ]
  [normed_add_comm_group F] [normed_space ℝ F] [complete_space F]
  {f : α × ℝ → F} (hf : integrable f ρ)
  {t : set α} (ht : measurable_set t) :
  ∫ a in t, ∫ x, f (a, x) ∂(cond_kernel ρ) a ∂ρ.fst = ∫ ω in t ×ˢ univ, f ω ∂ρ :=
begin
  nth_rewrite 1 measure_eq_comp_prod ρ,
  rw set_integral_comp_prod_univ _ ht,
  { simp_rw [kernel.prod_mk_left_apply, kernel.const_apply], },
  { rw measure_eq_comp_prod ρ at hf,
    exact hf.integrable_on, },
end

localized "notation (name := measurable_space.comap)
  `σₘ[` X ` ; ` m `]` := measurable_space.comap X m" in probability_theory

localized "notation (name := condexp_fun')
  P `[` Y `|` X `;` m `]` := P[ Y | σₘ[X ; m]]" in probability_theory

localized "notation (name := condexp_set)
  P `⟦` E `|` m `⟧` := P[ E.indicator (λ ω, (1 : ℝ)) | m]" in probability_theory

localized "notation (name := condexp_fun)
  P `⟦` Y `∈ₘ` s `|` X `;` m `⟧` := P ⟦ Y ⁻¹' s | σₘ[X ; m] ⟧" in probability_theory

variables {Ω E F : Type*} {mΩ : measurable_space Ω} {μ : measure Ω} {X : Ω → E} {Y : Ω → ℝ}

/-- Kernel associated with the conditional expectation of `Y` given `X`. -/
noncomputable
def condexp_kernel {mΩ : measurable_space Ω} [measurable_space E]
  (Y : Ω → ℝ) (X : Ω → E) (μ : measure Ω) :
  kernel E ℝ :=
cond_kernel (μ.map (λ ω, (X ω, Y ω)))

instance [measurable_space E] : is_markov_kernel (condexp_kernel Y X μ) :=
by { rw condexp_kernel, apply_instance, }

lemma measurable_condexp_kernel {mE : measurable_space E}
  {s : set ℝ} (hs : measurable_set s) :
  measurable[σₘ[X ; mE]] (λ ω, condexp_kernel Y X μ (X ω) s) :=
(kernel.measurable_coe _ hs).comp (measurable.of_comap_le le_rfl)

lemma integrable_condexp_kernel_to_real [measurable_space E] [is_finite_measure μ]
  (hX : measurable X) {s : set ℝ} (hs : measurable_set s) :
  integrable (λ ω, (condexp_kernel Y X μ (X ω) s).to_real) μ :=
begin
  refine integrable_to_real_of_lintegral_ne_top (measurable.ae_measurable _) _,
  { exact (kernel.measurable_coe _ hs).comp hX, },
  { refine ne_of_lt _,
    calc ∫⁻ ω, condexp_kernel Y X μ (X ω) s ∂μ
        ≤ ∫⁻ ω, 1 ∂μ : lintegral_mono (λ ω, prob_le_one)
    ... = μ univ : lintegral_one
    ... < ∞ : measure_lt_top _ _, },
end

lemma fst_map_prod_mk {mE : measurable_space E} (hX : measurable X) (hY : measurable Y) :
  (μ.map (λ ω, (X ω, Y ω))).fst = μ.map X :=
begin
  ext1 s hs,
  rw [measure.fst_apply _ hs,  measure.map_apply (hX.prod_mk hY) (measurable_fst hs),
    measure.map_apply hX hs,  ← prod_univ, mk_preimage_prod, preimage_univ, inter_univ],
end

lemma set_lintegral_preimage_condexp_kernel {mE : measurable_space E} [is_finite_measure μ]
  (hX : measurable X) (hY : measurable Y)
  {s : set ℝ} (hs : measurable_set s) {t : set E} (ht : measurable_set t) :
  ∫⁻ ω in X ⁻¹' t, condexp_kernel Y X μ (X ω) s ∂μ = μ (X ⁻¹' t ∩ Y ⁻¹' s) :=
begin
  change ∫⁻ ω in X ⁻¹' t, ((λ x, condexp_kernel Y X μ x s) ∘ X) ω ∂μ = μ (X ⁻¹' t ∩ Y ⁻¹' s),
  rw [lintegral_comp (kernel.measurable_coe _ hs) hX, condexp_kernel,
    ← measure.restrict_map hX ht, ← fst_map_prod_mk hX hY,
    set_lintegral_cond_kernel_prod _ ht hs, measure.map_apply (hX.prod_mk hY) (ht.prod hs),
    mk_preimage_prod],
  apply_instance,
end

lemma set_lintegral_condexp_kernel_of_measurable {mE : measurable_space E} [is_finite_measure μ]
  (hX : measurable X) (hY : measurable Y)
  {s : set ℝ} (hs : measurable_set s) {t : set Ω} (ht : measurable_set[σₘ[X ; mE]] t) :
  ∫⁻ ω in t, condexp_kernel Y X μ (X ω) s ∂μ = μ (Y ⁻¹' s ∩ t) :=
begin
  obtain ⟨tₑ, htₑ, rfl⟩ := ht,
  rw [set_lintegral_preimage_condexp_kernel hX hY hs htₑ, inter_comm],
  apply_instance,
end

lemma condexp_kernel_ae_eq {mE : measurable_space E} (hX : measurable X) (hY : measurable Y)
  [is_finite_measure μ] {s : set ℝ} (hs : measurable_set s) :
  (λ ω, (condexp_kernel Y X μ (X ω) s).to_real) =ᵐ[μ] μ⟦Y ∈ₘ s | X ; mE⟧ :=
begin
  refine ae_eq_condexp_of_forall_set_integral_eq hX.comap_le _ _ _ _,
  { exact (integrable_const _).indicator (hY hs),  },
  { exact λ t ht _, (integrable_condexp_kernel_to_real hX hs).integrable_on, },
  { intros t ht _,
    rw integral_to_real ((measurable_condexp_kernel hs).mono hX.comap_le le_rfl).ae_measurable
      (eventually_of_forall (λ ω, measure_lt_top (condexp_kernel Y X μ (X ω)) _)),
    rw [integral_indicator_const _ (hY hs), measure.restrict_apply (hY hs), smul_eq_mul, mul_one],
    congr' 1,
    exact set_lintegral_condexp_kernel_of_measurable hX hY hs ht, },
  { refine (measurable.strongly_measurable _).ae_strongly_measurable',
    refine @measurable.ennreal_to_real _ σₘ[X ; mE] _ _,
    exact measurable_condexp_kernel hs, },
end

lemma aux' {mE : measurable_space E} {ρ : measure (E × ℝ)} [is_finite_measure ρ]
  {mF : measurable_space F} [normed_add_comm_group F] [normed_space ℝ F] [complete_space F]
  [topological_space.second_countable_topology F]
  {f : E × ℝ → F} (hf : measurable f) (hf_int : integrable f ρ) :
  integrable (λ x, ∫ y, ‖f (x, y)‖ ∂(cond_kernel ρ x)) ρ.fst :=
begin
  nth_rewrite 0 measure_eq_comp_prod ρ at hf_int ⊢,
  rw integrable_comp_prod_iff at hf_int,
  swap,
  { refine measurable.ae_strongly_measurable _,
    sorry, },
  simp_rw [kernel.prod_mk_left_apply, kernel.const_apply] at hf_int,
  rw ← kernel.fst_apply,
  rw fst_comp_prod,
  rw kernel.const_apply,
  exact hf_int.2,
end

lemma aux {mE : measurable_space E} {ρ : measure (E × ℝ)} [is_finite_measure ρ]
  {mF : measurable_space F} [normed_add_comm_group F] [normed_space ℝ F] [complete_space F]
  {f : E × ℝ → F} (hf : measurable f) (hf_int : integrable f ρ) :
  integrable (λ x, ‖∫ y, f (x, y) ∂(cond_kernel ρ x)‖) ρ.fst :=
begin
  refine integrable.mono (aux' hf hf_int) _ _,
  sorry,
  refine eventually_of_forall (λ x, _),
  rw norm_norm,
  refine (norm_integral_le_integral_norm _).trans_eq _,
  { rw real.norm_of_nonneg,
    exact integral_nonneg_of_ae (eventually_of_forall (λ y, norm_nonneg _)), },
end

lemma integrable_cond_kernel {mE : measurable_space E} {ρ : measure (E × ℝ)} [is_finite_measure ρ]
  {mF : measurable_space F} [normed_add_comm_group F] [normed_space ℝ F] [complete_space F]
  {f : E × ℝ → F} (hf : measurable f) (hf_int : integrable f ρ) :
  integrable (λ x, ∫ y, f (x, y) ∂(cond_kernel ρ) x) ρ.fst :=
begin
  refine (integrable_norm_iff _).mp (aux hf hf_int),
  sorry,
end

lemma integrable_condexp_kernel [is_finite_measure μ] {mE : measurable_space E}
  (hX : measurable X) (hY : measurable Y)
  {mF : measurable_space F} [normed_add_comm_group F] [normed_space ℝ F] [complete_space F]
  [topological_space.second_countable_topology F] [opens_measurable_space F]
  {f : E × ℝ → F} (hf : measurable f)
  (hf_int : integrable (λ ω, f (X ω, Y ω)) μ) :
  integrable (λ ω, ∫ y, f (X ω, y) ∂(condexp_kernel Y X μ (X ω))) μ :=
begin
  change integrable ((λ x, ∫ y, f (x, y) ∂(condexp_kernel Y X μ x)) ∘ X) μ,
  refine integrable.comp_measurable _ hX,
  rw [← fst_map_prod_mk hX hY, condexp_kernel],
  refine integrable_cond_kernel hf _,
  rwa integrable_map_measure hf.ae_strongly_measurable (hX.prod_mk hY).ae_measurable,
end

lemma todo [is_finite_measure μ] {mE : measurable_space E}
  (hX : measurable X) (hY : measurable Y)
  {mF : measurable_space F} [normed_add_comm_group F] [normed_space ℝ F] [complete_space F]
  [topological_space.second_countable_topology F] [opens_measurable_space F]
  {f : E × ℝ → F} (hf : measurable f)
  (hf_int : integrable (λ ω, f (X ω, Y ω)) μ) :
  μ[(λ ω, f (X ω, Y ω)) | X; mE] =ᵐ[μ] λ ω, ∫ y, f (X ω, y) ∂(condexp_kernel Y X μ (X ω)) :=
begin
  have hf_int' : integrable f (μ.map (λ ω, (X ω, Y ω))),
  { rwa integrable_map_measure hf.ae_strongly_measurable (hX.prod_mk hY).ae_measurable, },
  symmetry,
  refine ae_eq_condexp_of_forall_set_integral_eq hX.comap_le hf_int (λ s hs hμs, _) _ _,
  { refine integrable.integrable_on _,
    exact integrable_condexp_kernel hX hY hf hf_int, },
  { rintros s ⟨t, ht, rfl⟩ _,
    change ∫ ω in X ⁻¹' t, ((λ x', ∫ (y : ℝ), f (x', y) ∂(condexp_kernel Y X μ) x') ∘ X) ω ∂μ
      = ∫ ω in X ⁻¹' t, f (X ω, Y ω) ∂μ,
    rw ← integral_map hX.ae_measurable,
    swap, { sorry, },
    rw ← measure.restrict_map hX ht,
    rw ← fst_map_prod_mk hX hY,
    rw condexp_kernel,
    rw set_integral_cond_kernel_fst _ hf_int' ht,
    rw set_integral_map (ht.prod measurable_set.univ) hf_int'.1 (hX.prod_mk hY).ae_measurable,
    rw [mk_preimage_prod, preimage_univ, inter_univ], },
  sorry,
end

lemma todo' [is_finite_measure μ] {mE : measurable_space E}
  (hX : measurable X) (hY : measurable Y) (hY_int : integrable Y μ):
  μ[Y | X; mE] =ᵐ[μ] λ ω, ∫ y, y ∂(condexp_kernel Y X μ (X ω)) :=
todo hX hY measurable_snd hY_int

end probability_theory
