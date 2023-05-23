/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import probability.kernel.disintegration
import probability.notation

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


open measure_theory set filter topological_space

open_locale nnreal ennreal measure_theory topology probability_theory

namespace probability_theory

variables {α Ω E F : Type*}
  [topological_space Ω] [measurable_space Ω] [polish_space Ω] [borel_space Ω] [nonempty Ω]
  [normed_add_comm_group F] [normed_space ℝ F] [complete_space F]

section fst_snd

lemma restrict_fst {α β : Type*} {mα : measurable_space α} {mβ : measurable_space β}
  {μ : measure (α × β)} {s : set α} (hs : measurable_set s) :
  μ.fst.restrict s = (μ.restrict (s ×ˢ univ)).fst :=
begin
  ext1 t ht,
  rw [measure.fst_apply ht, measure.restrict_apply ht, measure.restrict_apply (measurable_fst ht),
    measure.fst_apply (ht.inter hs), prod_univ, preimage_inter],
end

lemma restrict_snd {α β : Type*} {mα : measurable_space α} {mβ : measurable_space β}
  {μ : measure (α × β)} {s : set β} (hs : measurable_set s) :
  μ.snd.restrict s = (μ.restrict (univ ×ˢ s)).snd :=
begin
  ext1 t ht,
  rw [measure.snd_apply ht, measure.restrict_apply ht, measure.restrict_apply (measurable_snd ht),
    measure.snd_apply (ht.inter hs), univ_prod, preimage_inter],
end

lemma fst_comp_prod {α β γ : Type*} {mα : measurable_space α} {mβ : measurable_space β}
  {mγ : measurable_space γ}
  {κ : kernel α β} {η : kernel (α × β) γ} [is_s_finite_kernel κ] [is_markov_kernel η] :
  kernel.fst (κ ⊗ₖ η) = κ :=
begin
  ext a s hs : 2,
  rw [kernel.fst_apply' _ _ hs, kernel.comp_prod_apply],
  swap, { exact (measurable_fst hs), },
  simp only [mem_set_of_eq],
  rw [← lintegral_add_compl _ hs, ← add_zero (κ a s)],
  congr,
  { have : ∀ x ∈ s, η (a, x) {c : γ | x ∈ s} = 1,
    { intros x hx, simp only [hx, set_of_true, measure_univ], },
    rw set_lintegral_congr_fun hs (eventually_of_forall this),
    simp only,
    rw [set_lintegral_const, one_mul], },
  { have : ∀ x ∈ sᶜ, η (a, x) {c : γ | x ∈ s} = 0,
    { intros x hx, simp only [(mem_compl_iff s x).mp hx, set_of_false, measure_empty], },
    rw [set_lintegral_congr_fun hs.compl (eventually_of_forall this), lintegral_zero], },
end

lemma fst_map_prod_mk₀ {Ω : Type*} {Y : α → Ω} {mΩ : measurable_space Ω} {mE : measurable_space E}
  {mα : measurable_space α} {X : α → E} {μ : measure α}
  (hX : ae_measurable X μ) (hY : ae_measurable Y μ) :
  (μ.map (λ ω, (X ω, Y ω))).fst = μ.map X :=
begin
  ext1 s hs,
  rw [measure.fst_apply hs, measure.map_apply_of_ae_measurable (hX.prod_mk hY) (measurable_fst hs),
    measure.map_apply_of_ae_measurable hX hs, ← prod_univ, mk_preimage_prod, preimage_univ,
    inter_univ],
end

lemma fst_map_prod_mk {Ω : Type*} {Y : α → Ω} {mΩ : measurable_space Ω} {mE : measurable_space E}
  {mα : measurable_space α} {X : α → E} {μ : measure α}
  (hX : measurable X) (hY : measurable Y) :
  (μ.map (λ ω, (X ω, Y ω))).fst = μ.map X :=
fst_map_prod_mk₀ hX.ae_measurable hY.ae_measurable

end fst_snd

localized "notation (name := measurable_space.comap)
  `σₘ[` X ` ; ` m `]` := measurable_space.comap X m" in probability_theory

localized "notation (name := condexp_fun')
  P `[` Y `|` X `;` m `]` := P[ Y | σₘ[X ; m]]" in probability_theory

localized "notation (name := condexp_set)
  P `⟦` E `|` m `⟧` := P[ E.indicator (λ ω, (1 : ℝ)) | m]" in probability_theory

localized "notation (name := condexp_fun)
  P `⟦` Y `∈ₘ` s `|` X `;` m `⟧` := P ⟦ Y ⁻¹' s | σₘ[X ; m] ⟧" in probability_theory

variables {mα : measurable_space α} {μ : measure α} {X : α → E} {Y : α → Ω} [is_finite_measure μ]

/-- Kernel associated with the conditional expectation of `Y` given `X`. -/
noncomputable
def cond_distrib {mα : measurable_space α} [measurable_space E]
  (Y : α → Ω) (X : α → E) (μ : measure α) [is_finite_measure μ] :
  kernel E Ω :=
(μ.map (λ a, (X a, Y a))).cond_kernel

noncomputable
def condexp_kernel (μ : measure Ω) [is_finite_measure μ] (m : measurable_space Ω) :
  @kernel Ω Ω m _inst_2 :=
@cond_distrib Ω Ω Ω _ _inst_2 _ _ _ _inst_2 m id id μ _

instance [measurable_space E] : is_markov_kernel (cond_distrib Y X μ) :=
by { rw cond_distrib, apply_instance, }

lemma measurable_cond_distrib {mE : measurable_space E}
  {s : set Ω} (hs : measurable_set s) :
  measurable[σₘ[X ; mE]] (λ ω, cond_distrib Y X μ (X ω) s) :=
(kernel.measurable_coe _ hs).comp (measurable.of_comap_le le_rfl)

lemma integrable_cond_distrib_to_real [measurable_space E]
  (hX : measurable X) {s : set Ω} (hs : measurable_set s) :
  integrable (λ ω, (cond_distrib Y X μ (X ω) s).to_real) μ :=
begin
  refine integrable_to_real_of_lintegral_ne_top (measurable.ae_measurable _) _,
  { exact (kernel.measurable_coe _ hs).comp hX, },
  { refine ne_of_lt _,
    calc ∫⁻ ω, cond_distrib Y X μ (X ω) s ∂μ
        ≤ ∫⁻ ω, 1 ∂μ : lintegral_mono (λ ω, prob_le_one)
    ... = μ univ : lintegral_one
    ... < ∞ : measure_lt_top _ _, },
end

lemma set_lintegral_preimage_cond_distrib {mE : measurable_space E}
  (hX : measurable X) (hY : measurable Y)
  {s : set Ω} (hs : measurable_set s) {t : set E} (ht : measurable_set t) :
  ∫⁻ ω in X ⁻¹' t, cond_distrib Y X μ (X ω) s ∂μ = μ (X ⁻¹' t ∩ Y ⁻¹' s) :=
begin
  change ∫⁻ ω in X ⁻¹' t, ((λ x, cond_distrib Y X μ x s) ∘ X) ω ∂μ = μ (X ⁻¹' t ∩ Y ⁻¹' s),
  rw [lintegral_comp (kernel.measurable_coe _ hs) hX, cond_distrib,
    ← measure.restrict_map hX ht, ← fst_map_prod_mk hX hY,
    set_lintegral_cond_kernel_eq_measure_prod _ ht hs, measure.map_apply (hX.prod_mk hY) (ht.prod hs),
    mk_preimage_prod],
end

lemma set_lintegral_cond_distrib_of_measurable {mE : measurable_space E}
  (hX : measurable X) (hY : measurable Y)
  {s : set Ω} (hs : measurable_set s) {t : set α} (ht : measurable_set[σₘ[X ; mE]] t) :
  ∫⁻ ω in t, cond_distrib Y X μ (X ω) s ∂μ = μ (t ∩ Y ⁻¹' s) :=
by { obtain ⟨tₑ, htₑ, rfl⟩ := ht, rw set_lintegral_preimage_cond_distrib hX hY hs htₑ, }

lemma cond_distrib_ae_eq_condexp {mE : measurable_space E} (hX : measurable X) (hY : measurable Y)
  {s : set Ω} (hs : measurable_set s) :
  (λ ω, (cond_distrib Y X μ (X ω) s).to_real) =ᵐ[μ] μ⟦Y ∈ₘ s | X ; mE⟧ :=
begin
  refine ae_eq_condexp_of_forall_set_integral_eq hX.comap_le _ _ _ _,
  { exact (integrable_const _).indicator (hY hs),  },
  { exact λ t ht _, (integrable_cond_distrib_to_real hX hs).integrable_on, },
  { intros t ht _,
    rw [integral_to_real ((measurable_cond_distrib hs).mono hX.comap_le le_rfl).ae_measurable
        (eventually_of_forall (λ ω, measure_lt_top (cond_distrib Y X μ (X ω)) _)),
      integral_indicator_const _ (hY hs), measure.restrict_apply (hY hs), smul_eq_mul, mul_one,
      inter_comm, set_lintegral_cond_distrib_of_measurable hX hY hs ht], },
  { refine (measurable.strongly_measurable _).ae_strongly_measurable',
    refine @measurable.ennreal_to_real _ σₘ[X ; mE] _ _,
    exact measurable_cond_distrib hs, },
end

lemma integrable_integral_norm_cond_kernel {F : Type*} {mE : measurable_space E}
  {ρ : measure (E × Ω)} [is_finite_measure ρ]
  [normed_add_comm_group F] {f : E × Ω → F} (hf_int : integrable f ρ) :
  integrable (λ x, ∫ y, ‖f (x, y)‖ ∂(ρ.cond_kernel x)) ρ.fst :=
begin
  have hf_int' := hf_int,
  nth_rewrite 0 measure_eq_comp_prod ρ at hf_int,
  rw integrable_comp_prod_iff at hf_int,
  swap,
  { rw ←measure_eq_comp_prod ρ,
    exact hf_int'.1, },
  simp_rw [kernel.prod_mk_left_apply, kernel.const_apply] at hf_int,
  exact hf_int.2,
end

lemma integrable_norm_integral_cond_kernel {mE : measurable_space E}
  {ρ : measure (E × Ω)} [is_finite_measure ρ] {f : E × Ω → F} (hf_int : integrable f ρ) :
  integrable (λ x, ‖∫ y, f (x, y) ∂(ρ.cond_kernel x)‖) ρ.fst :=
begin
  refine integrable.mono (integrable_integral_norm_cond_kernel hf_int)
    hf_int.1.integral_cond_kernel.norm _,
  refine eventually_of_forall (λ x, _),
  rw norm_norm,
  refine (norm_integral_le_integral_norm _).trans_eq _,
  { rw real.norm_of_nonneg,
    exact integral_nonneg_of_ae (eventually_of_forall (λ y, norm_nonneg _)), },
end

lemma integrable_integral_cond_kernel {mE : measurable_space E} {ρ : measure (E × Ω)} [is_finite_measure ρ]
  {f : E × Ω → F} (hf_int : integrable f ρ) :
  integrable (λ x, ∫ y, f (x, y) ∂(ρ.cond_kernel x)) ρ.fst :=
(integrable_norm_iff (ae_strongly_measurable.integral_cond_kernel hf_int.1)).mp
  (integrable_norm_integral_cond_kernel hf_int)

lemma integrable_cond_distrib {mE : measurable_space E} (hX : measurable X) (hY : measurable Y)
  {f : E × Ω → F} (hf_int : integrable f (μ.map (λ a, (X a, Y a)))) :
  integrable (λ ω, ∫ y, f (X ω, y) ∂(cond_distrib Y X μ (X ω))) μ :=
begin
  change integrable ((λ x, ∫ y, f (x, y) ∂(cond_distrib Y X μ x)) ∘ X) μ,
  refine integrable.comp_measurable _ hX,
  rw [← fst_map_prod_mk hX hY, cond_distrib],
  exact integrable_integral_cond_kernel hf_int,
end

lemma _root_.measure_theory.ae_strongly_measurable.integral_cond_distrib
  {mE : measurable_space E} (hX : measurable X) (hY : measurable Y)
  {f : E × Ω → F} (hf : ae_strongly_measurable f (μ.map (λ ω, (X ω, Y ω)))) :
  ae_strongly_measurable (λ x, ∫ y, f (x, y) ∂(cond_distrib Y X μ x)) (μ.map X) :=
by { rw ← fst_map_prod_mk hX hY, exact hf.integral_cond_kernel, }

open measure_theory

lemma measure.map_comap_ac {α γ : Type*}
  {m0 : measurable_space α} {mγ : measurable_space γ}
  {μ : measure α} {g : γ → α} (hg : measurable g) :
  (μ.comap g).map g ≪ μ :=
begin
  intros s hμs,
  let t := to_measurable μ s,
  suffices : (μ.comap g).map g t = 0, from measure_mono_null (subset_to_measurable μ s) this,
  have hμt: μ t = 0, by rwa measure_to_measurable,
  rw measure.map_apply hg (measurable_set_to_measurable _ _),
  by_cases hg' : function.injective g ∧ ∀ s', measurable_set s' → null_measurable_set (g '' s') μ,
  { rw measure.comap_apply₀ g _ hg'.1 hg'.2 _,
    { exact measure_mono_null (image_preimage_subset _ _) hμt, },
    { exact measurable_set.null_measurable_set (hg (measurable_set_to_measurable _ _))}, },
  { classical,
    rw [measure.comap, dif_neg hg', measure.coe_zero, pi.zero_apply], },
end

lemma _root_.measure_theory.ae_strongly_measurable.comp_measurable''
  {α β γ : Type*} [topological_space β] {m0 : measurable_space α} {mγ : measurable_space γ}
  {f : α → β} {μ : measure α} (hf : ae_strongly_measurable f μ) {g : γ → α} (hg : measurable g) :
  ae_strongly_measurable' (measurable_space.comap g m0) (f ∘ g) (μ.comap g) :=
begin
  let f' := hf.mk f,
  refine ⟨f' ∘ g, _, _⟩,
  { exact hf.strongly_measurable_mk.comp_measurable (measurable_iff_comap_le.mpr le_rfl), },
  { exact ae_eq_comp' hg.ae_measurable hf.ae_eq_mk (measure.map_comap_ac hg), },
end

lemma _root_.measure_theory.ae_strongly_measurable.comp_measurable'
  {α β γ : Type*} [topological_space β] {m0 : measurable_space α} {mγ : measurable_space γ}
  {f : α → β} {μ : measure γ} {g : γ → α}
  (hf : ae_strongly_measurable f (μ.map g)) (hg : measurable g) :
  ae_strongly_measurable' (measurable_space.comap g m0) (f ∘ g) μ :=
begin
  let f' := hf.mk f,
  refine ⟨f' ∘ g, _, _⟩,
  { exact hf.strongly_measurable_mk.comp_measurable (measurable_iff_comap_le.mpr le_rfl), },
  { exact ae_eq_comp hg.ae_measurable hf.ae_eq_mk, },
end

open measure_theory

lemma ae_strongly_measurable'_integral_cond_distrib {mE : measurable_space E}
  (hX : measurable X) (hY : measurable Y)
  {f : E × Ω → F} (hf_int : integrable f (μ.map (λ ω, (X ω, Y ω)))) :
  ae_strongly_measurable' σₘ[X ; mE] (λ ω, ∫ y, f (X ω, y) ∂(cond_distrib Y X μ (X ω))) μ :=
(hf_int.1.integral_cond_distrib hX hY).comp_measurable' hX

lemma todo'' {mE : measurable_space E} (hX : measurable X) (hY : measurable Y)
  {f : E × Ω → F} (hf_int : integrable f (μ.map (λ ω, (X ω, Y ω)))) :
  μ[(λ ω, f (X ω, Y ω)) | X; mE] =ᵐ[μ] λ ω, ∫ y, f (X ω, y) ∂(cond_distrib Y X μ (X ω)) :=
begin
  have hf_int' : integrable (λ ω, f (X ω, Y ω)) μ,
  { exact (integrable_map_measure hf_int.1 (hX.prod_mk hY).ae_measurable).mp hf_int, },
  refine (ae_eq_condexp_of_forall_set_integral_eq hX.comap_le hf_int' (λ s hs hμs, _) _ _).symm,
  { exact (integrable_cond_distrib hX hY hf_int).integrable_on, },
  { rintros s ⟨t, ht, rfl⟩ _,
    change ∫ ω in X ⁻¹' t, ((λ x', ∫ y, f (x', y) ∂(cond_distrib Y X μ) x') ∘ X) ω ∂μ
      = ∫ ω in X ⁻¹' t, f (X ω, Y ω) ∂μ,
    rw ← integral_map hX.ae_measurable,
    swap,
    { rw ← measure.restrict_map hX ht,
      exact (hf_int.1.integral_cond_distrib hX hY).restrict, },
    rw [← measure.restrict_map hX ht, ← fst_map_prod_mk hX hY, cond_distrib,
      set_integral_cond_kernel_univ_left ht hf_int.integrable_on,
      set_integral_map (ht.prod measurable_set.univ) hf_int.1 (hX.prod_mk hY).ae_measurable,
      mk_preimage_prod, preimage_univ, inter_univ], },
  { exact ae_strongly_measurable'_integral_cond_distrib hX hY hf_int, },
end

lemma todo {mE : measurable_space E} (hX : measurable X) (hY : measurable Y)
  {f : E × Ω → F} (hf : strongly_measurable f) (hf_int : integrable (λ ω, f (X ω, Y ω)) μ) :
  μ[(λ ω, f (X ω, Y ω)) | X; mE] =ᵐ[μ] λ ω, ∫ y, f (X ω, y) ∂(cond_distrib Y X μ (X ω)) :=
begin
  have hf_int' : integrable f (μ.map (λ ω, (X ω, Y ω))),
  { rwa integrable_map_measure hf.ae_strongly_measurable (hX.prod_mk hY).ae_measurable, },
  exact todo'' hX hY hf_int',
end

lemma todo' {Ω} [normed_add_comm_group Ω] [normed_space ℝ Ω] [complete_space Ω]
  [measurable_space Ω] [borel_space Ω] [second_countable_topology Ω] {Y : α → Ω}
  {mE : measurable_space E}
  (hX : measurable X) (hY : measurable Y) (hY_int : integrable Y μ) :
  μ[Y | X; mE] =ᵐ[μ] λ ω, ∫ y, y ∂(cond_distrib Y X μ (X ω)) :=
todo hX hY measurable_snd.strongly_measurable hY_int

lemma condexp_ae_eq_integral_kernel {Ω : Type*} [topological_space Ω] (m : measurable_space Ω)
  {mΩ : measurable_space Ω} [borel_space Ω] [polish_space Ω] [nonempty Ω] (hm : m ≤ mΩ)
  {μ : measure Ω} [is_finite_measure μ]
  {f : Ω → F} (hf : strongly_measurable f) (hf_int : integrable f μ) :
  μ[f | m] =ᵐ[μ] λ ω, ∫ y, f y ∂(condexp_kernel μ m ω) :=
begin
  have hX : @measurable Ω Ω mΩ m id := measurable_id.mono le_rfl hm,
  have hY : measurable (id : Ω → Ω) := measurable_id,
  have hf' : @strongly_measurable (Ω × Ω) F _ (m.prod mΩ) (λ x : Ω × Ω, f x.2) :=
    hf.comp_measurable measurable_id.snd,
  refine eventually_eq.trans _ (todo hX hY hf' hf_int),
  simp only [measurable_space.comap_id, id.def],
end

end probability_theory
