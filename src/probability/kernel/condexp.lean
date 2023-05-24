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

namespace measure_theory

lemma measure.map_comap_ac {α γ : Type*} {m0 : measurable_space α} {mγ : measurable_space γ}
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

lemma ae_strongly_measurable.comp_measurable''
  {α β γ : Type*} [topological_space β] {m0 : measurable_space α} {mγ : measurable_space γ}
  {f : α → β} {μ : measure α} (hf : ae_strongly_measurable f μ)
  {g : γ → α} (hg : measurable g) :
  ae_strongly_measurable' (measurable_space.comap g m0) (f ∘ g) (μ.comap g) :=
begin
  let f' := hf.mk f,
  refine ⟨f' ∘ g, _, _⟩,
  { exact hf.strongly_measurable_mk.comp_measurable (measurable_iff_comap_le.mpr le_rfl), },
  { exact ae_eq_comp' hg.ae_measurable hf.ae_eq_mk (measure.map_comap_ac hg), },
end

lemma ae_strongly_measurable.comp_ae_measurable'
  {α β γ : Type*} [topological_space β] {m0 : measurable_space α} {mγ : measurable_space γ}
  {f : α → β} {μ : measure γ} {g : γ → α}
  (hf : ae_strongly_measurable f (μ.map g)) (hg : ae_measurable g μ) :
  ae_strongly_measurable' (measurable_space.comap g m0) (f ∘ g) μ :=
begin
  let f' := hf.mk f,
  refine ⟨f' ∘ g, _, _⟩,
  { exact hf.strongly_measurable_mk.comp_measurable (measurable_iff_comap_le.mpr le_rfl), },
  { exact ae_eq_comp hg hf.ae_eq_mk, },
end

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

end fst_snd

end measure_theory

open measure_theory

namespace probability_theory

variables {α Ω β F : Type*}
  [topological_space Ω] [measurable_space Ω] [polish_space Ω] [borel_space Ω] [nonempty Ω]
  [normed_add_comm_group F] [normed_space ℝ F] [complete_space F]

section fst_snd

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

lemma fst_map_prod_mk₀ {Ω : Type*} {Y : α → Ω} {mΩ : measurable_space Ω} {mβ : measurable_space β}
  {mα : measurable_space α} {X : α → β} {μ : measure α}
  (hX : ae_measurable X μ) (hY : ae_measurable Y μ) :
  (μ.map (λ ω, (X ω, Y ω))).fst = μ.map X :=
begin
  ext1 s hs,
  rw [measure.fst_apply hs, measure.map_apply_of_ae_measurable (hX.prod_mk hY) (measurable_fst hs),
    measure.map_apply_of_ae_measurable hX hs, ← prod_univ, mk_preimage_prod, preimage_univ,
    inter_univ],
end

lemma fst_map_prod_mk {Ω : Type*} {Y : α → Ω} {mΩ : measurable_space Ω} {mβ : measurable_space β}
  {mα : measurable_space α} {X : α → β} {μ : measure α}
  (hX : measurable X) (hY : measurable Y) :
  (μ.map (λ ω, (X ω, Y ω))).fst = μ.map X :=
fst_map_prod_mk₀ hX.ae_measurable hY.ae_measurable

end fst_snd

localized "notation (name := condexp_fun_comap')
  P `[` Y `|` X `;` m `]` := P[ Y | m.comap X]" in probability_theory

localized "notation (name := condexp_indicator)
  P `⟦` s `|` m `⟧` := P[ s.indicator (λ ω, (1 : ℝ)) | m]" in probability_theory

localized "notation (name := condexp_fun_mem)
  P `⟦` Y `∈ₘ` s `|` X `;` m `⟧` := P ⟦ Y ⁻¹' s | m.comap X ⟧" in probability_theory

variables {mα : measurable_space α} {μ : measure α} {X : α → β} {Y : α → Ω} [is_finite_measure μ]

/-- **Regular conditional probability distribution**: kernel associated with the conditional
expectation of `Y` given `X`. -/
@[irreducible] noncomputable
def cond_distrib {mα : measurable_space α} [measurable_space β]
  (Y : α → Ω) (X : α → β) (μ : measure α) [is_finite_measure μ] :
  kernel β Ω :=
(μ.map (λ a, (X a, Y a))).cond_kernel

instance [measurable_space β] : is_markov_kernel (cond_distrib Y X μ) :=
by { rw cond_distrib, apply_instance, }

lemma measurable_cond_distrib {mβ : measurable_space β}
  {s : set Ω} (hs : measurable_set s) :
  measurable[mβ.comap X] (λ ω, cond_distrib Y X μ (X ω) s) :=
(kernel.measurable_coe _ hs).comp (measurable.of_comap_le le_rfl)

lemma integrable_to_real_cond_distrib {mβ : measurable_space β}
  (hX : ae_measurable X μ) {s : set Ω} (hs : measurable_set s) :
  integrable (λ ω, (cond_distrib Y X μ (X ω) s).to_real) μ :=
begin
  refine integrable_to_real_of_lintegral_ne_top _ _,
  { exact measurable.comp_ae_measurable (kernel.measurable_coe _ hs) hX, },
  { refine ne_of_lt _,
    calc ∫⁻ ω, cond_distrib Y X μ (X ω) s ∂μ
        ≤ ∫⁻ ω, 1 ∂μ : lintegral_mono (λ ω, prob_le_one)
    ... = μ univ : lintegral_one
    ... < ∞ : measure_lt_top _ _, },
end

lemma _root_.measure_theory.integrable.integral_cond_distrib {mβ : measurable_space β}
  (hX : ae_measurable X μ) (hY : ae_measurable Y μ)
  {f : β × Ω → F} (hf_int : integrable f (μ.map (λ a, (X a, Y a)))) :
  integrable (λ ω, ∫ y, f (X ω, y) ∂(cond_distrib Y X μ (X ω))) μ :=
begin
  change integrable ((λ x, ∫ y, f (x, y) ∂(cond_distrib Y X μ x)) ∘ X) μ,
  refine integrable.comp_ae_measurable _ hX,
  rw [← fst_map_prod_mk₀ hX hY, cond_distrib],
  exact hf_int.integral_cond_kernel,
end

lemma _root_.measure_theory.ae_strongly_measurable.integral_cond_distrib {mβ : measurable_space β}
  (hX : ae_measurable X μ) (hY : ae_measurable Y μ)
  {f : β × Ω → F} (hf : ae_strongly_measurable f (μ.map (λ ω, (X ω, Y ω)))) :
  ae_strongly_measurable (λ x, ∫ y, f (x, y) ∂(cond_distrib Y X μ x)) (μ.map X) :=
by { rw ← fst_map_prod_mk₀ hX hY, rw cond_distrib, exact hf.integral_cond_kernel, }

lemma ae_strongly_measurable'_integral_cond_distrib {mβ : measurable_space β}
  (hX : ae_measurable X μ) (hY : ae_measurable Y μ)
  {f : β × Ω → F} (hf_int : integrable f (μ.map (λ ω, (X ω, Y ω)))) :
  ae_strongly_measurable' (mβ.comap X) (λ ω, ∫ y, f (X ω, y) ∂(cond_distrib Y X μ (X ω))) μ :=
(hf_int.1.integral_cond_distrib hX hY).comp_ae_measurable' hX

lemma set_lintegral_preimage_cond_distrib {mβ : measurable_space β}
  (hX : measurable X) (hY : ae_measurable Y μ)
  {s : set Ω} (hs : measurable_set s) {t : set β} (ht : measurable_set t) :
  ∫⁻ ω in X ⁻¹' t, cond_distrib Y X μ (X ω) s ∂μ = μ (X ⁻¹' t ∩ Y ⁻¹' s) :=
begin
  change ∫⁻ ω in X ⁻¹' t, ((λ x, cond_distrib Y X μ x s) ∘ X) ω ∂μ = μ (X ⁻¹' t ∩ Y ⁻¹' s),
  rw [lintegral_comp (kernel.measurable_coe _ hs) hX, cond_distrib,
    ← measure.restrict_map hX ht, ← fst_map_prod_mk₀ hX.ae_measurable hY,
    set_lintegral_cond_kernel_eq_measure_prod _ ht hs,
    measure.map_apply_of_ae_measurable (hX.ae_measurable.prod_mk hY) (ht.prod hs),
    mk_preimage_prod],
end

lemma set_lintegral_cond_distrib_of_measurable {mβ : measurable_space β}
  (hX : measurable X) (hY : ae_measurable Y μ)
  {s : set Ω} (hs : measurable_set s) {t : set α} (ht : measurable_set[mβ.comap X] t) :
  ∫⁻ ω in t, cond_distrib Y X μ (X ω) s ∂μ = μ (t ∩ Y ⁻¹' s) :=
by { obtain ⟨tₑ, htₑ, rfl⟩ := ht, rw set_lintegral_preimage_cond_distrib hX hY hs htₑ, }

lemma cond_distrib_ae_eq_condexp {mβ : measurable_space β} (hX : measurable X) (hY : measurable Y)
  {s : set Ω} (hs : measurable_set s) :
  (λ ω, (cond_distrib Y X μ (X ω) s).to_real) =ᵐ[μ] μ⟦Y ∈ₘ s | X ; mβ⟧ :=
begin
  refine ae_eq_condexp_of_forall_set_integral_eq hX.comap_le _ _ _ _,
  { exact (integrable_const _).indicator (hY hs),  },
  { exact λ t ht _, (integrable_to_real_cond_distrib hX.ae_measurable hs).integrable_on, },
  { intros t ht _,
    rw [integral_to_real ((measurable_cond_distrib hs).mono hX.comap_le le_rfl).ae_measurable
        (eventually_of_forall (λ ω, measure_lt_top (cond_distrib Y X μ (X ω)) _)),
      integral_indicator_const _ (hY hs), measure.restrict_apply (hY hs), smul_eq_mul, mul_one,
      inter_comm, set_lintegral_cond_distrib_of_measurable hX hY.ae_measurable hs ht], },
  { refine (measurable.strongly_measurable _).ae_strongly_measurable',
    refine @measurable.ennreal_to_real _ (mβ.comap X) _ _,
    exact measurable_cond_distrib hs, },
end

lemma todo'' {mβ : measurable_space β} (hX : measurable X) (hY : ae_measurable Y μ)
  {f : β × Ω → F} (hf_int : integrable f (μ.map (λ ω, (X ω, Y ω)))) :
  μ[(λ ω, f (X ω, Y ω)) | X; mβ] =ᵐ[μ] λ ω, ∫ y, f (X ω, y) ∂(cond_distrib Y X μ (X ω)) :=
begin
  have hf_int' : integrable (λ ω, f (X ω, Y ω)) μ,
  { exact (integrable_map_measure hf_int.1 (hX.ae_measurable.prod_mk hY)).mp hf_int, },
  refine (ae_eq_condexp_of_forall_set_integral_eq hX.comap_le hf_int' (λ s hs hμs, _) _ _).symm,
  { exact (hf_int.integral_cond_distrib hX.ae_measurable hY).integrable_on, },
  { rintros s ⟨t, ht, rfl⟩ _,
    change ∫ ω in X ⁻¹' t, ((λ x', ∫ y, f (x', y) ∂(cond_distrib Y X μ) x') ∘ X) ω ∂μ
      = ∫ ω in X ⁻¹' t, f (X ω, Y ω) ∂μ,
    rw ← integral_map hX.ae_measurable,
    swap,
    { rw ← measure.restrict_map hX ht,
      exact (hf_int.1.integral_cond_distrib hX.ae_measurable hY).restrict, },
    rw [← measure.restrict_map hX ht, ← fst_map_prod_mk₀ hX.ae_measurable hY, cond_distrib,
      set_integral_cond_kernel_univ_right ht hf_int.integrable_on,
      set_integral_map (ht.prod measurable_set.univ) hf_int.1 (hX.ae_measurable.prod_mk hY),
      mk_preimage_prod, preimage_univ, inter_univ], },
  { exact ae_strongly_measurable'_integral_cond_distrib hX.ae_measurable hY hf_int, },
end

lemma todo₀ {mβ : measurable_space β} (hX : measurable X) (hY : ae_measurable Y μ)
  {f : β × Ω → F} (hf : ae_strongly_measurable f (μ.map (λ a, (X a, Y a))))
  (hf_int : integrable (λ ω, f (X ω, Y ω)) μ) :
  μ[(λ ω, f (X ω, Y ω)) | X; mβ] =ᵐ[μ] λ ω, ∫ y, f (X ω, y) ∂(cond_distrib Y X μ (X ω)) :=
begin
  have hf_int' : integrable f (μ.map (λ ω, (X ω, Y ω))),
  { rwa integrable_map_measure hf (hX.ae_measurable.prod_mk hY), },
  exact todo'' hX hY hf_int',
end

lemma todo {mβ : measurable_space β} (hX : measurable X) (hY : ae_measurable Y μ)
  {f : β × Ω → F} (hf : strongly_measurable f) (hf_int : integrable (λ ω, f (X ω, Y ω)) μ) :
  μ[(λ ω, f (X ω, Y ω)) | X; mβ] =ᵐ[μ] λ ω, ∫ y, f (X ω, y) ∂(cond_distrib Y X μ (X ω)) :=
begin
  have hf_int' : integrable f (μ.map (λ ω, (X ω, Y ω))),
  { rwa integrable_map_measure hf.ae_strongly_measurable (hX.ae_measurable.prod_mk hY), },
  exact todo'' hX hY hf_int',
end

lemma todo_right {mβ : measurable_space β} (hX : measurable X) (hY : ae_measurable Y μ)
  {f : Ω → F} (hf : strongly_measurable f) (hf_int : integrable (λ ω, f (Y ω)) μ) :
  μ[(λ ω, f (Y ω)) | X; mβ] =ᵐ[μ] λ ω, ∫ y, f y ∂(cond_distrib Y X μ (X ω)) :=
todo hX hY (hf.comp_measurable measurable_snd) hf_int

lemma todo' {Ω} [normed_add_comm_group Ω] [normed_space ℝ Ω] [complete_space Ω]
  [measurable_space Ω] [borel_space Ω] [second_countable_topology Ω] {Y : α → Ω}
  {mβ : measurable_space β}
  (hX : measurable X) (hY_int : integrable Y μ) :
  μ[Y | X; mβ] =ᵐ[μ] λ ω, ∫ y, y ∂(cond_distrib Y X μ (X ω)) :=
todo_right hX hY_int.1.ae_measurable strongly_measurable_id hY_int

/-- Kernel associated with the conditional expectation with respect to a σ-algebra. -/
noncomputable
def condexp_kernel {Ω : Type*} [mΩ : measurable_space Ω] [topological_space Ω] [borel_space Ω]
  [polish_space Ω] [nonempty Ω]
  (μ : measure Ω) [is_finite_measure μ] (m : measurable_space Ω) :
  @kernel Ω Ω m mΩ :=
@cond_distrib Ω Ω Ω _ mΩ _ _ _ mΩ m id id μ _

lemma condexp_ae_eq_integral_condexp_kernel {Ω : Type*} [topological_space Ω]
  (m : measurable_space Ω) {mΩ : measurable_space Ω} [borel_space Ω] [polish_space Ω] [nonempty Ω]
  (hm : m ≤ mΩ) {μ : measure Ω} [is_finite_measure μ]
  {f : Ω → F} (hf : strongly_measurable f) (hf_int : integrable f μ) :
  μ[f | m] =ᵐ[μ] λ ω, ∫ y, f y ∂(condexp_kernel μ m ω) :=
begin
  have hX : @measurable Ω Ω mΩ m id := measurable_id.mono le_rfl hm,
  have hY : ae_measurable (id : Ω → Ω) μ := ae_measurable_id,
  have hf' : @strongly_measurable (Ω × Ω) F _ (m.prod mΩ) (λ x : Ω × Ω, f x.2) :=
    hf.comp_measurable measurable_id.snd,
  refine eventually_eq.trans _ (todo hX hY hf' hf_int),
  simp only [measurable_space.comap_id, id.def],
end

end probability_theory
