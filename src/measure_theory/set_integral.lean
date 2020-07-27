/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import measure_theory.bochner_integration
import measure_theory.measure_topology
import analysis.normed_space.indicator_function

/-!
# Set integral

This file is temporarily commented out because of an ongoing refactor.

Integrate a function over a subset of a measure space.

## Main definitions

`measurable_on`, `integrable_on`, `integral_on`

## Notation

`∫ a in s, f a` is `measure_theory.integral (s.indicator f)`
-/

noncomputable theory
open set filter topological_space measure_theory
open_locale classical topological_space interval big_operators filter

variables {α β E F : Type*} [measurable_space α]

section piecewise

variables {μ : measure α} {s : set α} {f g : α → β}

lemma piecewise_ae_eq_restrict (hs : is_measurable s) : piecewise s f g =ᵐ[μ.restrict s] f :=
by { rw [ae_restrict_eq hs], exact (piecewise_eq_on s f g).eventually_eq.inf_of_right }

lemma piecewise_ae_eq_restrict_compl (hs : is_measurable s) :
  piecewise s f g =ᵐ[μ.restrict sᶜ] g :=
by { rw [ae_restrict_eq hs.compl], exact (piecewise_eq_on_compl s f g).eventually_eq.inf_of_right }

end piecewise

section indicator_function

variables [has_zero β] {μ : measure α} {s : set α} {f : α → β}

lemma indicator_ae_eq_restrict (hs : is_measurable s) : indicator s f =ᵐ[μ.restrict s] f :=
piecewise_ae_eq_restrict hs

lemma indicator_ae_eq_restrict_compl (hs : is_measurable s) : indicator s f =ᵐ[μ.restrict sᶜ] 0 :=
piecewise_ae_eq_restrict_compl hs

end indicator_function

namespace measure_theory

section normed_group

variables [normed_group E] {f : α → E} {s t : set α} {μ ν : measure α}

/-- A function is `integrable_on` a set `s` if the integral of its pointwise norm over `s` is less
than infinity. -/
def integrable_on (f : α → E) (s : set α) (μ : measure α . volume_tac) : Prop :=
integrable f (μ.restrict s)

lemma integrable_on.integrable (h : integrable_on f s μ) :
  integrable f (μ.restrict s) :=
h

@[simp] lemma integrable_on_empty : integrable_on f ∅ μ :=
by simp [integrable_on]

@[simp] lemma integrable_on_univ : integrable_on f univ μ ↔ integrable f μ :=
by rw [integrable_on, measure.restrict_univ]

lemma integrable_on_zero : integrable_on (λ _, (0:E)) s μ := integrable_zero _ _ _

lemma integrable_on_const {C : E} : integrable_on (λ _, C) s μ ↔ C = 0 ∨ μ s < ⊤ :=
integrable_const_iff.trans $ by rw [measure.restrict_apply_univ]

lemma integrable_on.mono (h : integrable_on f t ν) (hs : s ⊆ t) (hμ : μ ≤ ν) :
  integrable_on f s μ :=
h.mono_meas $ measure.restrict_mono hs hμ

lemma integrable_on.mono_set (h : integrable_on f t μ) (hst : s ⊆ t) :
  integrable_on f s μ :=
h.mono hst (le_refl _)

lemma integrable_on.mono_meas (h : integrable_on f s ν) (hμ : μ ≤ ν) :
  integrable_on f s μ :=
h.mono (subset.refl _) hμ

lemma integrable_on.mono_set_ae (h : integrable_on f t μ) (hst : s ≤ᵐ[μ] t) :
  integrable_on f s μ :=
h.integrable.mono_meas $ restrict_mono_ae hst

lemma integrable.integrable_on (h : integrable f μ) : integrable_on f s μ :=
h.mono_meas $ measure.restrict_le_self

lemma integrable.integrable_on' (h : integrable f (μ.restrict s)) : integrable_on f s μ :=
h

lemma integrable_on.left_of_union (h : integrable_on f (s ∪ t) μ) : integrable_on f s μ :=
h.mono_set $ subset_union_left _ _

lemma integrable_on.right_of_union (h : integrable_on f (s ∪ t) μ) : integrable_on f t μ :=
h.mono_set $ subset_union_right _ _

lemma integrable_on.union (hs : integrable_on f s μ) (ht : integrable_on f t μ) :
  integrable_on f (s ∪ t) μ :=
(hs.add_meas ht).mono_meas $ measure.restrict_union_le _ _

@[simp] lemma integrable_on_union :
  integrable_on f (s ∪ t) μ ↔ integrable_on f s μ ∧ integrable_on f t μ :=
⟨λ h, ⟨h.left_of_union, h.right_of_union⟩, λ h, h.1.union h.2⟩

@[simp] lemma integrable_on_finite_union {s : set β} (hs : finite s) {t : β → set α} :
  integrable_on f (⋃ i ∈ s, t i) μ ↔ ∀ i ∈ s, integrable_on f (t i) μ :=
begin
  apply hs.induction_on,
  { simp },
  { intros a s ha hs hf,
    simp [hf, or_imp_distrib, forall_and_distrib] }
end

@[simp] lemma integrable_on_finset_union {s : finset β} {t : β → set α} :
  integrable_on f (⋃ i ∈ s, t i) μ ↔ ∀ i ∈ s, integrable_on f (t i) μ :=
integrable_on_finite_union s.finite_to_set

lemma integrable_on.add_meas (hμ : integrable_on f s μ) (hν : integrable_on f s ν) :
  integrable_on f s (μ + ν) :=
by { delta integrable_on, rw measure.restrict_add, exact hμ.integrable.add_meas hν }

@[simp] lemma integrable_on_add_meas :
  integrable_on f s (μ + ν) ↔ integrable_on f s μ ∧ integrable_on f s ν :=
⟨λ h, ⟨h.mono_meas (measure.le_add_right (le_refl _)),
  h.mono_meas (measure.le_add_left (le_refl _))⟩,
  λ h, h.1.add_meas h.2⟩

lemma integrable_on.indicator (h : integrable_on f s μ) (hs : is_measurable s) :
  integrable (indicator s f) μ :=
by simpa only [integrable_on, integrable, nnnorm_indicator_eq_indicator_nnnorm,
  ennreal.coe_indicator, lintegral_indicator _ hs] using h

lemma integrable_on_of_bounded {C} (hs : μ s < ⊤) (hf : ∀ᵐ x ∂(μ.restrict s), ∥f x∥ ≤ C) :
  integrable_on f s μ :=
by haveI : finite_measure (μ.restrict s) := ⟨by rwa [measure.restrict_apply_univ]⟩;
  exact integrable_of_bounded hf

lemma locally_integrable_of_inf_ae {l : filter α} {s : set α}
  (hsl : s ∈ l ⊓ μ.ae) (hf : integrable_on f s μ) :
  ∃ s ∈ l, integrable_on f s μ :=
begin
  rcases hsl with ⟨t, ht, u, hu, hs⟩,
  refine ⟨t, ht, _⟩,
  dsimp only [integrable_on] at hf ⊢,
  refine hf.mono_meas (λ v hv, _),
  simp only [measure.restrict_apply hv],
  refine measure_le_of_ae_imp (mem_sets_of_superset hu $ λ x hx, _),
  exact λ ⟨hv, ht⟩, ⟨hv, hs ⟨ht, hx⟩⟩
end

lemma locally_integrable_on_of_is_bounded_under' {l : filter α} [is_measurably_generated l]
  (hμ : ∃ s ∈ l ⊓ μ.ae, μ s < ⊤) (hf : (l ⊓ μ.ae).is_bounded_under (≤) (norm ∘ f)) :
  ∃ s ∈ l, integrable_on f s μ :=
begin
  rcases hμ with ⟨s, hsl, hsμ⟩,
  rcases hf with ⟨C, hC⟩,
  simp only [eventually_map] at hC,
  rcases hC.exists_measurable_mem with ⟨t, htl, htm, hC⟩,
  refine locally_integrable_of_inf_ae (inter_mem_sets htl hsl) _,
  refine integrable_on_of_bounded (lt_of_le_of_lt (measure_mono $ inter_subset_right _ _) hsμ) _,
  exact C,
  suffices : ∀ᵐ x ∂μ.restrict t, ∥f x∥ ≤ C,
    from ae_mono (measure.restrict_mono (inter_subset_left _ _) (le_refl _)) this,
  rw [ae_restrict_eq htm, eventually_inf_principal],
  exact eventually_of_forall hC
end

lemma locally_integrable_on_of_is_bounded_under [topological_space α] [opens_measurable_space α]
  [locally_finite_measure μ] {a : α} (hf : (𝓝 a ⊓ μ.ae).is_bounded_under (≤) (norm ∘ f)) :
  ∃ s ∈ 𝓝 a, integrable_on f s μ :=
locally_integrable_on_of_is_bounded_under' ((exists_mem_nhds_finite_meas a μ).imp $
  λ s hs, ⟨(inf_le_left : 𝓝 a ⊓ _ ≤ _) hs.fst, hs.snd⟩) hf

lemma locally_integrable_on_of_tendsto' [topological_space α] [opens_measurable_space α]
  [locally_finite_measure μ] {a : α} {b : E} (hf : tendsto f (𝓝 a ⊓ μ.ae) (𝓝 b)) :
  ∃ s ∈ 𝓝 a, integrable_on f s μ :=
locally_integrable_on_of_is_bounded_under hf.norm.is_bounded_under_le

lemma locally_integrable_on_of_tendsto [topological_space α] [opens_measurable_space α]
  [locally_finite_measure μ] {a : α} {b : E} (hf : tendsto f (𝓝 a) (𝓝 b)) :
  ∃ s ∈ 𝓝 a, integrable_on f s μ :=
locally_integrable_on_of_tendsto' (tendsto_le_left inf_le_left hf)

lemma locally_integrable_on_of_continuous_at [topological_space α] [opens_measurable_space α]
  [locally_finite_measure μ] {a : α} (hf : continuous_at f a) :
  ∃ s ∈ 𝓝 a, integrable_on f s μ :=
locally_integrable_on_of_tendsto hf

variables [measurable_space E] [borel_space E] [complete_space E] [second_countable_topology E]
  [normed_space ℝ E]

lemma integral_union (hst : disjoint s t) (hs : is_measurable s) (ht : is_measurable t)
  (hfm : measurable f) (hfs : integrable_on f s μ) (hft : integrable_on f t μ) :
  ∫ x in s ∪ t, f x ∂μ = ∫ x in s, f x ∂μ + ∫ x in t, f x ∂μ :=
by simp only [integrable_on, measure.restrict_union hst hs ht, integral_add_meas hfm hfs hft]

lemma integral_empty : ∫ x in ∅, f x ∂μ = 0 := by rw [measure.restrict_empty, integral_zero_meas]

lemma integral_univ : ∫ x in univ, f x ∂μ = ∫ x, f x ∂μ := by rw [measure.restrict_univ]

lemma integral_add_compl (hs : is_measurable s) (hfm : measurable f) (hfi : integrable f μ) :
  ∫ x in s, f x ∂μ + ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ :=
by rw [← integral_union (disjoint_compl s) hs hs.compl hfm hfi.integrable_on hfi.integrable_on,
  union_compl_self, integral_univ]

lemma integral_indicator (hfm : measurable f) (hfi : integrable_on f s μ)
  (hs : is_measurable s) :
  ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ :=
have hfms : measurable (indicator s f) := hfm.indicator hs,
calc ∫ x, indicator s f x ∂μ = ∫ x in s, indicator s f x ∂μ + ∫ x in sᶜ, indicator s f x ∂μ :
  (integral_add_compl hs hfms (hfi.indicator hs)).symm
... = ∫ x in s, f x ∂μ + ∫ x in sᶜ, 0 ∂μ :
  congr_arg2 (+) (integral_congr_ae hfms hfm (indicator_ae_eq_restrict hs))
    (integral_congr_ae hfms measurable_const (indicator_ae_eq_restrict_compl hs))
... = ∫ x in s, f x ∂μ : by simp

lemma set_integral_const (c : E) : ∫ x in s, c ∂μ = (μ s).to_real • c :=
by rw [integral_const, measure.restrict_apply_univ]

lemma norm_set_integral_le_of_norm_le_const {C : ℝ} (hs : μ s < ⊤)
  (hC : ∀ᵐ x ∂(μ.restrict s), ∥f x∥ ≤ C) :
  ∥∫ x in s, f x ∂μ∥ ≤ C * (μ s).to_real :=
begin
  rw ← measure.restrict_apply_univ at *,
  haveI : finite_measure (μ.restrict s) := ⟨‹_›⟩,
  exact norm_integral_le_of_norm_le_const hC
end

end normed_group

end measure_theory

open measure_theory

lemma is_compact.integrable_on_of_bounded_ae [topological_space α] [opens_measurable_space α]
  [t2_space α]
  [normed_group E] {μ : measure α} [locally_finite_measure μ] {s : set α} (hs : is_compact s)
  {f : α → E} {C : ℝ} (hC : ∀ᵐ x ∂μ, x ∈ s → ∥f x∥ ≤ C) :
  integrable_on f s μ :=
begin
  refine is_compact.induction_on hs integrable_on_empty (λ s t hst ht, ht.mono_set hst)
    (λ s t h, h.union) _,
  intros x hx,
  haveI := hs.is_measurable.principal_is_measurably_generated,
  dunfold nhds_within,
  apply locally_integrable_on_of_is_bounded_under',
  { rcases exists_mem_nhds_finite_meas x μ with ⟨t, ht, htμ⟩,
    exact ⟨t, mem_inf_sets_of_left (mem_inf_sets_of_left ht), htμ⟩ },
  { rw [← eventually_inf_principal] at hC,
    exact ⟨C, eventually_map.2 $
      hC.filter_mono (le_inf inf_le_right (le_trans inf_le_left inf_le_right))⟩ }
end

lemma continuous_on.integrable_on_compact [topological_space α] [opens_measurable_space α]
  [t2_space α]
  [normed_group E] {μ : measure α} [locally_finite_measure μ] {s : set α} (hs : is_compact s)
  {f : α → E} (hf : continuous_on f s) :
  integrable_on f s μ :=
let ⟨C, hC⟩ := ((hs.image_of_continuous_on hf).image continuous_norm).bdd_above in
hs.integrable_on_of_bounded_ae (eventually_of_forall $
  λ x hx, hC $ mem_image_of_mem _ $ mem_image_of_mem _ hx)

lemma continuous.integrable_on_compact [topological_space α] [opens_measurable_space α]
  [t2_space α] [normed_group E] {μ : measure α} [locally_finite_measure μ]
  {f : α → E} (hf : continuous f) {s : set α} (hs : is_compact s) :
  integrable_on f s μ :=
hf.continuous_on.integrable_on_compact hs

lemma continuous.integrable_on_of_compact_closure [topological_space α] [opens_measurable_space α]
  [t2_space α] [normed_group E] {μ : measure α} [locally_finite_measure μ]
  {f : α → E} (hf : continuous f) {s : set α} (hs : is_compact (closure s)) :
  integrable_on f s μ :=
(hf.integrable_on_compact hs).mono_set subset_closure


/-
namespace integrable

variables [measurable_space α] [measurable_space β] [normed_group E]

protected lemma measure_mono

end integrable

end measure_theory

section integral_on
variables [measurable_space α]
  [normed_group β] [second_countable_topology β] [normed_space ℝ β] [complete_space β]
  [measurable_space β] [borel_space β]
  {s t : set α} {f g : α → β} {μ : measure α}
open set

lemma integral_on_congr (hf : measurable f) (hg : measurable g) (hs : is_measurable s)
  (h : ∀ᵐ a ∂μ, a ∈ s → f a = g a) : ∫ a in s, f a ∂μ = ∫ a in s, g a ∂μ :=
integral_congr_ae hf hg $ _

lemma integral_on_congr_of_set (hsm : measurable_on s f) (htm : measurable_on t f)
  (h : ∀ᵐ a, a ∈ s ↔ a ∈ t) : (∫ a in s, f a) = (∫ a in t, f a) :=
integral_congr_ae hsm htm $ indicator_congr_of_set h

variables (s t)

lemma integral_on_smul (r : ℝ) (f : α → β) : (∫ a in s, r • (f a)) = r • (∫ a in s, f a) :=
by rw [← integral_smul, indicator_smul]

lemma integral_on_mul_left (r : ℝ) (f : α → ℝ) : (∫ a in s, r * (f a)) = r * (∫ a in s, f a) :=
integral_on_smul s r f

lemma integral_on_mul_right (r : ℝ) (f : α → ℝ) : (∫ a in s, (f a) * r) = (∫ a in s, f a) * r :=
by { simp only [mul_comm], exact integral_on_mul_left s r f }

lemma integral_on_div (r : ℝ) (f : α → ℝ) : (∫ a in s, (f a) / r) = (∫ a in s, f a) / r :=
by { simp only [div_eq_mul_inv], apply integral_on_mul_right }

lemma integral_on_neg (f : α → β) : (∫ a in s, -f a) = - (∫ a in s, f a) :=
by { simp only [indicator_neg], exact integral_neg _ }

variables {s t}

lemma integral_on_add {s : set α} (hfm : measurable_on s f) (hfi : integrable_on s f) (hgm : measurable_on s g)
  (hgi : integrable_on s g) : (∫ a in s, f a + g a) = (∫ a in s, f a) + (∫ a in s, g a) :=
by { simp only [indicator_add], exact integral_add hfm hfi hgm hgi }

lemma integral_on_sub (hfm : measurable_on s f) (hfi : integrable_on s f) (hgm : measurable_on s g)
  (hgi : integrable_on s g) : (∫ a in s, f a - g a) = (∫ a in s, f a) - (∫ a in s, g a) :=
by { simp only [indicator_sub], exact integral_sub hfm hfi hgm hgi }

lemma integral_on_le_integral_on_ae {f g : α → ℝ} (hfm : measurable_on s f) (hfi : integrable_on s f)
  (hgm : measurable_on s g) (hgi : integrable_on s g) (h : ∀ᵐ a, a ∈ s → f a ≤ g a) :
  (∫ a in s, f a) ≤ (∫ a in s, g a) :=
begin
  apply integral_le_integral_ae hfm hfi hgm hgi,
  apply indicator_le_indicator_ae,
  exact h
end

lemma integral_on_le_integral_on {f g : α → ℝ} (hfm : measurable_on s f) (hfi : integrable_on s f)
  (hgm : measurable_on s g) (hgi : integrable_on s g) (h : ∀ a, a ∈ s → f a ≤ g a) :
  (∫ a in s, f a) ≤ (∫ a in s, g a) :=
integral_on_le_integral_on_ae hfm hfi hgm hgi $ by filter_upwards [] h

lemma integral_on_union (hsm : measurable_on s f) (hsi : integrable_on s f)
  (htm : measurable_on t f) (hti : integrable_on t f) (h : disjoint s t) :
  (∫ a in (s ∪ t), f a) = (∫ a in s, f a) + (∫ a in t, f a) :=
by { rw [indicator_union_of_disjoint h, integral_add hsm hsi htm hti] }

lemma integral_on_union_ae (hs : is_measurable s) (ht : is_measurable t) (hsm : measurable_on s f)
  (hsi : integrable_on s f) (htm : measurable_on t f) (hti : integrable_on t f) (h : ∀ᵐ a, a ∉ s ∩ t) :
  (∫ a in (s ∪ t), f a) = (∫ a in s, f a) + (∫ a in t, f a) :=
begin
  have := integral_congr_ae _ _ (indicator_union_ae h f),
  rw [this, integral_add hsm hsi htm hti],
  { exact hsm.union hs ht htm },
  { exact measurable.add hsm htm }
end

lemma integral_on_nonneg_of_ae {f : α → ℝ} (hf : ∀ᵐ a, a ∈ s → 0 ≤ f a) : (0:ℝ) ≤ (∫ a in s, f a) :=
integral_nonneg_of_ae $ by { filter_upwards [hf] λ a h, indicator_nonneg' h }

lemma integral_on_nonneg {f : α → ℝ} (hf : ∀ a, a ∈ s → 0 ≤ f a) : (0:ℝ) ≤ (∫ a in s, f a) :=
integral_on_nonneg_of_ae $ univ_mem_sets' hf

lemma integral_on_nonpos_of_ae {f : α → ℝ} (hf : ∀ᵐ a, a ∈ s → f a ≤ 0) : (∫ a in s, f a) ≤ 0 :=
integral_nonpos_of_nonpos_ae $ by { filter_upwards [hf] λ a h, indicator_nonpos' h }

lemma integral_on_nonpos {f : α → ℝ} (hf : ∀ a, a ∈ s → f a ≤ 0) : (∫ a in s, f a) ≤ 0 :=
integral_on_nonpos_of_ae $ univ_mem_sets' hf

lemma tendsto_integral_on_of_monotone {s : ℕ → set α} {f : α → β} (hsm : ∀i, is_measurable (s i))
  (h_mono : monotone s) (hfm : measurable_on (Union s) f) (hfi : integrable_on (Union s) f) :
  tendsto (λi, ∫ a in (s i), f a) at_top (nhds (∫ a in (Union s), f a)) :=
let bound : α → ℝ := indicator (Union s) (λa, ∥f a∥) in
begin
  apply tendsto_integral_of_dominated_convergence,
  { assume i, exact hfm.subset (hsm i) (subset_Union _ _) },
  { assumption },
  { show integrable_on (Union s) (λa, ∥f a∥), rwa integrable_on_norm_iff },
  { assume i, apply ae_of_all,
    assume a,
    rw [norm_indicator_eq_indicator_norm],
    exact indicator_le_indicator_of_subset (subset_Union _ _) (λa, norm_nonneg _) _ },
  { filter_upwards [] λa, le_trans (tendsto_indicator_of_monotone _ h_mono _ _) (pure_le_nhds _) }
end

lemma tendsto_integral_on_of_antimono (s : ℕ → set α) (f : α → β) (hsm : ∀i, is_measurable (s i))
  (h_mono : ∀i j, i ≤ j → s j ⊆ s i) (hfm : measurable_on (s 0) f) (hfi : integrable_on (s 0) f) :
  tendsto (λi, ∫ a in (s i), f a) at_top (nhds (∫ a in (Inter s), f a)) :=
let bound : α → ℝ := indicator (s 0) (λa, ∥f a∥) in
begin
  apply tendsto_integral_of_dominated_convergence,
  { assume i, refine hfm.subset (hsm i) (h_mono _ _ (zero_le _)) },
  { exact hfm.subset (is_measurable.Inter hsm) (Inter_subset _ _) },
  { show integrable_on (s 0) (λa, ∥f a∥), rwa integrable_on_norm_iff },
  { assume i, apply ae_of_all,
    assume a,
    rw [norm_indicator_eq_indicator_norm],
    refine indicator_le_indicator_of_subset (h_mono _ _ (zero_le _)) (λa, norm_nonneg _) _ },
  { filter_upwards [] λa, le_trans (tendsto_indicator_of_antimono _ h_mono _ _) (pure_le_nhds _) }
end

-- TODO : prove this for an encodable type
-- by proving an encodable version of `filter.is_countably_generated_at_top_finset_nat `
lemma integral_on_Union (s : ℕ → set α) (f : α → β) (hm : ∀i, is_measurable (s i))
  (hd : ∀ i j, i ≠ j → s i ∩ s j = ∅) (hfm : measurable_on (Union s) f) (hfi : integrable_on (Union s) f) :
  (∫ a in (Union s), f a) = ∑'i, ∫ a in s i, f a :=
suffices h : tendsto (λn:finset ℕ, ∑ i in n, ∫ a in s i, f a) at_top (𝓝 $ (∫ a in (Union s), f a)),
  by { rwa has_sum.tsum_eq },
begin
  have : (λn:finset ℕ, ∑ i in n, ∫ a in s i, f a) = λn:finset ℕ, ∫ a in (⋃i∈n, s i), f a,
  { funext,
    rw [← integral_finset_sum, indicator_finset_bUnion],
    { assume i hi j hj hij, exact hd i j hij },
    { assume i, refine hfm.subset (hm _) (subset_Union _ _) },
    { assume i, refine hfi.subset (subset_Union _ _) } },
  rw this,
  refine tendsto_integral_filter_of_dominated_convergence _ _ _ _ _ _ _,
  { exact indicator (Union s) (λ a, ∥f a∥) },
  { exact is_countably_generated_at_top_finset_nat },
  { refine univ_mem_sets' (λ n, _),
    simp only [mem_set_of_eq],
    refine hfm.subset (is_measurable.Union (λ i, is_measurable.Union_Prop (λh, hm _)))
      (bUnion_subset_Union _ _), },
  { assumption },
  { refine univ_mem_sets' (λ n, univ_mem_sets' $ _),
    simp only [mem_set_of_eq],
    assume a,
    rw ← norm_indicator_eq_indicator_norm,
    refine norm_indicator_le_of_subset (bUnion_subset_Union _ _) _ _ },
  { rw [← integrable_on, integrable_on_norm_iff], assumption },
  { filter_upwards [] λa, le_trans (tendsto_indicator_bUnion_finset _ _ _) (pure_le_nhds _) }
end

end integral_on
-/
