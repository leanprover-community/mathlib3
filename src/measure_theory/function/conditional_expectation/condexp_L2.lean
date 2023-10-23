/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import analysis.inner_product_space.projection
import measure_theory.function.conditional_expectation.unique

/-! # Conditional expectation in L2

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains one step of the construction of the conditional expectation, which is completed
in `measure_theory.function.conditional_expectation.basic`. See that file for a description of the
full process.

We build the conditional expectation of an `L²` function, as an element of `L²`. This is the
orthogonal projection on the subspace of almost everywhere `m`-measurable functions.

## Main definitions

* `condexp_L2`: Conditional expectation of a function in L2 with respect to a sigma-algebra: it is
the orthogonal projection on the subspace `Lp_meas`.

## Implementation notes

Most of the results in this file are valid for a complete real normed space `F`.
However, some lemmas also use `𝕜 : is_R_or_C`:
* `condexp_L2` is defined only for an `inner_product_space` for now, and we use `𝕜` for its field.
* results about scalar multiplication are stated not only for `ℝ` but also for `𝕜` if we happen to
  have `normed_space 𝕜 F`.

-/

open topological_space filter continuous_linear_map
open_locale ennreal topology measure_theory

namespace measure_theory

variables {α E E' F G G' 𝕜 : Type*} {p : ℝ≥0∞}
  [is_R_or_C 𝕜] -- 𝕜 for ℝ or ℂ
  -- E for an inner product space
  [normed_add_comm_group E] [inner_product_space 𝕜 E] [complete_space E]
  -- E' for an inner product space on which we compute integrals
  [normed_add_comm_group E'] [inner_product_space 𝕜 E']
  [complete_space E'] [normed_space ℝ E']
  -- F for a Lp submodule
  [normed_add_comm_group F] [normed_space 𝕜 F]
  -- G for a Lp add_subgroup
  [normed_add_comm_group G]
  -- G' for integrals on a Lp add_subgroup
  [normed_add_comm_group G'] [normed_space ℝ G'] [complete_space G']

variables {m m0 : measurable_space α} {μ : measure α} {s t : set α}

local notation `⟪`x`, `y`⟫` := @inner 𝕜 E _ x y
local notation `⟪`x`, `y`⟫₂` := @inner 𝕜 (α →₂[μ] E) _ x y

variables (𝕜)
/-- Conditional expectation of a function in L2 with respect to a sigma-algebra -/
noncomputable
def condexp_L2 (hm : m ≤ m0) : (α →₂[μ] E) →L[𝕜] (Lp_meas E 𝕜 m 2 μ) :=
@orthogonal_projection 𝕜 (α →₂[μ] E) _ _ _ (Lp_meas E 𝕜 m 2 μ)
  (by { haveI : fact (m ≤ m0) := ⟨hm⟩, exact infer_instance, })
variables {𝕜}

lemma ae_strongly_measurable'_condexp_L2 (hm : m ≤ m0) (f : α →₂[μ] E) :
  ae_strongly_measurable' m (condexp_L2 𝕜 hm f) μ :=
Lp_meas.ae_strongly_measurable' _

lemma integrable_on_condexp_L2_of_measure_ne_top (hm : m ≤ m0) (hμs : μ s ≠ ∞) (f : α →₂[μ] E) :
  integrable_on (condexp_L2 𝕜 hm f) s μ :=
integrable_on_Lp_of_measure_ne_top ((condexp_L2 𝕜 hm f) : α →₂[μ] E)
  fact_one_le_two_ennreal.elim hμs

lemma integrable_condexp_L2_of_is_finite_measure (hm : m ≤ m0) [is_finite_measure μ]
  {f : α →₂[μ] E} :
  integrable (condexp_L2 𝕜 hm f) μ :=
integrable_on_univ.mp $ integrable_on_condexp_L2_of_measure_ne_top hm (measure_ne_top _ _) f

lemma norm_condexp_L2_le_one (hm : m ≤ m0) : ‖@condexp_L2 α E 𝕜 _ _ _ _ _ _ μ hm‖ ≤ 1 :=
by { haveI : fact (m ≤ m0) := ⟨hm⟩, exact orthogonal_projection_norm_le _, }

lemma norm_condexp_L2_le (hm : m ≤ m0) (f : α →₂[μ] E) : ‖condexp_L2 𝕜 hm f‖ ≤ ‖f‖ :=
((@condexp_L2 _ E 𝕜 _ _ _ _ _ _ μ hm).le_op_norm f).trans
  (mul_le_of_le_one_left (norm_nonneg _) (norm_condexp_L2_le_one hm))

lemma snorm_condexp_L2_le (hm : m ≤ m0) (f : α →₂[μ] E) :
  snorm (condexp_L2 𝕜 hm f) 2 μ ≤ snorm f 2 μ :=
begin
  rw [Lp_meas_coe, ← ennreal.to_real_le_to_real (Lp.snorm_ne_top _) (Lp.snorm_ne_top _),
    ← Lp.norm_def, ← Lp.norm_def, submodule.norm_coe],
  exact norm_condexp_L2_le hm f,
end

lemma norm_condexp_L2_coe_le (hm : m ≤ m0) (f : α →₂[μ] E) :
  ‖(condexp_L2 𝕜 hm f : α →₂[μ] E)‖ ≤ ‖f‖ :=
begin
  rw [Lp.norm_def, Lp.norm_def, ← Lp_meas_coe],
  refine (ennreal.to_real_le_to_real _ (Lp.snorm_ne_top _)).mpr (snorm_condexp_L2_le hm f),
  exact Lp.snorm_ne_top _,
end

lemma inner_condexp_L2_left_eq_right (hm : m ≤ m0) {f g : α →₂[μ] E} :
  ⟪(condexp_L2 𝕜 hm f : α →₂[μ] E), g⟫₂ = ⟪f, (condexp_L2 𝕜 hm g : α →₂[μ] E)⟫₂ :=
by { haveI : fact (m ≤ m0) := ⟨hm⟩, exact inner_orthogonal_projection_left_eq_right _ f g, }

lemma condexp_L2_indicator_of_measurable (hm : m ≤ m0)
  (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) (c : E) :
  (condexp_L2 𝕜 hm (indicator_const_Lp 2 (hm s hs) hμs c) : α →₂[μ] E)
    = indicator_const_Lp 2 (hm s hs) hμs c :=
begin
  rw condexp_L2,
  haveI : fact (m ≤ m0) := ⟨hm⟩,
  have h_mem : indicator_const_Lp 2 (hm s hs) hμs c ∈ Lp_meas E 𝕜 m 2 μ,
    from mem_Lp_meas_indicator_const_Lp hm hs hμs,
  let ind := (⟨indicator_const_Lp 2 (hm s hs) hμs c, h_mem⟩ : Lp_meas E 𝕜 m 2 μ),
  have h_coe_ind : (ind : α →₂[μ] E) = indicator_const_Lp 2 (hm s hs) hμs c, by refl,
  have h_orth_mem := orthogonal_projection_mem_subspace_eq_self ind,
  rw [← h_coe_ind, h_orth_mem],
end

lemma inner_condexp_L2_eq_inner_fun (hm : m ≤ m0) (f g : α →₂[μ] E)
  (hg : ae_strongly_measurable' m g μ) :
  ⟪(condexp_L2 𝕜 hm f : α →₂[μ] E), g⟫₂ = ⟪f, g⟫₂ :=
begin
  symmetry,
  rw [← sub_eq_zero, ← inner_sub_left, condexp_L2],
  simp only [mem_Lp_meas_iff_ae_strongly_measurable'.mpr hg, orthogonal_projection_inner_eq_zero],
end

section real

variables {hm : m ≤ m0}

lemma integral_condexp_L2_eq_of_fin_meas_real (f : Lp 𝕜 2 μ) (hs : measurable_set[m] s)
  (hμs : μ s ≠ ∞) :
  ∫ x in s, condexp_L2 𝕜 hm f x ∂μ = ∫ x in s, f x ∂μ :=
begin
  rw ← L2.inner_indicator_const_Lp_one (hm s hs) hμs,
  have h_eq_inner : ∫ x in s, condexp_L2 𝕜 hm f x ∂μ
    = inner (indicator_const_Lp 2 (hm s hs) hμs (1 : 𝕜)) (condexp_L2 𝕜 hm f),
  { rw L2.inner_indicator_const_Lp_one (hm s hs) hμs,
    congr, },
  rw [h_eq_inner, ← inner_condexp_L2_left_eq_right, condexp_L2_indicator_of_measurable hm hs hμs],
end

lemma lintegral_nnnorm_condexp_L2_le (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) (f : Lp ℝ 2 μ) :
  ∫⁻ x in s, ‖condexp_L2 ℝ hm f x‖₊ ∂μ ≤ ∫⁻ x in s, ‖f x‖₊ ∂μ :=
begin
  let h_meas := Lp_meas.ae_strongly_measurable' (condexp_L2 ℝ hm f),
  let g := h_meas.some,
  have hg_meas : strongly_measurable[m] g, from h_meas.some_spec.1,
  have hg_eq : g =ᵐ[μ] condexp_L2 ℝ hm f, from h_meas.some_spec.2.symm,
  have hg_eq_restrict : g =ᵐ[μ.restrict s] condexp_L2 ℝ hm f, from ae_restrict_of_ae hg_eq,
  have hg_nnnorm_eq : (λ x, (‖g x‖₊ : ℝ≥0∞))
    =ᵐ[μ.restrict s] (λ x, (‖condexp_L2 ℝ hm f x‖₊ : ℝ≥0∞)),
  { refine hg_eq_restrict.mono (λ x hx, _),
    dsimp only,
    rw hx, },
  rw lintegral_congr_ae hg_nnnorm_eq.symm,
  refine lintegral_nnnorm_le_of_forall_fin_meas_integral_eq hm
    (Lp.strongly_measurable f) _ _ _ _ hs hμs,
  { exact integrable_on_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs, },
  { exact hg_meas, },
  { rw [integrable_on, integrable_congr hg_eq_restrict],
    exact integrable_on_condexp_L2_of_measure_ne_top hm hμs f, },
  { intros t ht hμt,
    rw ← integral_condexp_L2_eq_of_fin_meas_real f ht hμt.ne,
    exact set_integral_congr_ae (hm t ht) (hg_eq.mono (λ x hx _, hx)), },
end

lemma condexp_L2_ae_eq_zero_of_ae_eq_zero (hs : measurable_set[m] s) (hμs : μ s ≠ ∞)
  {f : Lp ℝ 2 μ} (hf : f =ᵐ[μ.restrict s] 0) :
  condexp_L2 ℝ hm f =ᵐ[μ.restrict s] 0 :=
begin
  suffices h_nnnorm_eq_zero : ∫⁻ x in s, ‖condexp_L2 ℝ hm f x‖₊ ∂μ = 0,
  { rw lintegral_eq_zero_iff at h_nnnorm_eq_zero,
    refine h_nnnorm_eq_zero.mono (λ x hx, _),
    dsimp only at hx,
    rw pi.zero_apply at hx ⊢,
    { rwa [ennreal.coe_eq_zero, nnnorm_eq_zero] at hx, },
    { refine measurable.coe_nnreal_ennreal (measurable.nnnorm _),
      rw Lp_meas_coe,
      exact (Lp.strongly_measurable _).measurable }, },
  refine le_antisymm _ (zero_le _),
  refine (lintegral_nnnorm_condexp_L2_le hs hμs f).trans (le_of_eq _),
  rw lintegral_eq_zero_iff,
  { refine hf.mono (λ x hx, _),
    dsimp only,
    rw hx,
    simp, },
  { exact (Lp.strongly_measurable _).ennnorm, },
end

lemma lintegral_nnnorm_condexp_L2_indicator_le_real
  (hs : measurable_set s) (hμs : μ s ≠ ∞) (ht : measurable_set[m] t) (hμt : μ t ≠ ∞) :
  ∫⁻ a in t, ‖condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)) a‖₊ ∂μ ≤ μ (s ∩ t) :=
begin
  refine (lintegral_nnnorm_condexp_L2_le ht hμt _).trans (le_of_eq _),
  have h_eq : ∫⁻ x in t, ‖(indicator_const_Lp 2 hs hμs (1 : ℝ)) x‖₊ ∂μ
    = ∫⁻ x in t, s.indicator (λ x, (1 : ℝ≥0∞)) x ∂μ,
  { refine lintegral_congr_ae (ae_restrict_of_ae _),
    refine (@indicator_const_Lp_coe_fn _ _ _ 2 _ _ _ hs hμs (1 : ℝ)).mono (λ x hx, _),
    rw hx,
    classical,
    simp_rw set.indicator_apply,
    split_ifs; simp, },
  rw [h_eq, lintegral_indicator _ hs, lintegral_const, measure.restrict_restrict hs],
  simp only [one_mul, set.univ_inter, measurable_set.univ, measure.restrict_apply],
end

end real

/-- `condexp_L2` commutes with taking inner products with constants. See the lemma
`condexp_L2_comp_continuous_linear_map` for a more general result about commuting with continuous
linear maps. -/
lemma condexp_L2_const_inner (hm : m ≤ m0) (f : Lp E 2 μ) (c : E) :
  condexp_L2 𝕜 hm (((Lp.mem_ℒp f).const_inner c).to_Lp (λ a, ⟪c, f a⟫))
    =ᵐ[μ] λ a, ⟪c, condexp_L2 𝕜 hm f a⟫ :=
begin
  rw Lp_meas_coe,
  have h_mem_Lp : mem_ℒp (λ a, ⟪c, condexp_L2 𝕜 hm f a⟫) 2 μ,
  { refine mem_ℒp.const_inner _ _, rw Lp_meas_coe, exact Lp.mem_ℒp _, },
  have h_eq : h_mem_Lp.to_Lp _ =ᵐ[μ] λ a, ⟪c, condexp_L2 𝕜 hm f a⟫, from h_mem_Lp.coe_fn_to_Lp,
  refine eventually_eq.trans _ h_eq,
  refine Lp.ae_eq_of_forall_set_integral_eq' 𝕜 hm _ _ two_ne_zero ennreal.coe_ne_top
    (λ s hs hμs, integrable_on_condexp_L2_of_measure_ne_top hm hμs.ne _) _ _ _ _,
  { intros s hs hμs,
    rw [integrable_on, integrable_congr (ae_restrict_of_ae h_eq)],
    exact (integrable_on_condexp_L2_of_measure_ne_top hm hμs.ne _).const_inner _, },
  { intros s hs hμs,
    rw [← Lp_meas_coe, integral_condexp_L2_eq_of_fin_meas_real _ hs hμs.ne,
      integral_congr_ae (ae_restrict_of_ae h_eq), Lp_meas_coe,
      ← L2.inner_indicator_const_Lp_eq_set_integral_inner 𝕜 ↑(condexp_L2 𝕜 hm f) (hm s hs) c hμs.ne,
      ← inner_condexp_L2_left_eq_right, condexp_L2_indicator_of_measurable,
      L2.inner_indicator_const_Lp_eq_set_integral_inner 𝕜 f (hm s hs) c hμs.ne,
      set_integral_congr_ae (hm s hs)
        ((mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).const_inner c)).mono (λ x hx hxs, hx))], },
  { rw ← Lp_meas_coe, exact Lp_meas.ae_strongly_measurable' _, },
  { refine ae_strongly_measurable'.congr _ h_eq.symm,
    exact (Lp_meas.ae_strongly_measurable' _).const_inner _, },
end

/-- `condexp_L2` verifies the equality of integrals defining the conditional expectation. -/
lemma integral_condexp_L2_eq (hm : m ≤ m0)
  (f : Lp E' 2 μ) (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) :
  ∫ x in s, condexp_L2 𝕜 hm f x ∂μ = ∫ x in s, f x ∂μ :=
begin
  rw [← sub_eq_zero, Lp_meas_coe, ← integral_sub'
      (integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs)
      (integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs)],
  refine integral_eq_zero_of_forall_integral_inner_eq_zero 𝕜 _ _ _,
  { rw integrable_congr (ae_restrict_of_ae (Lp.coe_fn_sub ↑(condexp_L2 𝕜 hm f) f).symm),
    exact integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs, },
  intro c,
  simp_rw [pi.sub_apply, inner_sub_right],
  rw integral_sub
    ((integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs).const_inner c)
    ((integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs).const_inner c),
  have h_ae_eq_f := mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).const_inner c),
  rw [← Lp_meas_coe, sub_eq_zero,
    ← set_integral_congr_ae (hm s hs) ((condexp_L2_const_inner hm f c).mono (λ x hx _, hx)),
    ← set_integral_congr_ae (hm s hs) (h_ae_eq_f.mono (λ x hx _, hx))],
  exact integral_condexp_L2_eq_of_fin_meas_real _ hs hμs,
end

variables {E'' 𝕜' : Type*} [is_R_or_C 𝕜'] [normed_add_comm_group E'']
  [inner_product_space 𝕜' E''] [complete_space E''] [normed_space ℝ E'']

variables (𝕜 𝕜')
lemma condexp_L2_comp_continuous_linear_map (hm : m ≤ m0) (T : E' →L[ℝ] E'') (f : α →₂[μ] E') :
  (condexp_L2 𝕜' hm (T.comp_Lp f) : α →₂[μ] E'') =ᵐ[μ] T.comp_Lp (condexp_L2 𝕜 hm f : α →₂[μ] E') :=
begin
  refine Lp.ae_eq_of_forall_set_integral_eq' 𝕜' hm _ _ two_ne_zero ennreal.coe_ne_top
    (λ s hs hμs, integrable_on_condexp_L2_of_measure_ne_top hm hμs.ne _)
    (λ s hs hμs, integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs.ne)
    _ _ _,
  { intros s hs hμs,
    rw [T.set_integral_comp_Lp _ (hm s hs),
      T.integral_comp_comm
        (integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs.ne),
      ← Lp_meas_coe, ← Lp_meas_coe, integral_condexp_L2_eq hm f hs hμs.ne,
      integral_condexp_L2_eq hm (T.comp_Lp f) hs hμs.ne, T.set_integral_comp_Lp _ (hm s hs),
      T.integral_comp_comm
        (integrable_on_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs.ne)], },
  { rw ← Lp_meas_coe, exact Lp_meas.ae_strongly_measurable' _, },
  { have h_coe := T.coe_fn_comp_Lp (condexp_L2 𝕜 hm f : α →₂[μ] E'),
    rw ← eventually_eq at h_coe,
    refine ae_strongly_measurable'.congr _ h_coe.symm,
    exact (Lp_meas.ae_strongly_measurable' (condexp_L2 𝕜 hm f)).continuous_comp T.continuous, },
end
variables {𝕜 𝕜'}

section condexp_L2_indicator

variables (𝕜)
lemma condexp_L2_indicator_ae_eq_smul (hm : m ≤ m0) (hs : measurable_set s) (hμs : μ s ≠ ∞)
  (x : E') :
  condexp_L2 𝕜 hm (indicator_const_Lp 2 hs hμs x)
    =ᵐ[μ] λ a, (condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)) a) • x :=
begin
  rw indicator_const_Lp_eq_to_span_singleton_comp_Lp hs hμs x,
  have h_comp := condexp_L2_comp_continuous_linear_map ℝ 𝕜 hm (to_span_singleton ℝ x)
    (indicator_const_Lp 2 hs hμs (1 : ℝ)),
  rw ← Lp_meas_coe at h_comp,
  refine h_comp.trans _,
  exact (to_span_singleton ℝ x).coe_fn_comp_Lp _,
end

lemma condexp_L2_indicator_eq_to_span_singleton_comp (hm : m ≤ m0) (hs : measurable_set s)
  (hμs : μ s ≠ ∞) (x : E') :
  (condexp_L2 𝕜 hm (indicator_const_Lp 2 hs hμs x) : α →₂[μ] E')
    = (to_span_singleton ℝ x).comp_Lp (condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ))) :=
begin
  ext1,
  rw ← Lp_meas_coe,
  refine (condexp_L2_indicator_ae_eq_smul 𝕜 hm hs hμs x).trans _,
  have h_comp := (to_span_singleton ℝ x).coe_fn_comp_Lp
    (condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)) : α →₂[μ] ℝ),
  rw ← eventually_eq at h_comp,
  refine eventually_eq.trans _ h_comp.symm,
  refine eventually_of_forall (λ y, _),
  refl,
end

variables {𝕜}

lemma set_lintegral_nnnorm_condexp_L2_indicator_le (hm : m ≤ m0) (hs : measurable_set s)
  (hμs : μ s ≠ ∞) (x : E') {t : set α} (ht : measurable_set[m] t) (hμt : μ t ≠ ∞) :
  ∫⁻ a in t, ‖condexp_L2 𝕜 hm (indicator_const_Lp 2 hs hμs x) a‖₊ ∂μ ≤ μ (s ∩ t) * ‖x‖₊ :=
calc ∫⁻ a in t, ‖condexp_L2 𝕜 hm (indicator_const_Lp 2 hs hμs x) a‖₊ ∂μ
    = ∫⁻ a in t, ‖(condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)) a) • x‖₊ ∂μ :
set_lintegral_congr_fun (hm t ht)
  ((condexp_L2_indicator_ae_eq_smul 𝕜 hm hs hμs x).mono (λ a ha hat, by rw ha))
... = ∫⁻ a in t, ‖condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)) a‖₊ ∂μ * ‖x‖₊ :
begin
  simp_rw [nnnorm_smul, ennreal.coe_mul],
  rw [lintegral_mul_const, Lp_meas_coe],
  exact (Lp.strongly_measurable _).ennnorm
end
... ≤ μ (s ∩ t) * ‖x‖₊ :
  mul_le_mul_right' (lintegral_nnnorm_condexp_L2_indicator_le_real hs hμs ht hμt) _

lemma lintegral_nnnorm_condexp_L2_indicator_le (hm : m ≤ m0) (hs : measurable_set s)
  (hμs : μ s ≠ ∞) (x : E') [sigma_finite (μ.trim hm)] :
  ∫⁻ a, ‖condexp_L2 𝕜 hm (indicator_const_Lp 2 hs hμs x) a‖₊ ∂μ ≤ μ s * ‖x‖₊ :=
begin
  refine lintegral_le_of_forall_fin_meas_le' hm (μ s * ‖x‖₊) _ (λ t ht hμt, _),
  { rw Lp_meas_coe,
    exact (Lp.ae_strongly_measurable _).ennnorm },
  refine (set_lintegral_nnnorm_condexp_L2_indicator_le hm hs hμs x ht hμt).trans _,
  exact mul_le_mul_right' (measure_mono (set.inter_subset_left _ _)) _
end

/-- If the measure `μ.trim hm` is sigma-finite, then the conditional expectation of a measurable set
with finite measure is integrable. -/
lemma integrable_condexp_L2_indicator (hm : m ≤ m0) [sigma_finite (μ.trim hm)]
  (hs : measurable_set s) (hμs : μ s ≠ ∞) (x : E') :
  integrable (condexp_L2 𝕜 hm (indicator_const_Lp 2 hs hμs x)) μ :=
begin
  refine integrable_of_forall_fin_meas_le' hm (μ s * ‖x‖₊)
    (ennreal.mul_lt_top hμs ennreal.coe_ne_top) _ _,
  { rw Lp_meas_coe, exact Lp.ae_strongly_measurable _, },
  { refine λ t ht hμt, (set_lintegral_nnnorm_condexp_L2_indicator_le hm hs hμs x ht hμt).trans _,
    exact mul_le_mul_right' (measure_mono (set.inter_subset_left _ _)) _, },
end

end condexp_L2_indicator

section condexp_ind_smul

variables [normed_space ℝ G] {hm : m ≤ m0}

/-- Conditional expectation of the indicator of a measurable set with finite measure, in L2. -/
noncomputable
def condexp_ind_smul (hm : m ≤ m0) (hs : measurable_set s) (hμs : μ s ≠ ∞) (x : G) : Lp G 2 μ :=
(to_span_singleton ℝ x).comp_LpL 2 μ (condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)))

lemma ae_strongly_measurable'_condexp_ind_smul
  (hm : m ≤ m0) (hs : measurable_set s) (hμs : μ s ≠ ∞) (x : G) :
  ae_strongly_measurable' m (condexp_ind_smul hm hs hμs x) μ :=
begin
  have h : ae_strongly_measurable' m (condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ))) μ,
    from ae_strongly_measurable'_condexp_L2 _ _,
  rw condexp_ind_smul,
  suffices : ae_strongly_measurable' m
    ((to_span_singleton ℝ x) ∘ (condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)))) μ,
  { refine ae_strongly_measurable'.congr this _,
    refine eventually_eq.trans _ (coe_fn_comp_LpL _ _).symm,
    rw Lp_meas_coe, },
  exact ae_strongly_measurable'.continuous_comp (to_span_singleton ℝ x).continuous h,
end

lemma condexp_ind_smul_add (hs : measurable_set s) (hμs : μ s ≠ ∞) (x y : G) :
  condexp_ind_smul hm hs hμs (x + y)
    = condexp_ind_smul hm hs hμs x + condexp_ind_smul hm hs hμs y :=
by { simp_rw [condexp_ind_smul], rw [to_span_singleton_add, add_comp_LpL, add_apply], }

lemma condexp_ind_smul_smul (hs : measurable_set s) (hμs : μ s ≠ ∞) (c : ℝ) (x : G) :
  condexp_ind_smul hm hs hμs (c • x) = c • condexp_ind_smul hm hs hμs x :=
by { simp_rw [condexp_ind_smul], rw [to_span_singleton_smul, smul_comp_LpL, smul_apply], }

lemma condexp_ind_smul_smul' [normed_space ℝ F] [smul_comm_class ℝ 𝕜 F] (hs : measurable_set s)
  (hμs : μ s ≠ ∞) (c : 𝕜) (x : F) :
  condexp_ind_smul hm hs hμs (c • x) = c • condexp_ind_smul hm hs hμs x :=
by rw [condexp_ind_smul, condexp_ind_smul, to_span_singleton_smul',
  (to_span_singleton ℝ x).smul_comp_LpL c, smul_apply]

lemma condexp_ind_smul_ae_eq_smul (hm : m ≤ m0) (hs : measurable_set s) (hμs : μ s ≠ ∞) (x : G) :
  condexp_ind_smul hm hs hμs x
    =ᵐ[μ] λ a, (condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)) a) • x :=
(to_span_singleton ℝ x).coe_fn_comp_LpL _

lemma set_lintegral_nnnorm_condexp_ind_smul_le (hm : m ≤ m0) (hs : measurable_set s)
  (hμs : μ s ≠ ∞) (x : G) {t : set α} (ht : measurable_set[m] t) (hμt : μ t ≠ ∞) :
  ∫⁻ a in t, ‖condexp_ind_smul hm hs hμs x a‖₊ ∂μ ≤ μ (s ∩ t) * ‖x‖₊ :=
calc ∫⁻ a in t, ‖condexp_ind_smul hm hs hμs x a‖₊ ∂μ
    = ∫⁻ a in t, ‖condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)) a • x‖₊ ∂μ :
set_lintegral_congr_fun (hm t ht)
  ((condexp_ind_smul_ae_eq_smul hm hs hμs x).mono (λ a ha hat, by rw ha ))
... = ∫⁻ a in t, ‖condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)) a‖₊ ∂μ * ‖x‖₊ :
begin
  simp_rw [nnnorm_smul, ennreal.coe_mul],
  rw [lintegral_mul_const, Lp_meas_coe],
  exact (Lp.strongly_measurable _).ennnorm
end
... ≤ μ (s ∩ t) * ‖x‖₊ :
  mul_le_mul_right' (lintegral_nnnorm_condexp_L2_indicator_le_real hs hμs ht hμt) _

lemma lintegral_nnnorm_condexp_ind_smul_le (hm : m ≤ m0) (hs : measurable_set s)
  (hμs : μ s ≠ ∞) (x : G) [sigma_finite (μ.trim hm)] :
  ∫⁻ a, ‖condexp_ind_smul hm hs hμs x a‖₊ ∂μ ≤ μ s * ‖x‖₊ :=
begin
  refine lintegral_le_of_forall_fin_meas_le' hm (μ s * ‖x‖₊) _ (λ t ht hμt, _),
  { exact (Lp.ae_strongly_measurable _).ennnorm },
  refine (set_lintegral_nnnorm_condexp_ind_smul_le hm hs hμs x ht hμt).trans _,
  exact mul_le_mul_right' (measure_mono (set.inter_subset_left _ _)) _
end

/-- If the measure `μ.trim hm` is sigma-finite, then the conditional expectation of a measurable set
with finite measure is integrable. -/
lemma integrable_condexp_ind_smul (hm : m ≤ m0) [sigma_finite (μ.trim hm)]
  (hs : measurable_set s) (hμs : μ s ≠ ∞) (x : G) :
  integrable (condexp_ind_smul hm hs hμs x) μ :=
begin
  refine integrable_of_forall_fin_meas_le' hm (μ s * ‖x‖₊)
    (ennreal.mul_lt_top hμs ennreal.coe_ne_top) _ _,
  { exact Lp.ae_strongly_measurable _, },
  { refine λ t ht hμt, (set_lintegral_nnnorm_condexp_ind_smul_le hm hs hμs x ht hμt).trans _,
    exact mul_le_mul_right' (measure_mono (set.inter_subset_left _ _)) _, },
end

lemma condexp_ind_smul_empty {x : G} :
  condexp_ind_smul hm measurable_set.empty
    ((@measure_empty _ _ μ).le.trans_lt ennreal.coe_lt_top).ne x = 0 :=
begin
  rw [condexp_ind_smul, indicator_const_empty],
  simp only [coe_fn_coe_base, submodule.coe_zero, continuous_linear_map.map_zero],
end

lemma set_integral_condexp_L2_indicator (hs : measurable_set[m] s) (ht : measurable_set t)
  (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) :
  ∫ x in s, (condexp_L2 ℝ hm (indicator_const_Lp 2 ht hμt (1 : ℝ))) x ∂μ = (μ (t ∩ s)).to_real :=
calc ∫ x in s, (condexp_L2 ℝ hm (indicator_const_Lp 2 ht hμt (1 : ℝ))) x ∂μ
    = ∫ x in s, indicator_const_Lp 2 ht hμt (1 : ℝ) x ∂μ :
      @integral_condexp_L2_eq
        α _ ℝ _ _ _ _ _ _ _ _ _ hm (indicator_const_Lp 2 ht hμt (1 : ℝ)) hs hμs
... = (μ (t ∩ s)).to_real • 1 : set_integral_indicator_const_Lp (hm s hs) ht hμt (1 : ℝ)
... = (μ (t ∩ s)).to_real : by rw [smul_eq_mul, mul_one]

lemma set_integral_condexp_ind_smul (hs : measurable_set[m] s) (ht : measurable_set t)
  (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) (x : G') :
  ∫ a in s, (condexp_ind_smul hm ht hμt x) a ∂μ = (μ (t ∩ s)).to_real • x :=
calc ∫ a in s, (condexp_ind_smul hm ht hμt x) a ∂μ
    = (∫ a in s, (condexp_L2 ℝ hm (indicator_const_Lp 2 ht hμt (1 : ℝ)) a • x) ∂μ) :
  set_integral_congr_ae (hm s hs) ((condexp_ind_smul_ae_eq_smul hm ht hμt x).mono (λ x hx hxs, hx))
... = (∫ a in s, condexp_L2 ℝ hm (indicator_const_Lp 2 ht hμt (1 : ℝ)) a ∂μ) • x :
  integral_smul_const _ x
... = (μ (t ∩ s)).to_real • x :
  by rw set_integral_condexp_L2_indicator hs ht hμs hμt

lemma condexp_L2_indicator_nonneg (hm : m ≤ m0) (hs : measurable_set s) (hμs : μ s ≠ ∞)
  [sigma_finite (μ.trim hm)] :
  0 ≤ᵐ[μ] condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)) :=
begin
  have h : ae_strongly_measurable' m (condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ))) μ,
    from ae_strongly_measurable'_condexp_L2 _ _,
  refine eventually_le.trans_eq _ h.ae_eq_mk.symm,
  refine @ae_le_of_ae_le_trim _ _ _ _ _ _ hm _ _ _,
  refine ae_nonneg_of_forall_set_integral_nonneg_of_sigma_finite _ _,
  { intros t ht hμt,
    refine @integrable.integrable_on _ _ m _ _ _ _ _,
    refine integrable.trim hm _ _,
    { rw integrable_congr h.ae_eq_mk.symm,
      exact integrable_condexp_L2_indicator hm hs hμs _, },
    { exact h.strongly_measurable_mk, }, },
  { intros t ht hμt,
    rw ← set_integral_trim hm h.strongly_measurable_mk ht,
    have h_ae : ∀ᵐ x ∂μ, x ∈ t → h.mk _ x = condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)) x,
    { filter_upwards [h.ae_eq_mk] with x hx,
      exact λ _, hx.symm, },
    rw [set_integral_congr_ae (hm t ht) h_ae,
      set_integral_condexp_L2_indicator ht hs ((le_trim hm).trans_lt hμt).ne hμs],
    exact ennreal.to_real_nonneg, },
end

lemma condexp_ind_smul_nonneg {E} [normed_lattice_add_comm_group E] [normed_space ℝ E]
  [ordered_smul ℝ E] [sigma_finite (μ.trim hm)]
  (hs : measurable_set s) (hμs : μ s ≠ ∞) (x : E) (hx : 0 ≤ x) :
  0 ≤ᵐ[μ] condexp_ind_smul hm hs hμs x :=
begin
  refine eventually_le.trans_eq _ (condexp_ind_smul_ae_eq_smul hm hs hμs x).symm,
  filter_upwards [condexp_L2_indicator_nonneg hm hs hμs] with a ha,
  exact smul_nonneg ha hx,
end

end condexp_ind_smul

end measure_theory
