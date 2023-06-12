/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import measure_theory.function.conditional_expectation.unique

/-! # Conditional expectation

We build the conditional expectation of an integrable function `f` with value in a Banach space
with respect to a measure `μ` (defined on a measurable space structure `m0`) and a measurable space
structure `m` with `hm : m ≤ m0` (a sub-sigma-algebra). This is an `m`-strongly measurable
function `μ[f|hm]` which is integrable and verifies `∫ x in s, μ[f|hm] x ∂μ = ∫ x in s, f x ∂μ`
for all `m`-measurable sets `s`. It is unique as an element of `L¹`.

The construction is done in four steps:
* Define the conditional expectation of an `L²` function, as an element of `L²`. This is the
  orthogonal projection on the subspace of almost everywhere `m`-measurable functions.
* Show that the conditional expectation of the indicator of a measurable set with finite measure
  is integrable and define a map `set α → (E →L[ℝ] (α →₁[μ] E))` which to a set associates a linear
  map. That linear map sends `x ∈ E` to the conditional expectation of the indicator of the set
  with value `x`.
* Extend that map to `condexp_L1_clm : (α →₁[μ] E) →L[ℝ] (α →₁[μ] E)`. This is done using the same
  construction as the Bochner integral (see the file `measure_theory/integral/set_to_L1`).
* Define the conditional expectation of a function `f : α → E`, which is an integrable function
  `α → E` equal to 0 if `f` is not integrable, and equal to an `m`-measurable representative of
  `condexp_L1_clm` applied to `[f]`, the equivalence class of `f` in `L¹`.

## Main results

The conditional expectation and its properties

* `condexp (m : measurable_space α) (μ : measure α) (f : α → E)`: conditional expectation of `f`
  with respect to `m`.
* `integrable_condexp` : `condexp` is integrable.
* `strongly_measurable_condexp` : `condexp` is `m`-strongly-measurable.
* `set_integral_condexp (hf : integrable f μ) (hs : measurable_set[m] s)` : if `m ≤ m0` (the
  σ-algebra over which the measure is defined), then the conditional expectation verifies
  `∫ x in s, condexp m μ f x ∂μ = ∫ x in s, f x ∂μ` for any `m`-measurable set `s`.

While `condexp` is function-valued, we also define `condexp_L1` with value in `L1` and a continuous
linear map `condexp_L1_clm` from `L1` to `L1`. `condexp` should be used in most cases.

Uniqueness of the conditional expectation

* `ae_eq_condexp_of_forall_set_integral_eq`: an a.e. `m`-measurable function which verifies the
  equality of integrals is a.e. equal to `condexp`.

## Notations

For a measure `μ` defined on a measurable space structure `m0`, another measurable space structure
`m` with `hm : m ≤ m0` (a sub-σ-algebra) and a function `f`, we define the notation
* `μ[f|m] = condexp m μ f`.

## Implementation notes

Most of the results in this file are valid for a complete real normed space `F`.
However, some lemmas also use `𝕜 : is_R_or_C`:
* `condexp_L2` is defined only for an `inner_product_space` for now, and we use `𝕜` for its field.
* results about scalar multiplication are stated not only for `ℝ` but also for `𝕜` if we happen to
  have `normed_space 𝕜 F`.

## Tags

conditional expectation, conditional expected value

-/

noncomputable theory
open topological_space measure_theory.Lp filter continuous_linear_map
open_locale nnreal ennreal topology big_operators measure_theory

namespace measure_theory

variables {α β γ E E' F F' G G' H 𝕜 : Type*} {p : ℝ≥0∞}
  [is_R_or_C 𝕜] -- 𝕜 for ℝ or ℂ
  [topological_space β] -- β for a generic topological space
  -- E for an inner product space
  [normed_add_comm_group E] [inner_product_space 𝕜 E]
  -- E' for an inner product space on which we compute integrals
  [normed_add_comm_group E'] [inner_product_space 𝕜 E']
  [complete_space E'] [normed_space ℝ E']
  -- F for a Lp submodule
  [normed_add_comm_group F] [normed_space 𝕜 F]
  -- F' for integrals on a Lp submodule
  [normed_add_comm_group F'] [normed_space 𝕜 F'] [normed_space ℝ F'] [complete_space F']
  -- G for a Lp add_subgroup
  [normed_add_comm_group G]
  -- G' for integrals on a Lp add_subgroup
  [normed_add_comm_group G'] [normed_space ℝ G'] [complete_space G']
  -- H for a normed group (hypotheses of mem_ℒp)
  [normed_add_comm_group H]

/-! ## Conditional expectation in L2

We define a conditional expectation in `L2`: it is the orthogonal projection on the subspace
`Lp_meas`. -/

section condexp_L2

variables [complete_space E] {m m0 : measurable_space α} {μ : measure α}
  {s t : set α}

local notation `⟪`x`, `y`⟫` := @inner 𝕜 E _ x y
local notation `⟪`x`, `y`⟫₂` := @inner 𝕜 (α →₂[μ] E) _ x y

variables (𝕜)
/-- Conditional expectation of a function in L2 with respect to a sigma-algebra -/
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

end condexp_L2

section condexp_ind

/-! ## Conditional expectation of an indicator as a continuous linear map.

The goal of this section is to build
`condexp_ind (hm : m ≤ m0) (μ : measure α) (s : set s) : G →L[ℝ] α →₁[μ] G`, which
takes `x : G` to the conditional expectation of the indicator of the set `s` with value `x`,
seen as an element of `α →₁[μ] G`.
-/

variables {m m0 : measurable_space α} {μ : measure α} {s t : set α} [normed_space ℝ G]

section condexp_ind_L1_fin

/-- Conditional expectation of the indicator of a measurable set with finite measure,
as a function in L1. -/
def condexp_ind_L1_fin (hm : m ≤ m0) [sigma_finite (μ.trim hm)] (hs : measurable_set s)
  (hμs : μ s ≠ ∞) (x : G) : α →₁[μ] G :=
(integrable_condexp_ind_smul hm hs hμs x).to_L1 _

lemma condexp_ind_L1_fin_ae_eq_condexp_ind_smul (hm : m ≤ m0) [sigma_finite (μ.trim hm)]
  (hs : measurable_set s) (hμs : μ s ≠ ∞) (x : G) :
  condexp_ind_L1_fin hm hs hμs x =ᵐ[μ] condexp_ind_smul hm hs hμs x :=
(integrable_condexp_ind_smul hm hs hμs x).coe_fn_to_L1

variables {hm : m ≤ m0} [sigma_finite (μ.trim hm)]

lemma condexp_ind_L1_fin_add (hs : measurable_set s) (hμs : μ s ≠ ∞) (x y : G) :
  condexp_ind_L1_fin hm hs hμs (x + y)
    = condexp_ind_L1_fin hm hs hμs x + condexp_ind_L1_fin hm hs hμs y :=
begin
  ext1,
  refine (mem_ℒp.coe_fn_to_Lp _).trans _,
  refine eventually_eq.trans _ (Lp.coe_fn_add _ _).symm,
  refine eventually_eq.trans _
    (eventually_eq.add (mem_ℒp.coe_fn_to_Lp _).symm (mem_ℒp.coe_fn_to_Lp _).symm),
  rw condexp_ind_smul_add,
  refine (Lp.coe_fn_add _ _).trans (eventually_of_forall (λ a, _)),
  refl,
end

lemma condexp_ind_L1_fin_smul (hs : measurable_set s) (hμs : μ s ≠ ∞) (c : ℝ) (x : G) :
  condexp_ind_L1_fin hm hs hμs (c • x) = c • condexp_ind_L1_fin hm hs hμs x :=
begin
  ext1,
  refine (mem_ℒp.coe_fn_to_Lp _).trans _,
  refine eventually_eq.trans _ (Lp.coe_fn_smul _ _).symm,
  rw condexp_ind_smul_smul hs hμs c x,
  refine (Lp.coe_fn_smul _ _).trans _,
  refine (condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm hs hμs x).mono (λ y hy, _),
  rw [pi.smul_apply, pi.smul_apply, hy],
end

lemma condexp_ind_L1_fin_smul' [normed_space ℝ F] [smul_comm_class ℝ 𝕜 F]
  (hs : measurable_set s) (hμs : μ s ≠ ∞) (c : 𝕜) (x : F) :
  condexp_ind_L1_fin hm hs hμs (c • x) = c • condexp_ind_L1_fin hm hs hμs x :=
begin
  ext1,
  refine (mem_ℒp.coe_fn_to_Lp _).trans _,
  refine eventually_eq.trans _ (Lp.coe_fn_smul _ _).symm,
  rw condexp_ind_smul_smul' hs hμs c x,
  refine (Lp.coe_fn_smul _ _).trans _,
  refine (condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm hs hμs x).mono (λ y hy, _),
  rw [pi.smul_apply, pi.smul_apply, hy],
end

lemma norm_condexp_ind_L1_fin_le (hs : measurable_set s) (hμs : μ s ≠ ∞) (x : G) :
  ‖condexp_ind_L1_fin hm hs hμs x‖ ≤ (μ s).to_real * ‖x‖ :=
begin
  have : 0 ≤ ∫ (a : α), ‖condexp_ind_L1_fin hm hs hμs x a‖ ∂μ,
    from integral_nonneg (λ a, norm_nonneg _),
  rw [L1.norm_eq_integral_norm, ← ennreal.to_real_of_real (norm_nonneg x), ← ennreal.to_real_mul,
    ← ennreal.to_real_of_real this, ennreal.to_real_le_to_real ennreal.of_real_ne_top
      (ennreal.mul_ne_top hμs ennreal.of_real_ne_top),
    of_real_integral_norm_eq_lintegral_nnnorm],
  swap, { rw [← mem_ℒp_one_iff_integrable], exact Lp.mem_ℒp _, },
  have h_eq : ∫⁻ a, ‖condexp_ind_L1_fin hm hs hμs x a‖₊ ∂μ
    = ∫⁻ a, ‖condexp_ind_smul hm hs hμs x a‖₊ ∂μ,
  { refine lintegral_congr_ae _,
    refine (condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm hs hμs x).mono (λ z hz, _),
    dsimp only,
    rw hz, },
  rw [h_eq, of_real_norm_eq_coe_nnnorm],
  exact lintegral_nnnorm_condexp_ind_smul_le hm hs hμs x,
end

lemma condexp_ind_L1_fin_disjoint_union (hs : measurable_set s) (ht : measurable_set t)
  (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) (hst : s ∩ t = ∅) (x : G) :
  condexp_ind_L1_fin hm (hs.union ht) ((measure_union_le s t).trans_lt
    (lt_top_iff_ne_top.mpr (ennreal.add_ne_top.mpr ⟨hμs, hμt⟩))).ne x
  = condexp_ind_L1_fin hm hs hμs x + condexp_ind_L1_fin hm ht hμt x :=
begin
  ext1,
  have hμst := ((measure_union_le s t).trans_lt
    (lt_top_iff_ne_top.mpr (ennreal.add_ne_top.mpr ⟨hμs, hμt⟩))).ne,
  refine (condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm (hs.union ht) hμst x).trans _,
  refine eventually_eq.trans _ (Lp.coe_fn_add _ _).symm,
  have hs_eq := condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm hs hμs x,
  have ht_eq := condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm ht hμt x,
  refine eventually_eq.trans _ (eventually_eq.add hs_eq.symm ht_eq.symm),
  rw condexp_ind_smul,
  rw indicator_const_Lp_disjoint_union hs ht hμs hμt hst (1 : ℝ),
  rw (condexp_L2 ℝ hm).map_add,
  push_cast,
  rw ((to_span_singleton ℝ x).comp_LpL 2 μ).map_add,
  refine (Lp.coe_fn_add _ _).trans _,
  refine eventually_of_forall (λ y, _),
  refl,
end

end condexp_ind_L1_fin

open_locale classical

section condexp_ind_L1

/-- Conditional expectation of the indicator of a set, as a function in L1. Its value for sets
which are not both measurable and of finite measure is not used: we set it to 0. -/
def condexp_ind_L1 {m m0 : measurable_space α} (hm : m ≤ m0) (μ : measure α) (s : set α)
  [sigma_finite (μ.trim hm)] (x : G) :
  α →₁[μ] G :=
if hs : measurable_set s ∧ μ s ≠ ∞ then condexp_ind_L1_fin hm hs.1 hs.2 x else 0

variables {hm : m ≤ m0} [sigma_finite (μ.trim hm)]

lemma condexp_ind_L1_of_measurable_set_of_measure_ne_top (hs : measurable_set s) (hμs : μ s ≠ ∞)
  (x : G) :
  condexp_ind_L1 hm μ s x = condexp_ind_L1_fin hm hs hμs x :=
by simp only [condexp_ind_L1, and.intro hs hμs, dif_pos, ne.def, not_false_iff, and_self]

lemma condexp_ind_L1_of_measure_eq_top (hμs : μ s = ∞) (x : G) :
  condexp_ind_L1 hm μ s x = 0 :=
by simp only [condexp_ind_L1, hμs, eq_self_iff_true, not_true, ne.def, dif_neg, not_false_iff,
  and_false]

lemma condexp_ind_L1_of_not_measurable_set (hs : ¬ measurable_set s) (x : G) :
  condexp_ind_L1 hm μ s x = 0 :=
by simp only [condexp_ind_L1, hs, dif_neg, not_false_iff, false_and]

lemma condexp_ind_L1_add (x y : G) :
  condexp_ind_L1 hm μ s (x + y) = condexp_ind_L1 hm μ s x + condexp_ind_L1 hm μ s y :=
begin
  by_cases hs : measurable_set s,
  swap, {simp_rw condexp_ind_L1_of_not_measurable_set hs, rw zero_add, },
  by_cases hμs : μ s = ∞,
  { simp_rw condexp_ind_L1_of_measure_eq_top hμs, rw zero_add, },
  { simp_rw condexp_ind_L1_of_measurable_set_of_measure_ne_top hs hμs,
    exact condexp_ind_L1_fin_add hs hμs x y, },
end

lemma condexp_ind_L1_smul (c : ℝ) (x : G) :
  condexp_ind_L1 hm μ s (c • x) = c • condexp_ind_L1 hm μ s x :=
begin
  by_cases hs : measurable_set s,
  swap, {simp_rw condexp_ind_L1_of_not_measurable_set hs, rw smul_zero, },
  by_cases hμs : μ s = ∞,
  { simp_rw condexp_ind_L1_of_measure_eq_top hμs, rw smul_zero, },
  { simp_rw condexp_ind_L1_of_measurable_set_of_measure_ne_top hs hμs,
    exact condexp_ind_L1_fin_smul hs hμs c x, },
end

lemma condexp_ind_L1_smul' [normed_space ℝ F] [smul_comm_class ℝ 𝕜 F] (c : 𝕜) (x : F) :
  condexp_ind_L1 hm μ s (c • x) = c • condexp_ind_L1 hm μ s x :=
begin
  by_cases hs : measurable_set s,
  swap, {simp_rw condexp_ind_L1_of_not_measurable_set hs, rw smul_zero, },
  by_cases hμs : μ s = ∞,
  { simp_rw condexp_ind_L1_of_measure_eq_top hμs, rw smul_zero, },
  { simp_rw condexp_ind_L1_of_measurable_set_of_measure_ne_top hs hμs,
    exact condexp_ind_L1_fin_smul' hs hμs c x, },
end

lemma norm_condexp_ind_L1_le (x : G) :
  ‖condexp_ind_L1 hm μ s x‖ ≤ (μ s).to_real * ‖x‖ :=
begin
  by_cases hs : measurable_set s,
  swap, {simp_rw condexp_ind_L1_of_not_measurable_set hs, rw Lp.norm_zero,
    exact mul_nonneg ennreal.to_real_nonneg (norm_nonneg _), },
  by_cases hμs : μ s = ∞,
  { rw [condexp_ind_L1_of_measure_eq_top hμs x, Lp.norm_zero],
    exact mul_nonneg ennreal.to_real_nonneg (norm_nonneg _), },
  { rw condexp_ind_L1_of_measurable_set_of_measure_ne_top hs hμs x,
    exact norm_condexp_ind_L1_fin_le hs hμs x, },
end

lemma continuous_condexp_ind_L1 : continuous (λ x : G, condexp_ind_L1 hm μ s x) :=
continuous_of_linear_of_bound condexp_ind_L1_add condexp_ind_L1_smul norm_condexp_ind_L1_le

lemma condexp_ind_L1_disjoint_union (hs : measurable_set s) (ht : measurable_set t)
  (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) (hst : s ∩ t = ∅) (x : G) :
  condexp_ind_L1 hm μ (s ∪ t) x = condexp_ind_L1 hm μ s x + condexp_ind_L1 hm μ t x :=
begin
  have hμst : μ (s ∪ t) ≠ ∞, from ((measure_union_le s t).trans_lt
    (lt_top_iff_ne_top.mpr (ennreal.add_ne_top.mpr ⟨hμs, hμt⟩))).ne,
  rw [condexp_ind_L1_of_measurable_set_of_measure_ne_top hs hμs x,
    condexp_ind_L1_of_measurable_set_of_measure_ne_top ht hμt x,
    condexp_ind_L1_of_measurable_set_of_measure_ne_top (hs.union ht) hμst x],
  exact condexp_ind_L1_fin_disjoint_union hs ht hμs hμt hst x,
end

end condexp_ind_L1

/-- Conditional expectation of the indicator of a set, as a linear map from `G` to L1. -/
def condexp_ind {m m0 : measurable_space α} (hm : m ≤ m0) (μ : measure α) [sigma_finite (μ.trim hm)]
  (s : set α) : G →L[ℝ] α →₁[μ] G :=
{ to_fun    := condexp_ind_L1 hm μ s,
  map_add'  := condexp_ind_L1_add,
  map_smul' := condexp_ind_L1_smul,
  cont      := continuous_condexp_ind_L1, }

lemma condexp_ind_ae_eq_condexp_ind_smul (hm : m ≤ m0) [sigma_finite (μ.trim hm)]
  (hs : measurable_set s) (hμs : μ s ≠ ∞) (x : G) :
  condexp_ind hm μ s x =ᵐ[μ] condexp_ind_smul hm hs hμs x :=
begin
  refine eventually_eq.trans _ (condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm hs hμs x),
  simp [condexp_ind, condexp_ind_L1, hs, hμs],
end

variables {hm : m ≤ m0} [sigma_finite (μ.trim hm)]

lemma ae_strongly_measurable'_condexp_ind (hs : measurable_set s) (hμs : μ s ≠ ∞) (x : G) :
  ae_strongly_measurable' m (condexp_ind hm μ s x) μ :=
ae_strongly_measurable'.congr (ae_strongly_measurable'_condexp_ind_smul hm hs hμs x)
  (condexp_ind_ae_eq_condexp_ind_smul hm hs hμs x).symm

@[simp] lemma condexp_ind_empty : condexp_ind hm μ ∅ = (0 : G →L[ℝ] α →₁[μ] G) :=
begin
  ext1,
  ext1,
  refine (condexp_ind_ae_eq_condexp_ind_smul hm measurable_set.empty (by simp) x).trans _,
  rw condexp_ind_smul_empty,
  refine (Lp.coe_fn_zero G 2 μ).trans _,
  refine eventually_eq.trans _ (Lp.coe_fn_zero G 1 μ).symm,
  refl,
end

lemma condexp_ind_smul' [normed_space ℝ F] [smul_comm_class ℝ 𝕜 F] (c : 𝕜) (x : F) :
  condexp_ind hm μ s (c • x) = c • condexp_ind hm μ s x :=
condexp_ind_L1_smul' c x

lemma norm_condexp_ind_apply_le (x : G) : ‖condexp_ind hm μ s x‖ ≤ (μ s).to_real * ‖x‖ :=
norm_condexp_ind_L1_le x

lemma norm_condexp_ind_le : ‖(condexp_ind hm μ s : G →L[ℝ] α →₁[μ] G)‖ ≤ (μ s).to_real :=
continuous_linear_map.op_norm_le_bound _ ennreal.to_real_nonneg norm_condexp_ind_apply_le

lemma condexp_ind_disjoint_union_apply (hs : measurable_set s) (ht : measurable_set t)
  (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) (hst : s ∩ t = ∅) (x : G) :
  condexp_ind hm μ (s ∪ t) x = condexp_ind hm μ s x + condexp_ind hm μ t x :=
condexp_ind_L1_disjoint_union hs ht hμs hμt hst x

lemma condexp_ind_disjoint_union (hs : measurable_set s) (ht : measurable_set t) (hμs : μ s ≠ ∞)
  (hμt : μ t ≠ ∞) (hst : s ∩ t = ∅) :
  (condexp_ind hm μ (s ∪ t) : G →L[ℝ] α →₁[μ] G) = condexp_ind hm μ s + condexp_ind hm μ t :=
by { ext1, push_cast, exact condexp_ind_disjoint_union_apply hs ht hμs hμt hst x, }

variables (G)

lemma dominated_fin_meas_additive_condexp_ind (hm : m ≤ m0) (μ : measure α)
  [sigma_finite (μ.trim hm)] :
  dominated_fin_meas_additive μ (condexp_ind hm μ : set α → G →L[ℝ] α →₁[μ] G) 1 :=
⟨λ s t, condexp_ind_disjoint_union, λ s _ _, norm_condexp_ind_le.trans (one_mul _).symm.le⟩

variables {G}

lemma set_integral_condexp_ind (hs : measurable_set[m] s) (ht : measurable_set t) (hμs : μ s ≠ ∞)
  (hμt : μ t ≠ ∞) (x : G') :
  ∫ a in s, condexp_ind hm μ t x a ∂μ = (μ (t ∩ s)).to_real • x :=
calc
∫ a in s, condexp_ind hm μ t x a ∂μ = ∫ a in s, condexp_ind_smul hm ht hμt x a ∂μ :
  set_integral_congr_ae (hm s hs)
    ((condexp_ind_ae_eq_condexp_ind_smul hm ht hμt x).mono (λ x hx hxs, hx))
... = (μ (t ∩ s)).to_real • x : set_integral_condexp_ind_smul hs ht hμs hμt x

lemma condexp_ind_of_measurable (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) (c : G) :
  condexp_ind hm μ s c = indicator_const_Lp 1 (hm s hs) hμs c :=
begin
  ext1,
  refine eventually_eq.trans _ indicator_const_Lp_coe_fn.symm,
  refine (condexp_ind_ae_eq_condexp_ind_smul hm (hm s hs) hμs c).trans _,
  refine (condexp_ind_smul_ae_eq_smul hm (hm s hs) hμs c).trans _,
  rw [Lp_meas_coe, condexp_L2_indicator_of_measurable hm hs hμs (1 : ℝ)],
  refine (@indicator_const_Lp_coe_fn α _ _ 2 μ _ s (hm s hs) hμs (1 : ℝ)).mono (λ x hx, _),
  dsimp only,
  rw hx,
  by_cases hx_mem : x ∈ s; simp [hx_mem],
end

lemma condexp_ind_nonneg {E} [normed_lattice_add_comm_group E] [normed_space ℝ E] [ordered_smul ℝ E]
  (hs : measurable_set s) (hμs : μ s ≠ ∞) (x : E) (hx : 0 ≤ x) :
  0 ≤ condexp_ind hm μ s x :=
begin
  rw ← coe_fn_le,
  refine eventually_le.trans_eq _ (condexp_ind_ae_eq_condexp_ind_smul hm hs hμs x).symm,
  exact (coe_fn_zero E 1 μ).trans_le (condexp_ind_smul_nonneg hs hμs x hx),
end

end condexp_ind

section condexp_L1

variables {m m0 : measurable_space α} {μ : measure α}
  {hm : m ≤ m0} [sigma_finite (μ.trim hm)] {f g : α → F'} {s : set α}

/-- Conditional expectation of a function as a linear map from `α →₁[μ] F'` to itself. -/
def condexp_L1_clm (hm : m ≤ m0) (μ : measure α) [sigma_finite (μ.trim hm)] :
  (α →₁[μ] F') →L[ℝ] α →₁[μ] F' :=
L1.set_to_L1 (dominated_fin_meas_additive_condexp_ind F' hm μ)

lemma condexp_L1_clm_smul (c : 𝕜) (f : α →₁[μ] F') :
  condexp_L1_clm hm μ (c • f) = c • condexp_L1_clm hm μ f :=
L1.set_to_L1_smul (dominated_fin_meas_additive_condexp_ind F' hm μ)
  (λ c s x, condexp_ind_smul' c x) c f

lemma condexp_L1_clm_indicator_const_Lp (hs : measurable_set s) (hμs : μ s ≠ ∞) (x : F') :
  (condexp_L1_clm hm μ) (indicator_const_Lp 1 hs hμs x) = condexp_ind hm μ s x :=
L1.set_to_L1_indicator_const_Lp (dominated_fin_meas_additive_condexp_ind F' hm μ) hs hμs x

lemma condexp_L1_clm_indicator_const (hs : measurable_set s) (hμs : μ s ≠ ∞) (x : F') :
  (condexp_L1_clm hm μ) ↑(simple_func.indicator_const 1 hs hμs x) = condexp_ind hm μ s x :=
by { rw Lp.simple_func.coe_indicator_const, exact condexp_L1_clm_indicator_const_Lp hs hμs x, }

/-- Auxiliary lemma used in the proof of `set_integral_condexp_L1_clm`. -/
lemma set_integral_condexp_L1_clm_of_measure_ne_top (f : α →₁[μ] F') (hs : measurable_set[m] s)
  (hμs : μ s ≠ ∞) :
  ∫ x in s, condexp_L1_clm hm μ f x ∂μ = ∫ x in s, f x ∂μ :=
begin
  refine Lp.induction ennreal.one_ne_top
    (λ f : α →₁[μ] F', ∫ x in s, condexp_L1_clm hm μ f x ∂μ = ∫ x in s, f x ∂μ)
  _ _ (is_closed_eq _ _) f,
  { intros x t ht hμt,
    simp_rw condexp_L1_clm_indicator_const ht hμt.ne x,
    rw [Lp.simple_func.coe_indicator_const, set_integral_indicator_const_Lp (hm _ hs)],
    exact set_integral_condexp_ind hs ht hμs hμt.ne x, },
  { intros f g hf_Lp hg_Lp hfg_disj hf hg,
    simp_rw (condexp_L1_clm hm μ).map_add,
    rw set_integral_congr_ae (hm s hs) ((Lp.coe_fn_add (condexp_L1_clm hm μ (hf_Lp.to_Lp f))
      (condexp_L1_clm hm μ (hg_Lp.to_Lp g))).mono (λ x hx hxs, hx)),
    rw set_integral_congr_ae (hm s hs) ((Lp.coe_fn_add (hf_Lp.to_Lp f) (hg_Lp.to_Lp g)).mono
      (λ x hx hxs, hx)),
    simp_rw pi.add_apply,
    rw [integral_add (L1.integrable_coe_fn _).integrable_on (L1.integrable_coe_fn _).integrable_on,
      integral_add (L1.integrable_coe_fn _).integrable_on (L1.integrable_coe_fn _).integrable_on,
      hf, hg], },
  { exact (continuous_set_integral s).comp (condexp_L1_clm hm μ).continuous, },
  { exact continuous_set_integral s, },
end

/-- The integral of the conditional expectation `condexp_L1_clm` over an `m`-measurable set is equal
to the integral of `f` on that set. See also `set_integral_condexp`, the similar statement for
`condexp`. -/
lemma set_integral_condexp_L1_clm (f : α →₁[μ] F') (hs : measurable_set[m] s) :
  ∫ x in s, condexp_L1_clm hm μ f x ∂μ = ∫ x in s, f x ∂μ :=
begin
  let S := spanning_sets (μ.trim hm),
  have hS_meas : ∀ i, measurable_set[m] (S i) := measurable_spanning_sets (μ.trim hm),
  have hS_meas0 : ∀ i, measurable_set (S i) := λ i, hm _ (hS_meas i),
  have hs_eq : s = ⋃ i, S i ∩ s,
  { simp_rw set.inter_comm,
    rw [← set.inter_Union, (Union_spanning_sets (μ.trim hm)), set.inter_univ], },
  have hS_finite : ∀ i, μ (S i ∩ s) < ∞,
  { refine λ i, (measure_mono (set.inter_subset_left _ _)).trans_lt _,
    have hS_finite_trim := measure_spanning_sets_lt_top (μ.trim hm) i,
    rwa trim_measurable_set_eq hm (hS_meas i) at hS_finite_trim, },
  have h_mono : monotone (λ i, (S i) ∩ s),
  { intros i j hij x,
    simp_rw set.mem_inter_iff,
    exact λ h, ⟨monotone_spanning_sets (μ.trim hm) hij h.1, h.2⟩, },
  have h_eq_forall : (λ i, ∫ x in (S i) ∩ s, condexp_L1_clm hm μ f x ∂μ)
      = λ i, ∫ x in (S i) ∩ s, f x ∂μ,
    from funext (λ i, set_integral_condexp_L1_clm_of_measure_ne_top f
      (@measurable_set.inter α m _ _ (hS_meas i) hs) (hS_finite i).ne),
  have h_right : tendsto (λ i, ∫ x in (S i) ∩ s, f x ∂μ) at_top (𝓝 (∫ x in s, f x ∂μ)),
  { have h := tendsto_set_integral_of_monotone (λ i, (hS_meas0 i).inter (hm s hs)) h_mono
      (L1.integrable_coe_fn f).integrable_on,
    rwa ← hs_eq at h, },
  have h_left : tendsto (λ i, ∫ x in (S i) ∩ s, condexp_L1_clm hm μ f x ∂μ) at_top
    (𝓝 (∫ x in s, condexp_L1_clm hm μ f x ∂μ)),
  { have h := tendsto_set_integral_of_monotone (λ i, (hS_meas0 i).inter (hm s hs))
      h_mono (L1.integrable_coe_fn (condexp_L1_clm hm μ f)).integrable_on,
    rwa ← hs_eq at h, },
  rw h_eq_forall at h_left,
  exact tendsto_nhds_unique h_left h_right,
end

lemma ae_strongly_measurable'_condexp_L1_clm (f : α →₁[μ] F') :
  ae_strongly_measurable' m (condexp_L1_clm hm μ f) μ :=
begin
  refine Lp.induction ennreal.one_ne_top
    (λ f : α →₁[μ] F', ae_strongly_measurable' m (condexp_L1_clm hm μ f) μ)
    _ _ _ f,
  { intros c s hs hμs,
    rw condexp_L1_clm_indicator_const hs hμs.ne c,
    exact ae_strongly_measurable'_condexp_ind hs hμs.ne c, },
  { intros f g hf hg h_disj hfm hgm,
    rw (condexp_L1_clm hm μ).map_add,
    refine ae_strongly_measurable'.congr _ (coe_fn_add _ _).symm,
    exact ae_strongly_measurable'.add hfm hgm, },
  { have : {f : Lp F' 1 μ | ae_strongly_measurable' m (condexp_L1_clm hm μ f) μ}
        = (condexp_L1_clm hm μ) ⁻¹' {f | ae_strongly_measurable' m f μ},
      by refl,
    rw this,
    refine is_closed.preimage (condexp_L1_clm hm μ).continuous _,
    exact is_closed_ae_strongly_measurable' hm, },
end

lemma condexp_L1_clm_Lp_meas (f : Lp_meas F' ℝ m 1 μ) :
  condexp_L1_clm hm μ (f : α →₁[μ] F') = ↑f :=
begin
  let g := Lp_meas_to_Lp_trim_lie F' ℝ 1 μ hm f,
  have hfg : f = (Lp_meas_to_Lp_trim_lie F' ℝ 1 μ hm).symm g,
    by simp only [linear_isometry_equiv.symm_apply_apply],
  rw hfg,
  refine @Lp.induction α F' m _ 1 (μ.trim hm) _ ennreal.coe_ne_top
    (λ g : α →₁[μ.trim hm] F',
      condexp_L1_clm hm μ ((Lp_meas_to_Lp_trim_lie F' ℝ 1 μ hm).symm g : α →₁[μ] F')
        = ↑((Lp_meas_to_Lp_trim_lie F' ℝ 1 μ hm).symm g)) _ _ _ g,
  { intros c s hs hμs,
    rw [Lp.simple_func.coe_indicator_const, Lp_meas_to_Lp_trim_lie_symm_indicator hs hμs.ne c,
      condexp_L1_clm_indicator_const_Lp],
    exact condexp_ind_of_measurable hs ((le_trim hm).trans_lt hμs).ne c, },
  { intros f g hf hg hfg_disj hf_eq hg_eq,
    rw linear_isometry_equiv.map_add,
    push_cast,
    rw [map_add, hf_eq, hg_eq], },
  { refine is_closed_eq _ _,
    { refine (condexp_L1_clm hm μ).continuous.comp (continuous_induced_dom.comp _),
      exact linear_isometry_equiv.continuous _, },
    { refine continuous_induced_dom.comp _,
      exact linear_isometry_equiv.continuous _, }, },
end

lemma condexp_L1_clm_of_ae_strongly_measurable'
  (f : α →₁[μ] F') (hfm : ae_strongly_measurable' m f μ) :
  condexp_L1_clm hm μ f = f :=
condexp_L1_clm_Lp_meas (⟨f, hfm⟩ : Lp_meas F' ℝ m 1 μ)

/-- Conditional expectation of a function, in L1. Its value is 0 if the function is not
integrable. The function-valued `condexp` should be used instead in most cases. -/
def condexp_L1 (hm : m ≤ m0) (μ : measure α) [sigma_finite (μ.trim hm)] (f : α → F') : α →₁[μ] F' :=
set_to_fun μ (condexp_ind hm μ) (dominated_fin_meas_additive_condexp_ind F' hm μ) f

lemma condexp_L1_undef (hf : ¬ integrable f μ) : condexp_L1 hm μ f = 0 :=
set_to_fun_undef (dominated_fin_meas_additive_condexp_ind F' hm μ) hf

lemma condexp_L1_eq (hf : integrable f μ) :
  condexp_L1 hm μ f = condexp_L1_clm hm μ (hf.to_L1 f) :=
set_to_fun_eq (dominated_fin_meas_additive_condexp_ind F' hm μ) hf

@[simp] lemma condexp_L1_zero : condexp_L1 hm μ (0 : α → F') = 0 :=
set_to_fun_zero _

@[simp] lemma condexp_L1_measure_zero (hm : m ≤ m0) : condexp_L1 hm (0 : measure α) f = 0 :=
set_to_fun_measure_zero _ rfl

lemma ae_strongly_measurable'_condexp_L1 {f : α → F'} :
  ae_strongly_measurable' m (condexp_L1 hm μ f) μ :=
begin
  by_cases hf : integrable f μ,
  { rw condexp_L1_eq hf,
    exact ae_strongly_measurable'_condexp_L1_clm _, },
  { rw condexp_L1_undef hf,
    refine ae_strongly_measurable'.congr _ (coe_fn_zero _ _ _).symm,
    exact strongly_measurable.ae_strongly_measurable' (@strongly_measurable_zero _ _ m _ _), },
end

lemma condexp_L1_congr_ae (hm : m ≤ m0) [sigma_finite (μ.trim hm)] (h : f =ᵐ[μ] g) :
  condexp_L1 hm μ f = condexp_L1 hm μ g :=
set_to_fun_congr_ae _ h

lemma integrable_condexp_L1 (f : α → F') : integrable (condexp_L1 hm μ f) μ :=
L1.integrable_coe_fn _

/-- The integral of the conditional expectation `condexp_L1` over an `m`-measurable set is equal to
the integral of `f` on that set. See also `set_integral_condexp`, the similar statement for
`condexp`. -/
lemma set_integral_condexp_L1 (hf : integrable f μ) (hs : measurable_set[m] s) :
  ∫ x in s, condexp_L1 hm μ f x ∂μ = ∫ x in s, f x ∂μ :=
begin
  simp_rw condexp_L1_eq hf,
  rw set_integral_condexp_L1_clm (hf.to_L1 f) hs,
  exact set_integral_congr_ae (hm s hs) ((hf.coe_fn_to_L1).mono (λ x hx hxs, hx)),
end

lemma condexp_L1_add (hf : integrable f μ) (hg : integrable g μ) :
  condexp_L1 hm μ (f + g) = condexp_L1 hm μ f + condexp_L1 hm μ g :=
set_to_fun_add _ hf hg

lemma condexp_L1_neg (f : α → F') : condexp_L1 hm μ (-f) = - condexp_L1 hm μ f :=
set_to_fun_neg _ f

lemma condexp_L1_smul (c : 𝕜) (f : α → F') : condexp_L1 hm μ (c • f) = c • condexp_L1 hm μ f :=
set_to_fun_smul _ (λ c _ x, condexp_ind_smul' c x) c f

lemma condexp_L1_sub (hf : integrable f μ) (hg : integrable g μ) :
  condexp_L1 hm μ (f - g) = condexp_L1 hm μ f - condexp_L1 hm μ g :=
set_to_fun_sub _ hf hg

lemma condexp_L1_of_ae_strongly_measurable'
  (hfm : ae_strongly_measurable' m f μ) (hfi : integrable f μ) :
  condexp_L1 hm μ f =ᵐ[μ] f :=
begin
  rw condexp_L1_eq hfi,
  refine eventually_eq.trans _ (integrable.coe_fn_to_L1 hfi),
  rw condexp_L1_clm_of_ae_strongly_measurable',
  exact ae_strongly_measurable'.congr hfm (integrable.coe_fn_to_L1 hfi).symm,
end

lemma condexp_L1_mono {E} [normed_lattice_add_comm_group E] [complete_space E] [normed_space ℝ E]
  [ordered_smul ℝ E] {f g : α → E}
  (hf : integrable f μ) (hg : integrable g μ) (hfg : f ≤ᵐ[μ] g) :
  condexp_L1 hm μ f ≤ᵐ[μ] condexp_L1 hm μ g :=
begin
  rw coe_fn_le,
  have h_nonneg : ∀ s, measurable_set s → μ s < ∞ → ∀ x : E, 0 ≤ x → 0 ≤ condexp_ind hm μ s x,
    from λ s hs hμs x hx, condexp_ind_nonneg hs hμs.ne x hx,
  exact set_to_fun_mono (dominated_fin_meas_additive_condexp_ind E hm μ) h_nonneg hf hg hfg,
end

end condexp_L1

section condexp

/-! ### Conditional expectation of a function -/

open_locale classical

variables {𝕜} {m m0 : measurable_space α} {μ : measure α} {f g : α → F'} {s : set α}

/-- Conditional expectation of a function. It is defined as 0 if any one of the following conditions
is true:
- `m` is not a sub-σ-algebra of `m0`,
- `μ` is not σ-finite with respect to `m`,
- `f` is not integrable. -/
@[irreducible]
def condexp (m : measurable_space α) {m0 : measurable_space α} (μ : measure α) (f : α → F') :
  α → F' :=
if hm : m ≤ m0
  then if h : sigma_finite (μ.trim hm) ∧ integrable f μ
    then if strongly_measurable[m] f
      then f
      else (@ae_strongly_measurable'_condexp_L1 _ _ _ _ _ m m0 μ hm h.1 _).mk
        (@condexp_L1 _ _ _ _ _ _ _ hm μ h.1 f)
    else 0
  else 0

-- We define notation `μ[f|m]` for the conditional expectation of `f` with respect to `m`.
localized "notation (name := measure_theory.condexp)
  μ `[` f `|` m `]` := measure_theory.condexp m μ f" in measure_theory

lemma condexp_of_not_le (hm_not : ¬ m ≤ m0) : μ[f|m] = 0 := by rw [condexp, dif_neg hm_not]

lemma condexp_of_not_sigma_finite (hm : m ≤ m0) (hμm_not : ¬ sigma_finite (μ.trim hm)) :
  μ[f|m] = 0 :=
by { rw [condexp, dif_pos hm, dif_neg], push_neg, exact λ h, absurd h hμm_not, }

lemma condexp_of_sigma_finite (hm : m ≤ m0) [hμm : sigma_finite (μ.trim hm)] :
  μ[f|m] =
  if integrable f μ
    then if strongly_measurable[m] f
      then f else ae_strongly_measurable'_condexp_L1.mk (condexp_L1 hm μ f)
    else 0 :=
begin
  rw [condexp, dif_pos hm],
  simp only [hμm, ne.def, true_and],
  by_cases hf : integrable f μ,
  { rw [dif_pos hf, if_pos hf], },
  { rw [dif_neg hf, if_neg hf], },
end

lemma condexp_of_strongly_measurable (hm : m ≤ m0) [hμm : sigma_finite (μ.trim hm)]
  {f : α → F'} (hf : strongly_measurable[m] f) (hfi : integrable f μ) :
  μ[f|m] = f :=
by { rw [condexp_of_sigma_finite hm, if_pos hfi, if_pos hf], apply_instance, }

lemma condexp_const (hm : m ≤ m0) (c : F') [is_finite_measure μ] : μ[(λ x : α, c)|m] = λ _, c :=
condexp_of_strongly_measurable hm (@strongly_measurable_const _ _ m _ _) (integrable_const c)

lemma condexp_ae_eq_condexp_L1 (hm : m ≤ m0) [hμm : sigma_finite (μ.trim hm)]
  (f : α → F') : μ[f|m] =ᵐ[μ] condexp_L1 hm μ f :=
begin
  rw condexp_of_sigma_finite hm,
  by_cases hfi : integrable f μ,
  { rw if_pos hfi,
    by_cases hfm : strongly_measurable[m] f,
    { rw if_pos hfm,
      exact (condexp_L1_of_ae_strongly_measurable'
        (strongly_measurable.ae_strongly_measurable' hfm) hfi).symm, },
    { rw if_neg hfm,
      exact (ae_strongly_measurable'.ae_eq_mk ae_strongly_measurable'_condexp_L1).symm, }, },
  rw [if_neg hfi, condexp_L1_undef hfi],
  exact (coe_fn_zero _ _ _).symm,
end

lemma condexp_ae_eq_condexp_L1_clm (hm : m ≤ m0) [sigma_finite (μ.trim hm)] (hf : integrable f μ) :
  μ[f|m] =ᵐ[μ] condexp_L1_clm hm μ (hf.to_L1 f) :=
begin
  refine (condexp_ae_eq_condexp_L1 hm f).trans (eventually_of_forall (λ x, _)),
  rw condexp_L1_eq hf,
end

lemma condexp_undef (hf : ¬ integrable f μ) : μ[f|m] = 0 :=
begin
  by_cases hm : m ≤ m0,
  swap, { rw condexp_of_not_le hm, },
  by_cases hμm : sigma_finite (μ.trim hm),
  swap, { rw condexp_of_not_sigma_finite hm hμm, },
  haveI : sigma_finite (μ.trim hm) := hμm,
  rw [condexp_of_sigma_finite, if_neg hf],
end

@[simp] lemma condexp_zero : μ[(0 : α → F')|m] = 0 :=
begin
  by_cases hm : m ≤ m0,
  swap, { rw condexp_of_not_le hm, },
  by_cases hμm : sigma_finite (μ.trim hm),
  swap, { rw condexp_of_not_sigma_finite hm hμm, },
  haveI : sigma_finite (μ.trim hm) := hμm,
  exact condexp_of_strongly_measurable hm (@strongly_measurable_zero _ _ m _ _)
    (integrable_zero _ _ _),
end

lemma strongly_measurable_condexp : strongly_measurable[m] (μ[f|m]) :=
begin
  by_cases hm : m ≤ m0,
  swap, { rw condexp_of_not_le hm, exact strongly_measurable_zero, },
  by_cases hμm : sigma_finite (μ.trim hm),
  swap, { rw condexp_of_not_sigma_finite hm hμm, exact strongly_measurable_zero, },
  haveI : sigma_finite (μ.trim hm) := hμm,
  rw condexp_of_sigma_finite hm,
  swap, { apply_instance, },
  split_ifs with hfi hfm,
  { exact hfm, },
  { exact ae_strongly_measurable'.strongly_measurable_mk _, },
  { exact strongly_measurable_zero, },
end

lemma condexp_congr_ae (h : f =ᵐ[μ] g) : μ[f | m] =ᵐ[μ] μ[g | m] :=
begin
  by_cases hm : m ≤ m0,
  swap, { simp_rw condexp_of_not_le hm, },
  by_cases hμm : sigma_finite (μ.trim hm),
  swap, { simp_rw condexp_of_not_sigma_finite hm hμm, },
  haveI : sigma_finite (μ.trim hm) := hμm,
  exact (condexp_ae_eq_condexp_L1 hm f).trans
    (filter.eventually_eq.trans (by rw condexp_L1_congr_ae hm h)
    (condexp_ae_eq_condexp_L1 hm g).symm),
end

lemma condexp_of_ae_strongly_measurable' (hm : m ≤ m0) [hμm : sigma_finite (μ.trim hm)]
  {f : α → F'} (hf : ae_strongly_measurable' m f μ) (hfi : integrable f μ) :
  μ[f|m] =ᵐ[μ] f :=
begin
  refine ((condexp_congr_ae hf.ae_eq_mk).trans _).trans hf.ae_eq_mk.symm,
  rw condexp_of_strongly_measurable hm hf.strongly_measurable_mk
    ((integrable_congr hf.ae_eq_mk).mp hfi),
end

lemma integrable_condexp : integrable (μ[f|m]) μ :=
begin
  by_cases hm : m ≤ m0,
  swap, { rw condexp_of_not_le hm, exact integrable_zero _ _ _, },
  by_cases hμm : sigma_finite (μ.trim hm),
  swap, { rw condexp_of_not_sigma_finite hm hμm, exact integrable_zero _ _ _, },
  haveI : sigma_finite (μ.trim hm) := hμm,
  exact (integrable_condexp_L1 f).congr (condexp_ae_eq_condexp_L1 hm f).symm,
end

/-- The integral of the conditional expectation `μ[f|hm]` over an `m`-measurable set is equal to
the integral of `f` on that set. -/
lemma set_integral_condexp (hm : m ≤ m0) [sigma_finite (μ.trim hm)]
  (hf : integrable f μ) (hs : measurable_set[m] s) :
  ∫ x in s, μ[f|m] x ∂μ = ∫ x in s, f x ∂μ :=
begin
  rw set_integral_congr_ae (hm s hs) ((condexp_ae_eq_condexp_L1 hm f).mono (λ x hx _, hx)),
  exact set_integral_condexp_L1 hf hs,
end

lemma integral_condexp (hm : m ≤ m0) [hμm : sigma_finite (μ.trim hm)]
  (hf : integrable f μ) : ∫ x, μ[f|m] x ∂μ = ∫ x, f x ∂μ :=
begin
  suffices : ∫ x in set.univ, μ[f|m] x ∂μ = ∫ x in set.univ, f x ∂μ,
    by { simp_rw integral_univ at this, exact this, },
  exact set_integral_condexp hm hf (@measurable_set.univ _ m),
end

/-- **Uniqueness of the conditional expectation**
If a function is a.e. `m`-measurable, verifies an integrability condition and has same integral
as `f` on all `m`-measurable sets, then it is a.e. equal to `μ[f|hm]`. -/
lemma ae_eq_condexp_of_forall_set_integral_eq (hm : m ≤ m0) [sigma_finite (μ.trim hm)]
  {f g : α → F'} (hf : integrable f μ)
  (hg_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → integrable_on g s μ)
  (hg_eq : ∀ s : set α, measurable_set[m] s → μ s < ∞ → ∫ x in s, g x ∂μ = ∫ x in s, f x ∂μ)
  (hgm : ae_strongly_measurable' m g μ) :
  g =ᵐ[μ] μ[f|m] :=
begin
  refine ae_eq_of_forall_set_integral_eq_of_sigma_finite' hm hg_int_finite
    (λ s hs hμs, integrable_condexp.integrable_on) (λ s hs hμs, _) hgm
    (strongly_measurable.ae_strongly_measurable' strongly_measurable_condexp),
  rw [hg_eq s hs hμs, set_integral_condexp hm hf hs],
end

lemma condexp_bot' [hμ : μ.ae.ne_bot] (f : α → F') :
  μ[f|⊥] = λ _, (μ set.univ).to_real⁻¹ • ∫ x, f x ∂μ :=
begin
  by_cases hμ_finite : is_finite_measure μ,
  swap,
  { have h : ¬ sigma_finite (μ.trim bot_le),
    { rwa sigma_finite_trim_bot_iff, },
    rw not_is_finite_measure_iff at hμ_finite,
    rw [condexp_of_not_sigma_finite bot_le h],
    simp only [hμ_finite, ennreal.top_to_real, inv_zero, zero_smul],
    refl, },
  haveI : is_finite_measure μ := hμ_finite,
  by_cases hf : integrable f μ,
  swap, { rw [integral_undef hf, smul_zero, condexp_undef hf], refl, },
  have h_meas : strongly_measurable[⊥] (μ[f|⊥]) := strongly_measurable_condexp,
  obtain ⟨c, h_eq⟩ := strongly_measurable_bot_iff.mp h_meas,
  rw h_eq,
  have h_integral : ∫ x, μ[f|⊥] x ∂μ = ∫ x, f x ∂μ := integral_condexp bot_le hf,
  simp_rw [h_eq, integral_const] at h_integral,
  rw [← h_integral, ← smul_assoc, smul_eq_mul, inv_mul_cancel, one_smul],
  rw [ne.def, ennreal.to_real_eq_zero_iff, auto.not_or_eq, measure.measure_univ_eq_zero,
    ← ae_eq_bot, ← ne.def, ← ne_bot_iff],
  exact ⟨hμ, measure_ne_top μ set.univ⟩,
end

lemma condexp_bot_ae_eq (f : α → F') :
  μ[f|⊥] =ᵐ[μ] λ _, (μ set.univ).to_real⁻¹ • ∫ x, f x ∂μ :=
begin
  by_cases μ.ae.ne_bot,
  { refine eventually_of_forall (λ x, _),
    rw condexp_bot' f,
    exact h, },
  { rw [ne_bot_iff, not_not, ae_eq_bot] at h,
    simp only [h, ae_zero], },
end

lemma condexp_bot [is_probability_measure μ] (f : α → F') :
  μ[f|⊥] = λ _, ∫ x, f x ∂μ :=
by { refine (condexp_bot' f).trans _, rw [measure_univ, ennreal.one_to_real, inv_one, one_smul], }

lemma condexp_add (hf : integrable f μ) (hg : integrable g μ) :
  μ[f + g | m] =ᵐ[μ] μ[f|m] + μ[g|m] :=
begin
  by_cases hm : m ≤ m0,
  swap, { simp_rw condexp_of_not_le hm, simp, },
  by_cases hμm : sigma_finite (μ.trim hm),
  swap, { simp_rw condexp_of_not_sigma_finite hm hμm, simp, },
  haveI : sigma_finite (μ.trim hm) := hμm,
  refine (condexp_ae_eq_condexp_L1 hm _).trans _,
  rw condexp_L1_add hf hg,
  exact (coe_fn_add _ _).trans
    ((condexp_ae_eq_condexp_L1 hm _).symm.add (condexp_ae_eq_condexp_L1 hm _).symm),
end

lemma condexp_finset_sum {ι : Type*} {s : finset ι} {f : ι → α → F'}
  (hf : ∀ i ∈ s, integrable (f i) μ) :
  μ[∑ i in s, f i | m] =ᵐ[μ] ∑ i in s, μ[f i | m] :=
begin
  induction s using finset.induction_on with i s his heq hf,
  { rw [finset.sum_empty, finset.sum_empty, condexp_zero] },
  { rw [finset.sum_insert his, finset.sum_insert his],
    exact (condexp_add (hf i $ finset.mem_insert_self i s) $ integrable_finset_sum' _
      (λ j hmem, hf j $ finset.mem_insert_of_mem hmem)).trans
      ((eventually_eq.refl _ _).add (heq $ λ j hmem, hf j $ finset.mem_insert_of_mem hmem)) }
end

lemma condexp_smul (c : 𝕜) (f : α → F') : μ[c • f | m] =ᵐ[μ] c • μ[f|m] :=
begin
  by_cases hm : m ≤ m0,
  swap, { simp_rw condexp_of_not_le hm, simp, },
  by_cases hμm : sigma_finite (μ.trim hm),
  swap, { simp_rw condexp_of_not_sigma_finite hm hμm, simp, },
  haveI : sigma_finite (μ.trim hm) := hμm,
  refine (condexp_ae_eq_condexp_L1 hm _).trans _,
  rw condexp_L1_smul c f,
  refine (@condexp_ae_eq_condexp_L1 _ _ _ _ _ m _ _ hm _ f).mp _,
  refine (coe_fn_smul c (condexp_L1 hm μ f)).mono (λ x hx1 hx2, _),
  rw [hx1, pi.smul_apply, pi.smul_apply, hx2],
end

lemma condexp_neg (f : α → F') : μ[-f|m] =ᵐ[μ] - μ[f|m] :=
by letI : module ℝ (α → F') := @pi.module α (λ _, F') ℝ _ _ (λ _, infer_instance);
calc μ[-f|m] = μ[(-1 : ℝ) • f|m] : by rw neg_one_smul ℝ f
... =ᵐ[μ] (-1 : ℝ) • μ[f|m] : condexp_smul (-1) f
... = -μ[f|m] : neg_one_smul ℝ (μ[f|m])

lemma condexp_sub (hf : integrable f μ) (hg : integrable g μ) :
  μ[f - g | m] =ᵐ[μ] μ[f|m] - μ[g|m] :=
begin
  simp_rw sub_eq_add_neg,
  exact (condexp_add hf hg.neg).trans (eventually_eq.rfl.add (condexp_neg g)),
end

lemma condexp_condexp_of_le {m₁ m₂ m0 : measurable_space α} {μ : measure α} (hm₁₂ : m₁ ≤ m₂)
  (hm₂ : m₂ ≤ m0) [sigma_finite (μ.trim hm₂)] :
  μ[ μ[f|m₂] | m₁] =ᵐ[μ] μ[f | m₁] :=
begin
  by_cases hμm₁ : sigma_finite (μ.trim (hm₁₂.trans hm₂)),
  swap, { simp_rw condexp_of_not_sigma_finite (hm₁₂.trans hm₂) hμm₁, },
  haveI : sigma_finite (μ.trim (hm₁₂.trans hm₂)) := hμm₁,
  by_cases hf : integrable f μ,
  swap, { simp_rw [condexp_undef hf, condexp_zero], },
  refine ae_eq_of_forall_set_integral_eq_of_sigma_finite' (hm₁₂.trans hm₂)
    (λ s hs hμs, integrable_condexp.integrable_on) (λ s hs hμs, integrable_condexp.integrable_on)
    _ (strongly_measurable.ae_strongly_measurable' strongly_measurable_condexp)
      (strongly_measurable.ae_strongly_measurable' strongly_measurable_condexp),
  intros s hs hμs,
  rw set_integral_condexp (hm₁₂.trans hm₂) integrable_condexp hs,
  swap, { apply_instance, },
  rw [set_integral_condexp (hm₁₂.trans hm₂) hf hs, set_integral_condexp hm₂ hf (hm₁₂ s hs)],
end

lemma condexp_mono {E} [normed_lattice_add_comm_group E] [complete_space E] [normed_space ℝ E]
  [ordered_smul ℝ E] {f g : α → E} (hf : integrable f μ) (hg : integrable g μ) (hfg : f ≤ᵐ[μ] g) :
  μ[f | m] ≤ᵐ[μ] μ[g | m] :=
begin
  by_cases hm : m ≤ m0,
  swap, { simp_rw condexp_of_not_le hm, },
  by_cases hμm : sigma_finite (μ.trim hm),
  swap, { simp_rw condexp_of_not_sigma_finite hm hμm, },
  haveI : sigma_finite (μ.trim hm) := hμm,
  exact (condexp_ae_eq_condexp_L1 hm _).trans_le
    ((condexp_L1_mono hf hg hfg).trans_eq (condexp_ae_eq_condexp_L1 hm _).symm),
end

lemma condexp_nonneg {E} [normed_lattice_add_comm_group E] [complete_space E] [normed_space ℝ E]
  [ordered_smul ℝ E] {f : α → E} (hf : 0 ≤ᵐ[μ] f) :
  0 ≤ᵐ[μ] μ[f | m] :=
begin
  by_cases hfint : integrable f μ,
  { rw (condexp_zero.symm : (0 : α → E) = μ[0 | m]),
    exact condexp_mono (integrable_zero _ _ _) hfint hf },
  { rw condexp_undef hfint, }
end

lemma condexp_nonpos {E} [normed_lattice_add_comm_group E] [complete_space E] [normed_space ℝ E]
  [ordered_smul ℝ E] {f : α → E} (hf : f ≤ᵐ[μ] 0) :
  μ[f | m] ≤ᵐ[μ] 0 :=
begin
  by_cases hfint : integrable f μ,
  { rw (condexp_zero.symm : (0 : α → E) = μ[0 | m]),
    exact condexp_mono hfint (integrable_zero _ _ _) hf },
  { rw condexp_undef hfint, }
end

/-- **Lebesgue dominated convergence theorem**: sufficient conditions under which almost
  everywhere convergence of a sequence of functions implies the convergence of their image by
  `condexp_L1`. -/
lemma tendsto_condexp_L1_of_dominated_convergence (hm : m ≤ m0) [sigma_finite (μ.trim hm)]
  {fs : ℕ → α → F'} {f : α → F'} (bound_fs : α → ℝ)
  (hfs_meas : ∀ n, ae_strongly_measurable (fs n) μ) (h_int_bound_fs : integrable bound_fs μ)
  (hfs_bound : ∀ n, ∀ᵐ x ∂μ, ‖fs n x‖ ≤ bound_fs x)
  (hfs : ∀ᵐ x ∂μ, tendsto (λ n, fs n x) at_top (𝓝 (f x))) :
  tendsto (λ n, condexp_L1 hm μ (fs n)) at_top (𝓝 (condexp_L1 hm μ f)) :=
tendsto_set_to_fun_of_dominated_convergence _ bound_fs hfs_meas h_int_bound_fs hfs_bound hfs

/-- If two sequences of functions have a.e. equal conditional expectations at each step, converge
and verify dominated convergence hypotheses, then the conditional expectations of their limits are
a.e. equal. -/
lemma tendsto_condexp_unique (fs gs : ℕ → α → F') (f g : α → F')
  (hfs_int : ∀ n, integrable (fs n) μ) (hgs_int : ∀ n, integrable (gs n) μ)
  (hfs : ∀ᵐ x ∂μ, tendsto (λ n, fs n x) at_top (𝓝 (f x)))
  (hgs : ∀ᵐ x ∂μ, tendsto (λ n, gs n x) at_top (𝓝 (g x)))
  (bound_fs : α → ℝ) (h_int_bound_fs : integrable bound_fs μ)
  (bound_gs : α → ℝ) (h_int_bound_gs : integrable bound_gs μ)
  (hfs_bound : ∀ n, ∀ᵐ x ∂μ, ‖fs n x‖ ≤ bound_fs x)
  (hgs_bound : ∀ n, ∀ᵐ x ∂μ, ‖gs n x‖ ≤ bound_gs x)
  (hfg : ∀ n, μ[fs n | m] =ᵐ[μ] μ[gs n | m]) :
  μ[f | m] =ᵐ[μ] μ[g | m] :=
begin
  by_cases hm : m ≤ m0, swap, { simp_rw condexp_of_not_le hm, },
  by_cases hμm : sigma_finite (μ.trim hm), swap, { simp_rw condexp_of_not_sigma_finite hm hμm, },
  haveI : sigma_finite (μ.trim hm) := hμm,
  refine (condexp_ae_eq_condexp_L1 hm f).trans ((condexp_ae_eq_condexp_L1 hm g).trans _).symm,
  rw ← Lp.ext_iff,
  have hn_eq : ∀ n, condexp_L1 hm μ (gs n) = condexp_L1 hm μ (fs n),
  { intros n,
    ext1,
    refine (condexp_ae_eq_condexp_L1 hm (gs n)).symm.trans ((hfg n).symm.trans _),
    exact (condexp_ae_eq_condexp_L1 hm (fs n)), },
  have hcond_fs : tendsto (λ n, condexp_L1 hm μ (fs n)) at_top (𝓝 (condexp_L1 hm μ f)),
    from tendsto_condexp_L1_of_dominated_convergence hm _ (λ n, (hfs_int n).1) h_int_bound_fs
       hfs_bound hfs,
  have hcond_gs : tendsto (λ n, condexp_L1 hm μ (gs n)) at_top (𝓝 (condexp_L1 hm μ g)),
    from tendsto_condexp_L1_of_dominated_convergence hm _ (λ n, (hgs_int n).1) h_int_bound_gs
       hgs_bound hgs,
  exact tendsto_nhds_unique_of_eventually_eq hcond_gs hcond_fs (eventually_of_forall hn_eq),
end

end condexp

end measure_theory
