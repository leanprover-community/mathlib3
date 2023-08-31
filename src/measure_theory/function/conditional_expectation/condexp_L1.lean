/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import measure_theory.function.conditional_expectation.condexp_L2

/-! # Conditional expectation in L1

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains two more steps of the construction of the conditional expectation, which is
completed in `measure_theory.function.conditional_expectation.basic`. See that file for a
description of the full process.

The contitional expectation of an `L²` function is defined in
`measure_theory.function.conditional_expectation.condexp_L2`. In this file, we perform two steps.
* Show that the conditional expectation of the indicator of a measurable set with finite measure
  is integrable and define a map `set α → (E →L[ℝ] (α →₁[μ] E))` which to a set associates a linear
  map. That linear map sends `x ∈ E` to the conditional expectation of the indicator of the set
  with value `x`.
* Extend that map to `condexp_L1_clm : (α →₁[μ] E) →L[ℝ] (α →₁[μ] E)`. This is done using the same
  construction as the Bochner integral (see the file `measure_theory/integral/set_to_L1`).

## Main definitions

* `condexp_L1`: Conditional expectation of a function as a linear map from `L1` to itself.

-/

noncomputable theory
open topological_space measure_theory.Lp filter continuous_linear_map
open_locale nnreal ennreal topology big_operators measure_theory

namespace measure_theory

variables {α β F F' G G' 𝕜 : Type*} {p : ℝ≥0∞}
  [is_R_or_C 𝕜] -- 𝕜 for ℝ or ℂ
  -- F for a Lp submodule
  [normed_add_comm_group F] [normed_space 𝕜 F]
  -- F' for integrals on a Lp submodule
  [normed_add_comm_group F'] [normed_space 𝕜 F'] [normed_space ℝ F'] [complete_space F']
  -- G for a Lp add_subgroup
  [normed_add_comm_group G]
  -- G' for integrals on a Lp add_subgroup
  [normed_add_comm_group G'] [normed_space ℝ G'] [complete_space G']

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

end measure_theory
