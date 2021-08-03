/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import measure_theory.l2_space

/-! # Conditional expectation

The conditional expectation will be defined for functions in `L²` by an orthogonal projection into
a complete subspace of `L²`. It will then be extended to `L¹`.

For now, this file contains only the definition of the subspace of `Lᵖ` containing functions which
are measurable with respect to a sub-σ-algebra, as well as a proof that it is complete.

-/

noncomputable theory
open topological_space measure_theory.Lp filter
open_locale nnreal ennreal topological_space big_operators measure_theory

namespace measure_theory

/-- A function `f` verifies `ae_measurable' m f μ` if it is `μ`-a.e. equal to an `m`-measurable
function. This is similar to `ae_measurable`, but the `measurable_space` structures used for the
measurability statement and for the measure are different. -/
def ae_measurable' {α β} [measurable_space β] (m : measurable_space α) {m0 : measurable_space α}
  (f : α → β) (μ : measure α) : Prop :=
∃ g : α → β, @measurable α β m _ g ∧ f =ᵐ[μ] g

namespace ae_measurable'

variables {α β 𝕜 : Type*} {m m0 : measurable_space α} {μ : measure α}
  [measurable_space β] [measurable_space 𝕜] {f g : α → β}

lemma congr (hf : ae_measurable' m f μ) (hfg : f =ᵐ[μ] g) : ae_measurable' m g μ :=
by { obtain ⟨f', hf'_meas, hff'⟩ := hf, exact ⟨f', hf'_meas, hfg.symm.trans hff'⟩, }

lemma add [has_add β] [has_measurable_add₂ β] (hf : ae_measurable' m f μ)
  (hg : ae_measurable' m g μ) :
  ae_measurable' m (f+g) μ :=
begin
  rcases hf with ⟨f', h_f'_meas, hff'⟩,
  rcases hg with ⟨g', h_g'_meas, hgg'⟩,
  exact ⟨f' + g', @measurable.add α m _ _ _ _ f' g' h_f'_meas h_g'_meas, hff'.add hgg'⟩,
end

lemma const_smul [has_scalar 𝕜 β] [has_measurable_smul 𝕜 β] (c : 𝕜) (hf : ae_measurable' m f μ) :
  ae_measurable' m (c • f) μ :=
begin
  rcases hf with ⟨f', h_f'_meas, hff'⟩,
  refine ⟨c • f', @measurable.const_smul α m _ _ _ _ _ _ f' h_f'_meas c, _⟩,
  exact eventually_eq.fun_comp hff' (λ x, c • x),
end

end ae_measurable'

lemma ae_measurable'_of_ae_measurable'_trim {α β} {m m0 m0' : measurable_space α}
  [measurable_space β] (hm0 : m0 ≤ m0') {μ : measure α} {f : α → β}
  (hf : ae_measurable' m f (μ.trim hm0)) :
  ae_measurable' m f μ :=
by { obtain ⟨g, hg_meas, hfg⟩ := hf, exact ⟨g, hg_meas, ae_eq_of_ae_eq_trim hfg⟩, }

variables {α β γ E E' F F' G G' H 𝕜 : Type*} {p : ℝ≥0∞}
  [is_R_or_C 𝕜] [measurable_space 𝕜] -- 𝕜 for ℝ or ℂ, together with a measurable_space
  [measurable_space β] -- β for a generic measurable space
  -- E for an inner product space
  [inner_product_space 𝕜 E] [measurable_space E] [borel_space E] [second_countable_topology E]
  -- E' for an inner product space on which we compute integrals
  [inner_product_space 𝕜 E'] [measurable_space E'] [borel_space E'] [second_countable_topology E']
  [complete_space E'] [normed_space ℝ E']
  -- F for a Lp submodule
  [normed_group F] [normed_space 𝕜 F] [measurable_space F] [borel_space F]
  [second_countable_topology F]
  -- F' for integrals on a Lp submodule
  [normed_group F'] [normed_space 𝕜 F'] [measurable_space F'] [borel_space F']
  [second_countable_topology F'] [normed_space ℝ F'] [complete_space F']
  -- G for a Lp add_subgroup
  [normed_group G] [measurable_space G] [borel_space G] [second_countable_topology G]
  -- G' for integrals on a Lp add_subgroup
  [normed_group G'] [measurable_space G'] [borel_space G'] [second_countable_topology G']
  [normed_space ℝ G'] [complete_space G']
  -- H for measurable space and normed group (hypotheses of mem_ℒp)
  [measurable_space H] [normed_group H]

section Lp_meas

variables (F 𝕜)
/-- `Lp_meas F 𝕜 m p μ` is the subspace of `Lp F p μ` containing functions `f` verifying
`ae_measurable' m f μ`, i.e. functions which are `μ`-a.e. equal to an `m`-measurable function. -/
def Lp_meas [opens_measurable_space 𝕜] (m : measurable_space α) [measurable_space α] (p : ℝ≥0∞)
  (μ : measure α) :
  submodule 𝕜 (Lp F p μ) :=
{ carrier   := {f : (Lp F p μ) | ae_measurable' m f μ} ,
  zero_mem' := ⟨(0 : α → F), @measurable_zero _ α _ m _, Lp.coe_fn_zero _ _ _⟩,
  add_mem'  := λ f g hf hg, (hf.add hg).congr (Lp.coe_fn_add f g).symm,
  smul_mem' := λ c f hf, (hf.const_smul c).congr (Lp.coe_fn_smul c f).symm, }
variables {F 𝕜}

variables [opens_measurable_space 𝕜]

lemma mem_Lp_meas_iff_ae_measurable' {m m0 : measurable_space α} {μ : measure α} {f : Lp F p μ} :
  f ∈ Lp_meas F 𝕜 m p μ ↔ ae_measurable' m f μ :=
by simp_rw [← set_like.mem_coe, ← submodule.mem_carrier, Lp_meas, set.mem_set_of_eq]

lemma Lp_meas.ae_measurable' {m m0 : measurable_space α} {μ : measure α} (f : Lp_meas F 𝕜 m p μ) :
  ae_measurable' m f μ :=
mem_Lp_meas_iff_ae_measurable'.mp f.mem

lemma mem_Lp_meas_self {m0 : measurable_space α} (μ : measure α) (f : Lp F p μ) :
  f ∈ Lp_meas F 𝕜 m0 p μ :=
mem_Lp_meas_iff_ae_measurable'.mpr (Lp.ae_measurable f)

lemma Lp_meas_coe {m m0 : measurable_space α} {μ : measure α} {f : Lp_meas F 𝕜 m p μ} :
  ⇑f = (f : Lp F p μ) :=
coe_fn_coe_base f

lemma mem_Lp_meas_indicator_const_Lp {m m0 : measurable_space α} (hm : m ≤ m0)
  {μ : measure α} {s : set α} (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) {c : F} :
  indicator_const_Lp p (hm s hs) hμs c ∈ Lp_meas F 𝕜 m p μ :=
⟨s.indicator (λ x : α, c),
  @measurable.indicator α _ m _ _ s (λ x, c) (@measurable_const _ α _ m _) hs,
  indicator_const_Lp_coe_fn⟩

section complete_subspace

/-! ## The subspace `Lp_meas` is complete.

We define a `linear_isometry_equiv` between `Lp_meas` and the `Lp` space corresponding to the
measure `μ.trim hm`. As a consequence, the completeness of `Lp` implies completeness of
`Lp_meas`. -/

variables {ι : Type*} {m m0 : measurable_space α} {μ : measure α}

/-- If `f` belongs to `Lp_meas F 𝕜 m p μ`, then the measurable function it is almost everywhere
equal to (given by `ae_measurable.mk`) belongs to `ℒp` for the measure `μ.trim hm`. -/
lemma mem_ℒp_trim_of_mem_Lp_meas (hm : m ≤ m0) (f : Lp F p μ) (hf_meas : f ∈ Lp_meas F 𝕜 m p μ) :
  @mem_ℒp α F m _ _ (mem_Lp_meas_iff_ae_measurable'.mp hf_meas).some p (μ.trim hm) :=
begin
  have hf : ae_measurable' m f μ, from (mem_Lp_meas_iff_ae_measurable'.mp hf_meas),
  let g := hf.some,
  obtain ⟨hg, hfg⟩ := hf.some_spec,
  change @mem_ℒp α F m _ _ g p (μ.trim hm),
  refine ⟨@measurable.ae_measurable _ _ m _ g (μ.trim hm) hg, _⟩,
  have h_snorm_fg : @snorm α _ m _ g p (μ.trim hm) = snorm f p μ,
    by { rw snorm_trim hm hg, exact snorm_congr_ae hfg.symm, },
  rw h_snorm_fg,
  exact Lp.snorm_lt_top f,
end

/-- If `f` belongs to `Lp` for the measure `μ.trim hm`, then it belongs to the subspace
`Lp_meas F 𝕜 m p μ`. -/
lemma mem_Lp_meas_to_Lp_of_trim (hm : m ≤ m0) (f : @Lp α F m _ _ _ _ p (μ.trim hm)) :
  (mem_ℒp_of_mem_ℒp_trim hm (@Lp.mem_ℒp _ _ m _ _ _ _ _ _ f)).to_Lp f ∈ Lp_meas F 𝕜 m p μ :=
begin
  let hf_mem_ℒp := mem_ℒp_of_mem_ℒp_trim hm (@Lp.mem_ℒp _ _ m _ _ _ _ _ _ f),
  rw mem_Lp_meas_iff_ae_measurable',
  refine ae_measurable'.congr _ (mem_ℒp.coe_fn_to_Lp hf_mem_ℒp).symm,
  refine ae_measurable'_of_ae_measurable'_trim hm _,
  exact (@Lp.ae_measurable _ _ m _ _ _ _ _ _ f),
end

variables (F 𝕜 p μ)
/-- Map from `Lp_meas` to `Lp F p (μ.trim hm)`. -/
def Lp_meas_to_Lp_trim (hm : m ≤ m0) (f : Lp_meas F 𝕜 m p μ) : @Lp α F m _ _ _ _ p (μ.trim hm) :=
@mem_ℒp.to_Lp _ _ m p (μ.trim hm) _ _ _ _ (mem_Lp_meas_iff_ae_measurable'.mp f.mem).some
  (mem_ℒp_trim_of_mem_Lp_meas hm f f.mem)

/-- Map from `Lp F p (μ.trim hm)` to `Lp_meas`, inverse of `Lp_meas_to_Lp_trim`. -/
def Lp_trim_to_Lp_meas (hm : m ≤ m0) (f : @Lp α F m _ _ _ _ p (μ.trim hm)) :
  Lp_meas F 𝕜 m p μ :=
⟨(mem_ℒp_of_mem_ℒp_trim hm (@Lp.mem_ℒp _ _ m _ _ _ _ _ _ f)).to_Lp f,
  mem_Lp_meas_to_Lp_of_trim hm f⟩

variables {F 𝕜 p μ}

lemma Lp_meas_to_Lp_trim_ae_eq (hm : m ≤ m0) (f : Lp_meas F 𝕜 m p μ) :
  Lp_meas_to_Lp_trim F 𝕜 p μ hm f =ᵐ[μ] f :=
(ae_eq_of_ae_eq_trim
    (@mem_ℒp.coe_fn_to_Lp _ _ m _ _ _ _ _ _ _ (mem_ℒp_trim_of_mem_Lp_meas hm ↑f f.mem))).trans
  (mem_Lp_meas_iff_ae_measurable'.mp f.mem).some_spec.2.symm

lemma Lp_trim_to_Lp_meas_ae_eq (hm : m ≤ m0) (f : @Lp α F m _ _ _ _ p (μ.trim hm)) :
  Lp_trim_to_Lp_meas F 𝕜 p μ hm f =ᵐ[μ] f :=
mem_ℒp.coe_fn_to_Lp _

/-- `Lp_trim_to_Lp_meas` is a right inverse of `Lp_meas_to_Lp_trim`. -/
lemma Lp_meas_to_Lp_trim_right_inv (hm : m ≤ m0) :
  function.right_inverse (Lp_trim_to_Lp_meas F 𝕜 p μ hm) (Lp_meas_to_Lp_trim F 𝕜 p μ hm) :=
begin
  intro f,
  ext1,
  refine ae_eq_trim_of_measurable hm _ _ _,
  { exact @Lp.measurable _ _ m _ _ _ _ _ _ _, },
  { exact @Lp.measurable _ _ m _ _ _ _ _ _ _, },
  { exact (Lp_meas_to_Lp_trim_ae_eq hm _).trans (Lp_trim_to_Lp_meas_ae_eq hm _), },
end

/-- `Lp_trim_to_Lp_meas` is a left inverse of `Lp_meas_to_Lp_trim`. -/
lemma Lp_meas_to_Lp_trim_left_inv (hm : m ≤ m0) :
  function.left_inverse (Lp_trim_to_Lp_meas F 𝕜 p μ hm) (Lp_meas_to_Lp_trim F 𝕜 p μ hm) :=
begin
  intro f,
  ext1,
  ext1,
  rw ← Lp_meas_coe,
  exact (Lp_trim_to_Lp_meas_ae_eq hm _).trans (Lp_meas_to_Lp_trim_ae_eq hm _),
end

lemma Lp_meas_to_Lp_trim_add (hm : m ≤ m0) (f g : Lp_meas F 𝕜 m p μ) :
  Lp_meas_to_Lp_trim F 𝕜 p μ hm (f + g)
    = Lp_meas_to_Lp_trim F 𝕜 p μ hm f + Lp_meas_to_Lp_trim F 𝕜 p μ hm g :=
begin
  ext1,
  refine eventually_eq.trans _ (@Lp.coe_fn_add _ _ m _ _ _ _ _ _ _ _).symm,
  refine ae_eq_trim_of_measurable hm _ _ _,
  { exact @Lp.measurable _ _ m _ _ _ _ _ _ _, },
  { exact @measurable.add _ m _ _ _ _ _ _ (@Lp.measurable _ _ m _ _ _ _ _ _ _)
      (@Lp.measurable _ _ m _ _ _ _ _ _ _), },
  refine (Lp_meas_to_Lp_trim_ae_eq hm _).trans _,
  refine eventually_eq.trans _
    (eventually_eq.add (Lp_meas_to_Lp_trim_ae_eq hm f).symm (Lp_meas_to_Lp_trim_ae_eq hm g).symm),
  refine (Lp.coe_fn_add _ _).trans _,
  simp_rw Lp_meas_coe,
  refine eventually_of_forall (λ x, _),
  refl,
end

lemma Lp_meas_to_Lp_trim_smul (hm : m ≤ m0) (c : 𝕜) (f : Lp_meas F 𝕜 m p μ) :
  Lp_meas_to_Lp_trim F 𝕜 p μ hm (c • f) = c • Lp_meas_to_Lp_trim F 𝕜 p μ hm f :=
begin
  ext1,
  refine eventually_eq.trans _ (@Lp.coe_fn_smul _ _ m _ _ _ _ _ _ _ _ _ _ _ _ _).symm,
  refine ae_eq_trim_of_measurable hm _ _ _,
  { exact @Lp.measurable _ _ m _ _ _ _ _ _ _, },
  { exact @measurable.const_smul _ m _ _ _ _ _ _ _ (@Lp.measurable _ _ m _ _ _ _ _ _ _) c, },
  refine (Lp_meas_to_Lp_trim_ae_eq hm _).trans _,
  refine (Lp.coe_fn_smul c _).trans _,
  refine (Lp_meas_to_Lp_trim_ae_eq hm f).mono (λ x hx, _),
  rw [pi.smul_apply, pi.smul_apply, hx, Lp_meas_coe],
  refl,
end

/-- `Lp_meas_to_Lp_trim` preserves the norm. -/
lemma Lp_meas_to_Lp_trim_norm_map [hp : fact (1 ≤ p)] (hm : m ≤ m0) (f : Lp_meas F 𝕜 m p μ) :
  ∥Lp_meas_to_Lp_trim F 𝕜 p μ hm f∥ = ∥f∥ :=
begin
  rw [norm_def, snorm_trim hm (@Lp.measurable _ _ m _ _ _ _ _ _ _)],
  swap, { apply_instance, },
  rw [snorm_congr_ae (Lp_meas_to_Lp_trim_ae_eq hm _), Lp_meas_coe, ← norm_def],
  congr,
end

variables (F 𝕜 p μ)
/-- A linear isometry equivalence between `Lp_meas` and `Lp F p (μ.trim hm)`. -/
def Lp_meas_to_Lp_trim_lie [hp : fact (1 ≤ p)] (hm : m ≤ m0) :
  Lp_meas F 𝕜 m p μ ≃ₗᵢ[𝕜] @Lp α F m _ _ _ _ p (μ.trim hm) :=
{ to_fun    := Lp_meas_to_Lp_trim F 𝕜 p μ hm,
  map_add'  := Lp_meas_to_Lp_trim_add hm,
  map_smul' := Lp_meas_to_Lp_trim_smul hm,
  inv_fun   := Lp_trim_to_Lp_meas F 𝕜 p μ hm,
  left_inv  := Lp_meas_to_Lp_trim_left_inv hm,
  right_inv := Lp_meas_to_Lp_trim_right_inv hm,
  norm_map' := Lp_meas_to_Lp_trim_norm_map hm, }
variables {F 𝕜 p μ}

instance [hm : fact (m ≤ m0)] [complete_space F] [hp : fact (1 ≤ p)] :
  complete_space (Lp_meas F 𝕜 m p μ) :=
by { rw (Lp_meas_to_Lp_trim_lie F 𝕜 p μ hm.elim).to_isometric.complete_space_iff, apply_instance, }

end complete_subspace

end Lp_meas

section integral_norm_le

variables {m m0 : measurable_space α} {μ : measure α} {s : set α}

/-- Let `m` be a sub-σ-algebra of `m0`, `f` a `m0`-measurable function and `g` a `m`-measurable
function, such that their integrals coincide on `m`-measurable sets with finite measure.
Then `∫ x in s, ∥g x∥ ∂μ ≤ ∫ x in s, ∥f x∥ ∂μ` on all `m`-measurable sets with finite measure. -/
lemma integral_norm_le_of_forall_fin_meas_integral_eq (hm : m ≤ m0) {f g : α → ℝ}
  (hf : measurable f) (hfi : integrable_on f s μ) (hg : measurable[m] g) (hgi : integrable_on g s μ)
  (hgf : ∀ t, measurable_set[m] t → μ t < ∞ → ∫ x in t, g x ∂μ = ∫ x in t, f x ∂μ)
  (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) :
  ∫ x in s, ∥g x∥ ∂μ ≤ ∫ x in s, ∥f x∥ ∂μ :=
begin
  rw integral_norm_eq_pos_sub_neg (hg.mono hm le_rfl) hgi,
  rw integral_norm_eq_pos_sub_neg hf hfi,
  have h_meas_nonneg_g : measurable_set[m] {x | 0 ≤ g x},
    from @measurable_set_le _ α _ _ _ m _ _ _ _ g (@measurable_const _ α _ m _) hg,
  have h_meas_nonneg_f : measurable_set {x | 0 ≤ f x},
    from measurable_set_le measurable_const hf,
  have h_meas_nonpos_g : measurable_set[m] {x | g x ≤ 0},
    from @measurable_set_le _ α _ _ _ m _ _ _ g _ hg (@measurable_const _ α _ m _),
  have h_meas_nonpos_f : measurable_set {x | f x ≤ 0},
    from measurable_set_le hf measurable_const,
  refine sub_le_sub _ _,
  { rw [measure.restrict_restrict (hm _ h_meas_nonneg_g),
      measure.restrict_restrict h_meas_nonneg_f,
      hgf _ (@measurable_set.inter α m _ _ h_meas_nonneg_g hs)
        ((measure_mono (set.inter_subset_right _ _)).trans_lt (lt_top_iff_ne_top.mpr hμs)),
      ← measure.restrict_restrict (hm _ h_meas_nonneg_g),
      ← measure.restrict_restrict h_meas_nonneg_f],
    exact set_integral_le_nonneg (hm _ h_meas_nonneg_g) hf hfi, },
  { rw [measure.restrict_restrict (hm _ h_meas_nonpos_g),
      measure.restrict_restrict h_meas_nonpos_f,
      hgf _ (@measurable_set.inter α m _ _ h_meas_nonpos_g hs)
        ((measure_mono (set.inter_subset_right _ _)).trans_lt (lt_top_iff_ne_top.mpr hμs)),
      ← measure.restrict_restrict (hm _ h_meas_nonpos_g),
      ← measure.restrict_restrict h_meas_nonpos_f],
    exact set_integral_nonpos_le (hm _ h_meas_nonpos_g) hf hfi, },
end

/-- Let `m` be a sub-σ-algebra of `m0`, `f` a `m0`-measurable function and `g` a `m`-measurable
function, such that their integrals coincide on `m`-measurable sets with finite measure.
Then `∫⁻ x in s, ∥g x∥₊ ∂μ ≤ ∫⁻ x in s, ∥f x∥₊ ∂μ` on all `m`-measurable sets with finite
measure. -/
lemma lintegral_nnnorm_le_of_forall_fin_meas_integral_eq (hm : m ≤ m0) {f g : α → ℝ}
  (hf : measurable f) (hfi : integrable_on f s μ) (hg : measurable[m] g) (hgi : integrable_on g s μ)
  (hgf : ∀ t, measurable_set[m] t → μ t < ∞ → ∫ x in t, g x ∂μ = ∫ x in t, f x ∂μ)
  (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) :
  ∫⁻ x in s, ∥g x∥₊ ∂μ ≤ ∫⁻ x in s, ∥f x∥₊ ∂μ :=
begin
  rw [← of_real_integral_norm_eq_lintegral_nnnorm hfi,
    ← of_real_integral_norm_eq_lintegral_nnnorm hgi, ennreal.of_real_le_of_real_iff],
  { exact integral_norm_le_of_forall_fin_meas_integral_eq hm hf hfi hg hgi hgf hs hμs, },
  { exact integral_nonneg (λ x, norm_nonneg _), },
end

end integral_norm_le

local attribute [instance] fact_one_le_two_ennreal

variables [borel_space 𝕜] {m m0 : measurable_space α} {μ : measure α}
  {s t : set α}

local notation `⟪`x`, `y`⟫` := @inner 𝕜 E _ x y
local notation `⟪`x`, `y`⟫'` := @inner 𝕜 E' _ x y
local notation `⟪`x`, `y`⟫₂` := @inner 𝕜 (α →₂[μ] E) _ x y

section ae_eq_of_forall_set_integral_eq

lemma ae_const_le_iff_forall_lt_measure_zero (f : α → ℝ) (c : ℝ) :
  (∀ᵐ x ∂μ, c ≤ f x) ↔ ∀ b < c, μ {x | f x ≤ b} = 0 :=
begin
  rw ae_iff,
  push_neg,
  have h_Union : {x | f x < c} = ⋃ (r : ℚ) (hr : ↑r < c), {x | f x ≤ r},
  { ext1 x,
    simp_rw [set.mem_Union, set.mem_set_of_eq],
    split; intro h,
    { obtain ⟨q, lt_q, q_lt⟩ := exists_rat_btwn h, exact ⟨q, q_lt, lt_q.le⟩, },
    { obtain ⟨q, q_lt, q_le⟩ := h, exact q_le.trans_lt q_lt, }, },
  rw [h_Union, measure_Union_null_iff],
  split; intros h b,
  { intro hbc,
    obtain ⟨r, hr⟩ := exists_rat_btwn hbc,
    specialize h r,
    simp only [hr.right, set.Union_pos] at h,
    refine measure_mono_null (λ x hx, _) h,
    rw set.mem_set_of_eq at hx ⊢,
    exact hx.trans hr.1.le, },
  { by_cases hbc : ↑b < c,
    { simp only [hbc, set.Union_pos],
      exact h _ hbc, },
    { simp [hbc], }, },
end

lemma measure_lt_top_of_integrable_on {f : α → H} {s : set α} (hfs : integrable_on f s μ)
  (hs : measurable_set s) (C : ℝ≥0∞) (hC : 0 < C) (hfC : ∀ᵐ x ∂μ, x ∈ s → C ≤ ∥f x∥₊) :
  μ s < ∞ :=
begin
  rw [integrable_on, integrable, has_finite_integral] at hfs,
  have hf_int_s := hfs.2,
  have hbs_int : ∫⁻ x in s, C ∂μ ≤ ∫⁻ x in s, ∥f x∥₊ ∂μ,
    from lintegral_mono_ae ((ae_restrict_iff' hs).mpr hfC),
  rw [lintegral_const, measure.restrict_apply_univ] at hbs_int,
  have h_mul_lt_top : C * μ s < ∞, from hbs_int.trans_lt hf_int_s,
  rw ennreal.mul_lt_top_iff at h_mul_lt_top,
  cases h_mul_lt_top with h h,
  { exact h.2, },
  cases h with h h,
  { exact absurd h hC.ne.symm, },
  { rw h, exact ennreal.coe_lt_top, },
end

/-- Use `ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure` instead. -/
private lemma ae_nonneg_of_forall_set_ℝ_of_measurable_of_finite_measure [finite_measure μ]
  {f : α → ℝ} (hfm : measurable f) (hf : integrable f μ)
  (hf_zero : ∀ s, measurable_set s → 0 ≤ ∫ x in s, f x ∂μ) :
  0 ≤ᵐ[μ] f :=
begin
  simp_rw [eventually_le, pi.zero_apply],
  rw ae_const_le_iff_forall_lt_measure_zero,
  intros b hb_neg,
  let s := {x | f x ≤ b},
  have hs : measurable_set s, from measurable_set_le hfm measurable_const,
  have h_int_gt : ∫ x in s, f x ∂μ ≤ b * (μ s).to_real,
  { have h_const_le : ∫ x in s, f x ∂μ ≤ ∫ x in s, b ∂μ,
    { refine set_integral_mono_ae_restrict hf.integrable_on
        (integrable_on_const.mpr (or.inr (measure_lt_top μ s))) _,
      rw [eventually_le, ae_restrict_iff hs],
      exact eventually_of_forall (λ x hxs, hxs), },
    rwa [set_integral_const, smul_eq_mul, mul_comm] at h_const_le, },
  by_contra,
  refine (lt_self_iff_false (∫ x in s, f x ∂μ)).mp (h_int_gt.trans_lt _),
  refine (mul_neg_iff.mpr (or.inr ⟨hb_neg, _⟩)).trans_le _,
  swap, { simp_rw measure.restrict_restrict hs, exact hf_zero s hs, },
  refine (ennreal.to_real_nonneg).lt_of_ne (λ h_eq, h _),
  cases (ennreal.to_real_eq_zero_iff _).mp h_eq.symm with hμs_eq_zero hμs_eq_top,
  { exact hμs_eq_zero, },
  { exact absurd hμs_eq_top (measure_lt_top μ s).ne, },
end

lemma ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure [finite_measure μ]
  {f : α → ℝ} (hf : integrable f μ) (hf_zero : ∀ s, measurable_set s → 0 ≤ ∫ x in s, f x ∂μ) :
  0 ≤ᵐ[μ] f :=
begin
  rcases hf with ⟨⟨f', hf'_meas, hf_ae⟩, hf_finite_int⟩,
  have hf'_integrable : integrable f' μ,
    from integrable.congr ⟨⟨f', hf'_meas, hf_ae⟩, hf_finite_int⟩ hf_ae,
  have hf'_zero : ∀ s, measurable_set s → 0 ≤ ∫ x in s, f' x ∂μ,
  { intros s hs,
    rw set_integral_congr_ae hs (hf_ae.mono (λ x hx hxs, hx.symm)),
    exact hf_zero s hs, },
  exact (ae_nonneg_of_forall_set_ℝ_of_measurable_of_finite_measure hf'_meas
    hf'_integrable hf'_zero).trans hf_ae.symm.le,
end

lemma ae_nonneg_of_forall_set_integral_nonneg' {f : α → ℝ}
  {t : set α} (ht : measurable_set t) (hμt : μ t ≠ ∞) (hf : integrable_on f t μ)
  (hf_zero : ∀ s, measurable_set s → 0 ≤ ∫ x in (s ∩ t), f x ∂μ) :
  0 ≤ᵐ[μ.restrict t] f :=
begin
  haveI : fact (μ t < ∞) := ⟨lt_top_iff_ne_top.mpr hμt⟩,
  refine ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure hf (λ s hs, _),
  simp_rw measure.restrict_restrict hs,
  exact hf_zero s hs,
end

lemma ae_nonneg_restrict_of_forall_set_integral_nonneg {f : α → ℝ}
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s, measurable_set s → μ s < ∞ → 0 ≤ ∫ x in s, f x ∂μ)
  {t : set α} (ht : measurable_set t) (hμt : μ t ≠ ∞) :
  0 ≤ᵐ[μ.restrict t] f :=
begin
  refine ae_nonneg_of_forall_set_integral_nonneg' ht hμt
    (hf_int_finite t ht (lt_top_iff_ne_top.mpr hμt)) (λ s hs, _),
  refine (hf_zero (s ∩ t) (hs.inter ht) _),
  exact (measure_mono (set.inter_subset_right s t)).trans_lt (lt_top_iff_ne_top.mpr hμt),
end

lemma ae_eq_zero_restrict_of_forall_set_integral_eq_zero_ℝ {f : α → ℝ}
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = 0)
  {t : set α} (ht : measurable_set t) (hμt : μ t ≠ ∞) :
  f =ᵐ[μ.restrict t] 0 :=
begin
  suffices h_and : f ≤ᵐ[μ.restrict t] 0 ∧ 0 ≤ᵐ[μ.restrict t] f,
    from h_and.1.mp (h_and.2.mono (λ x hx1 hx2, le_antisymm hx2 hx1)),
  refine ⟨_, ae_nonneg_restrict_of_forall_set_integral_nonneg hf_int_finite
    (λ s hs hμs, (hf_zero s hs hμs).symm.le) ht hμt⟩,
  suffices h_neg : 0 ≤ᵐ[μ.restrict t] -f,
  { refine h_neg.mono (λ x hx, _),
    rw pi.neg_apply at hx,
    refine le_of_neg_le_neg _,
    simpa using hx, },
  refine ae_nonneg_restrict_of_forall_set_integral_nonneg (λ s hs hμs, (hf_int_finite s hs hμs).neg)
    (λ s hs hμs, _) ht hμt,
  simp_rw pi.neg_apply,
  rw [integral_neg, neg_nonneg],
  exact (hf_zero s hs hμs).le,
end

lemma ae_eq_zero_of_forall_inner_ae_eq_zero {𝕜' : Type*} [is_R_or_C 𝕜'] [measurable_space α]
  [inner_product_space 𝕜' γ] [second_countable_topology γ]
  {μ : measure α} {f : α → γ} (hf : ∀ c : γ, ∀ᵐ x ∂μ, inner c (f x) = (0 : 𝕜')) :
  f =ᵐ[μ] 0 :=
begin
  let s := dense_seq γ,
  have hs : dense_range s := dense_range_dense_seq γ,
  have hf' : ∀ᵐ x ∂μ, ∀ n : ℕ, inner (s n) (f x) = (0 : 𝕜'), from ae_all_iff.mpr (λ n, hf (s n)),
  refine hf'.mono (λ x hx, _),
  rw [pi.zero_apply, ← inner_self_eq_zero],
  have h_closed : is_closed {c : γ | inner c (f x) = (0 : 𝕜')},
    from is_closed_eq (continuous_id.inner continuous_const) continuous_const,
  exact @is_closed_property ℕ γ _ s (λ c, inner c (f x) = (0 : 𝕜')) hs h_closed (λ n, hx n) _,
end

lemma ae_measurable.re {f : α → 𝕜} (hf : ae_measurable f μ) :
  ae_measurable (λ x, is_R_or_C.re (f x)) μ :=
measurable.comp_ae_measurable is_R_or_C.continuous_re.measurable hf

lemma ae_measurable.im {f : α → 𝕜} (hf : ae_measurable f μ) :
  ae_measurable (λ x, is_R_or_C.im (f x)) μ :=
measurable.comp_ae_measurable is_R_or_C.continuous_im.measurable hf

lemma integrable.re {f : α → 𝕜} (hf : integrable f μ) :
  integrable (λ x, is_R_or_C.re (f x)) μ :=
begin
  have h_norm_le : ∀ a, ∥is_R_or_C.re (f a)∥ ≤ ∥f a∥,
  { intro a,
    rw [is_R_or_C.norm_eq_abs, is_R_or_C.norm_eq_abs, is_R_or_C.abs_to_real],
    exact is_R_or_C.abs_re_le_abs _, },
  exact integrable.mono hf (ae_measurable.re hf.1) (eventually_of_forall h_norm_le),
end

lemma integrable.im {f : α → 𝕜} (hf : integrable f μ) :
  integrable (λ x, is_R_or_C.im (f x)) μ :=
begin
  have h_norm_le : ∀ a, ∥is_R_or_C.im (f a)∥ ≤ ∥f a∥,
  { intro a,
    rw [is_R_or_C.norm_eq_abs, is_R_or_C.norm_eq_abs, is_R_or_C.abs_to_real],
    exact is_R_or_C.abs_im_le_abs _, },
  exact integrable.mono hf (ae_measurable.im hf.1) (eventually_of_forall h_norm_le),
end

lemma integrable.const_inner {f : α → E} (hf : integrable f μ) (c : E) :
  integrable (λ x, ⟪c, f x⟫) μ :=
begin
  have hf_const_mul : integrable (λ x, ∥c∥ * ∥f x∥) μ, from integrable.const_mul hf.norm (∥c∥),
  refine integrable.mono hf_const_mul (ae_measurable.inner ae_measurable_const hf.1) _,
  refine eventually_of_forall (λ x, _),
  rw is_R_or_C.norm_eq_abs,
  refine (abs_inner_le_norm _ _).trans _,
  simp,
end

lemma ae_eq_zero_restrict_of_forall_set_integral_eq_zero [is_scalar_tower ℝ 𝕜 E'] (f : α → E')
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = 0)
  {t : set α} (ht : measurable_set t) (hμt : μ t ≠ ∞) :
  f =ᵐ[μ.restrict t] 0 :=
begin
  refine ae_eq_zero_of_forall_inner_ae_eq_zero (λ c, _),
  suffices h_re_im : (∀ᵐ x ∂(μ.restrict t), is_R_or_C.re ⟪c, f x⟫' = 0)
    ∧ ∀ᵐ x ∂(μ.restrict t), is_R_or_C.im ⟪c, f x⟫' = 0,
  { rw ← eventually_and at h_re_im,
    refine h_re_im.mono (λ x hx, _),
    rwa [is_R_or_C.ext_iff, add_monoid_hom.map_zero, add_monoid_hom.map_zero], },
  have hf_inner_re : ∀ s, measurable_set s → μ s < ∞ →
      integrable_on (λ x, is_R_or_C.re ⟪c, f x⟫') s μ,
    from λ s hs hμs, integrable.re (integrable.const_inner (hf_int_finite s hs hμs) c),
  have hf_inner_im : ∀ s, measurable_set s → μ s < ∞ →
      integrable_on (λ x, is_R_or_C.im ⟪c, f x⟫') s μ,
    from λ s hs hμs, integrable.im (integrable.const_inner (hf_int_finite s hs hμs) c),
  have hf_zero_inner : ∀ s, measurable_set s → μ s < ∞ → ∫ x in s, ⟪c, f x⟫' ∂μ = 0,
  { intros s hs hμs,
    rw integral_inner (hf_int_finite s hs hμs) c,
    simp [hf_zero s hs hμs], },
  have hf_zero_inner_re : ∀ s, measurable_set s → μ s < ∞ → ∫ x in s, is_R_or_C.re ⟪c, f x⟫' ∂μ = 0,
  { intros s hs hμs,
    rw [integral_re (integrable.const_inner (hf_int_finite s hs hμs) c), hf_zero_inner s hs hμs,
      is_R_or_C.zero_re'], },
  have hf_zero_inner_im : ∀ s, measurable_set s → μ s < ∞ → ∫ x in s, is_R_or_C.im ⟪c, f x⟫' ∂μ = 0,
  { intros s hs hμs,
    rw [integral_im (integrable.const_inner (hf_int_finite s hs hμs) c), hf_zero_inner s hs hμs],
    simp only [add_monoid_hom.map_zero], },
  exact ⟨ae_eq_zero_restrict_of_forall_set_integral_eq_zero_ℝ hf_inner_re hf_zero_inner_re ht hμt,
    ae_eq_zero_restrict_of_forall_set_integral_eq_zero_ℝ hf_inner_im hf_zero_inner_im ht hμt⟩,
end

lemma ae_eq_zero_of_forall_set_integral_eq_zero' [is_scalar_tower ℝ 𝕜 E'] (f : α → E')
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = 0)
  {t : set α} {S : ℕ → set α} (hS_meas : ∀ n, measurable_set (S n)) (hSμ : ∀ n, μ (S n) < ∞)
  (htS : t = ⋃ n, S n) :
  f =ᵐ[μ.restrict t] 0 :=
begin
  rw [eventually_eq, ae_iff, measure.restrict_apply'],
  swap, { rw htS, exact measurable_set.Union hS_meas, },
  simp_rw [htS, set.inter_Union],
  refine le_antisymm _ (zero_le _),
  refine (measure_Union_le _).trans _,
  suffices h_all_zero : ∀ i, μ ({a : α | ¬f a = 0} ∩ S i) = 0, by simp [h_all_zero],
  intro i,
  rw ← measure.restrict_apply' (hS_meas i),
  exact ae_eq_zero_restrict_of_forall_set_integral_eq_zero f hf_int_finite hf_zero (hS_meas i)
    (hSμ i).ne,
end

lemma univ_eq_Union_lt (f : α → H) :
  set.univ = ⋃ (n : ℕ), ({x | f x = 0} ∪ {x | ((1:ℝ)/n) ≤ ∥f x∥}) :=
begin
  sorry,
end

lemma ae_eq_zero_of_forall_set_integral_eq_zero_of_measurable [is_scalar_tower ℝ 𝕜 E'] {f : α → E'}
  (hf : integrable f μ) (hfm : measurable f)
  (hf_zero : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = 0) :
  f =ᵐ[μ] 0 :=
begin
  rw ← @measure.restrict_univ _ _ μ,
  refine ae_eq_zero_of_forall_set_integral_eq_zero' f (λ s hs hμs, hf.integrable_on) hf_zero
    _ _ (univ_eq_Union_lt f),
  { intro n,
    refine measurable_set.union _ (measurable_set_le measurable_const hfm.norm),
    exact measurable_set_eq_fun hfm measurable_const, },
end

/-- Use `ae_nonneg_of_forall_set_ℝ` instead. -/
private lemma ae_nonneg_of_forall_set_ℝ_of_measurable {f : α → ℝ} (hf : integrable f μ)
  (hfm : measurable f) (hf_zero : ∀ s, measurable_set s → μ s < ∞ → 0 ≤ ∫ x in s, f x ∂μ) :
  0 ≤ᵐ[μ] f :=
begin
  simp_rw [eventually_le, pi.zero_apply],
  rw ae_const_le_iff_forall_lt_measure_zero,
  intros b hb_neg,
  let s := {x | f x ≤ b},
  have hs : measurable_set s, from measurable_set_le hfm measurable_const,
  have hfs : ∀ x ∈ s, f x ≤ b, from λ x hxs, hxs,
  have hμs_lt_top : μ s < ∞,
  { refine measure_lt_top_of_integrable_on hf.integrable_on hs (∥b∥₊ : ℝ≥0∞) _
      (eventually_of_forall _),
    { rwa [← of_real_norm_eq_coe_nnnorm, ennreal.of_real_pos, real.norm_eq_abs,
      abs_eq_neg_self.mpr hb_neg.le, lt_neg, neg_zero], },
    { simp_rw [← of_real_norm_eq_coe_nnnorm, real.norm_eq_abs],
      refine λ x hx, ennreal.of_real_le_of_real _,
      rw [abs_eq_neg_self.mpr hb_neg.le, abs_eq_neg_self.mpr ((hfs x hx).trans hb_neg.le)],
      exact neg_le_neg (hfs x hx), }, },
  have h_int_gt : ∫ x in s, f x ∂μ ≤ b * (μ s).to_real,
  { have h_const_le : ∫ x in s, f x ∂μ ≤ ∫ x in s, b ∂μ,
    { refine set_integral_mono_ae_restrict hf.integrable_on
        (integrable_on_const.mpr (or.inr hμs_lt_top)) _,
      rw [eventually_le, ae_restrict_iff hs],
      exact eventually_of_forall hfs, },
    rwa [set_integral_const, smul_eq_mul, mul_comm] at h_const_le, },
  by_contra,
  refine (lt_self_iff_false (∫ x in s, f x ∂μ)).mp (h_int_gt.trans_lt _),
  refine (mul_neg_iff.mpr (or.inr ⟨hb_neg, _⟩)).trans_le (hf_zero s hs hμs_lt_top),
  refine (ennreal.to_real_nonneg).lt_of_ne (λ h_eq, h _),
  cases (ennreal.to_real_eq_zero_iff _).mp h_eq.symm with hμs_to_real hμs_to_real,
  { exact hμs_to_real, },
  { exact absurd hμs_to_real hμs_lt_top.ne, },
end

lemma ae_nonneg_of_forall_set_integral_nonneg {f : α → ℝ} (hf : integrable f μ)
  (hf_zero : ∀ s, measurable_set s → μ s < ∞ → 0 ≤ ∫ x in s, f x ∂μ) :
  0 ≤ᵐ[μ] f :=
begin
  rcases hf with ⟨⟨f', hf'_meas, hf_ae⟩, hf_finite_int⟩,
  have hf'_integrable : integrable f' μ,
    from integrable.congr ⟨⟨f', hf'_meas, hf_ae⟩, hf_finite_int⟩ hf_ae,
  have hf'_zero : ∀ s, measurable_set s → μ s < ∞ → 0 ≤ ∫ x in s, f' x ∂μ,
  { intros s hs,
    rw set_integral_congr_ae hs (hf_ae.mono (λ x hx hxs, hx.symm)),
    exact hf_zero s hs, },
  exact (ae_nonneg_of_forall_set_ℝ_of_measurable hf'_integrable hf'_meas hf'_zero).trans
    hf_ae.symm.le,
end

lemma ae_eq_zero_of_forall_set_integral_eq_zero_ℝ {f : α → ℝ} (hf : integrable f μ)
  (hf_zero : ∀ s, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = 0) :
  f =ᵐ[μ] 0 :=
begin
  suffices h_and : f ≤ᵐ[μ] 0 ∧ 0 ≤ᵐ[μ] f,
    from h_and.1.mp (h_and.2.mono (λ x hx1 hx2, le_antisymm hx2 hx1)),
  refine ⟨_, ae_nonneg_of_forall_set_integral_nonneg hf (λ s hs hμs, (hf_zero s hs hμs).symm.le)⟩,
  suffices h_neg : 0 ≤ᵐ[μ] -f,
  { refine h_neg.mono (λ x hx, _),
    rw pi.neg_apply at hx,
    refine le_of_neg_le_neg _,
    simpa using hx, },
  refine ae_nonneg_of_forall_set_integral_nonneg hf.neg (λ s hs hμs, _),
  simp_rw pi.neg_apply,
  rw [integral_neg, neg_nonneg],
  exact (hf_zero s hs hμs).le,
end

lemma ae_eq_zero_of_forall_set_integral_eq_zero [is_scalar_tower ℝ 𝕜 E'] (f : α → E')
  (hf : integrable f μ) (hf_zero : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = 0) :
  f =ᵐ[μ] 0 :=
begin
  refine ae_eq_zero_of_forall_inner_ae_eq_zero (λ c, _),
  suffices h_re_im : (∀ᵐ x ∂μ, is_R_or_C.re ⟪c, f x⟫' = 0) ∧ ∀ᵐ x ∂μ, is_R_or_C.im ⟪c, f x⟫' = 0,
  { rw ← eventually_and at h_re_im,
    refine h_re_im.mono (λ x hx, _),
    rwa [is_R_or_C.ext_iff, add_monoid_hom.map_zero, add_monoid_hom.map_zero], },
  have hf_inner_re : integrable (λ x, is_R_or_C.re ⟪c, f x⟫') μ,
    from integrable.re (integrable.const_inner hf c),
  have hf_inner_im : integrable (λ x, is_R_or_C.im ⟪c, f x⟫') μ,
    from integrable.im (integrable.const_inner hf c),
  have hf_zero_inner : ∀ s, measurable_set s → μ s < ∞ → ∫ x in s, ⟪c, f x⟫' ∂μ = 0,
  { intros s hs hμs,
    rw integral_inner hf.integrable_on c,
    simp [hf_zero s hs hμs], },
  have hf_zero_inner_re : ∀ s, measurable_set s → μ s < ∞ → ∫ x in s, is_R_or_C.re ⟪c, f x⟫' ∂μ = 0,
  { intros s hs hμs,
    rw [integral_re (integrable.const_inner hf c).integrable_on, hf_zero_inner s hs hμs,
      is_R_or_C.zero_re'], },
  have hf_zero_inner_im : ∀ s, measurable_set s → μ s < ∞ → ∫ x in s, is_R_or_C.im ⟪c, f x⟫' ∂μ = 0,
  { intros s hs hμs,
    rw [integral_im (integrable.const_inner hf c).integrable_on, hf_zero_inner s hs hμs],
    simp only [add_monoid_hom.map_zero], },
  exact ⟨ae_eq_zero_of_forall_set_integral_eq_zero_ℝ hf_inner_re hf_zero_inner_re,
    ae_eq_zero_of_forall_set_integral_eq_zero_ℝ hf_inner_im hf_zero_inner_im⟩,
end

lemma ae_eq_of_forall_set_integral_eq [is_scalar_tower ℝ 𝕜 E'] (f g : α → E') (hf : integrable f μ)
  (hg : integrable g μ)
  (hfg : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ) :
  f =ᵐ[μ] g :=
begin
  suffices h_sub : f-g =ᵐ[μ] 0,
    by { refine h_sub.mono (λ x hx, _), rwa [pi.sub_apply, pi.zero_apply, sub_eq_zero] at hx, },
  have hfg' : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, (f - g) x ∂μ = 0,
  { intros s hs hμs,
    rw integral_sub' hf.integrable_on hg.integrable_on,
    exact sub_eq_zero.mpr (hfg s hs hμs), },
  exact ae_eq_zero_of_forall_set_integral_eq_zero (f-g) (hf.sub hg) hfg',
end

end ae_eq_of_forall_set_integral_eq

/-! ## Conditional expectation in L2

We define a conditional expectation in `L2`: it is the orthogonal projection on the subspace
`Lp_meas`. -/

section condexp_L2

variables [complete_space E]

variables (𝕜)
/-- Conditional expectation of a function in L2 with respect to a sigma-algebra -/
def condexp_L2 (hm : m ≤ m0) : (α →₂[μ] E) →L[𝕜] (Lp_meas E 𝕜 m 2 μ) :=
@orthogonal_projection 𝕜 (α →₂[μ] E) _ _ (Lp_meas E 𝕜 m 2 μ)
  (by { haveI : fact (m ≤ m0) := ⟨hm⟩, exact infer_instance, })
variables {𝕜}

lemma integrable_on_condexp_L2_of_measure_ne_top (hm : m ≤ m0) (hμs : μ s ≠ ∞) (f : α →₂[μ] E) :
  integrable_on (condexp_L2 𝕜 hm f) s μ :=
integrable_on_Lp_of_measure_ne_top ((condexp_L2 𝕜 hm f) : α →₂[μ] E)
  fact_one_le_two_ennreal.elim hμs

lemma integrable_condexp_L2_of_finite_measure (hm : m ≤ m0) [finite_measure μ] {f : α →₂[μ] E} :
  integrable (condexp_L2 𝕜 hm f) μ :=
integrable_on_univ.mp $ integrable_on_condexp_L2_of_measure_ne_top hm (measure_ne_top _ _) f

lemma norm_condexp_L2_le_one (hm : m ≤ m0) : ∥@condexp_L2 α E 𝕜 _ _ _ _ _ _ _ _ _ μ _ hm∥ ≤ 1 :=
by { haveI : fact (m ≤ m0) := ⟨hm⟩, exact orthogonal_projection_norm_le _, }

lemma norm_condexp_L2_le (hm : m ≤ m0) (f : α →₂[μ] E) : ∥condexp_L2 𝕜 hm f∥ ≤ ∥f∥ :=
((@condexp_L2 _ E 𝕜 _ _ _ _ _ _ _ _ _ μ _ hm).le_op_norm f).trans
  (mul_le_of_le_one_left (norm_nonneg _) (norm_condexp_L2_le_one hm))

lemma snorm_condexp_L2_le (hm : m ≤ m0) (f : α →₂[μ] E) :
  snorm (condexp_L2 𝕜 hm f) 2 μ ≤ snorm f 2 μ :=
begin
  rw [Lp_meas_coe, ← ennreal.to_real_le_to_real (Lp.snorm_ne_top _) (Lp.snorm_ne_top _), ← norm_def,
    ← norm_def, submodule.norm_coe],
  exact norm_condexp_L2_le hm f,
end

lemma norm_condexp_L2_coe_le (hm : m ≤ m0) (f : α →₂[μ] E) :
  ∥(condexp_L2 𝕜 hm f : α →₂[μ] E)∥ ≤ ∥f∥ :=
begin
  rw [norm_def, norm_def, ← Lp_meas_coe],
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
  haveI : fact(m ≤ m0) := ⟨hm⟩,
  have h_mem : indicator_const_Lp 2 (hm s hs) hμs c ∈ Lp_meas E 𝕜 m 2 μ,
    from mem_Lp_meas_indicator_const_Lp hm hs hμs,
  let ind := (⟨indicator_const_Lp 2 (hm s hs) hμs c, h_mem⟩ : Lp_meas E 𝕜 m 2 μ),
  have h_coe_ind : (ind : α →₂[μ] E) = indicator_const_Lp 2 (hm s hs) hμs c, by refl,
  have h_orth_mem := orthogonal_projection_mem_subspace_eq_self ind,
  rw [← h_coe_ind, h_orth_mem],
end

lemma inner_condexp_L2_eq_inner_fun (hm : m ≤ m0) (f g : α →₂[μ] E) (hg : ae_measurable' m g μ) :
  ⟪(condexp_L2 𝕜 hm f : α →₂[μ] E), g⟫₂ = ⟪f, g⟫₂ :=
begin
  symmetry,
  rw [← sub_eq_zero, ← inner_sub_left, condexp_L2],
  simp only [mem_Lp_meas_iff_ae_measurable'.mpr hg, orthogonal_projection_inner_eq_zero],
end

section restrict



end restrict

section real

lemma integral_condexp_L2_eq_of_fin_meas (hm : m ≤ m0) (f : Lp 𝕜 2 μ) {s : set α}
  (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) :
  ∫ x in s, condexp_L2 𝕜 hm f x ∂μ = ∫ x in s, f x ∂μ :=
begin
  rw ← L2.inner_indicator_const_Lp_one (hm s hs) hμs,
  have h_eq_inner : ∫ x in s, condexp_L2 𝕜 hm f x ∂μ
    = inner (indicator_const_Lp 2 (hm s hs) hμs (1 : 𝕜)) (condexp_L2 𝕜 hm f),
  { rw L2.inner_indicator_const_Lp_one (hm s hs) hμs,
    congr, },
  rw [h_eq_inner, ← inner_condexp_L2_left_eq_right, condexp_L2_indicator_of_measurable hm hs hμs],
end

lemma lintegral_nnnorm_condexp_L2_le (hm : m ≤ m0) (hs : measurable_set[m] s) (hμs : μ s ≠ ∞)
  (f : Lp ℝ 2 μ) :
  ∫⁻ x in s, ∥condexp_L2 ℝ hm f x∥₊ ∂μ ≤ ∫⁻ x in s, ∥f x∥₊ ∂μ :=
begin
  let h_meas := Lp_meas.ae_measurable' (condexp_L2 ℝ hm f),
  let g := h_meas.some,
  have hg_meas : @measurable _ _ m _ g, from h_meas.some_spec.1,
  have hg_eq : g =ᵐ[μ] condexp_L2 ℝ hm f, from h_meas.some_spec.2.symm,
  have hg_eq_restrict : g =ᵐ[μ.restrict s] condexp_L2 ℝ hm f, from ae_restrict_of_ae hg_eq,
  have hg_nnnorm_eq : (λ x, (∥g x∥₊ : ℝ≥0∞))
    =ᵐ[μ.restrict s] (λ x, (∥condexp_L2 ℝ hm f x∥₊ : ℝ≥0∞)),
  { refine hg_eq_restrict.mono (λ x hx, _),
    dsimp only,
    rw hx, },
  rw lintegral_congr_ae hg_nnnorm_eq.symm,
  refine lintegral_nnnorm_le_of_forall_fin_meas_integral_eq hm (Lp.measurable f) _ _ _ _ hs hμs,
  { exact integrable_on_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs, },
  { exact hg_meas, },
  { rw [integrable_on, integrable_congr hg_eq_restrict],
    exact integrable_on_condexp_L2_of_measure_ne_top hm hμs f, },
  { intros t ht hμt,
    rw ← integral_condexp_L2_eq_of_fin_meas hm f ht hμt.ne,
    exact set_integral_congr_ae (hm t ht) (hg_eq.mono (λ x hx _, hx)), },
end

lemma condexp_L2_ae_eq_zero_of_ae_eq_zero (hm : m ≤ m0) (hs : measurable_set[m] s) (hμs : μ s ≠ ∞)
  {f : Lp ℝ 2 μ} (hf : f =ᵐ[μ.restrict s] 0) :
  condexp_L2 ℝ hm f =ᵐ[μ.restrict s] 0 :=
begin
  suffices h_nnnorm_eq_zero : ∫⁻ x in s, ∥condexp_L2 ℝ hm f x∥₊ ∂μ = 0,
  { rw lintegral_eq_zero_iff at h_nnnorm_eq_zero,
    refine h_nnnorm_eq_zero.mono (λ x hx, _),
    dsimp only at hx,
    rw pi.zero_apply at hx ⊢,
    { rwa [ennreal.coe_eq_zero, nnnorm_eq_zero] at hx, },
    { refine measurable.coe_nnreal_ennreal (measurable.nnnorm _),
      rw Lp_meas_coe,
      exact Lp.measurable _, }, },
  refine le_antisymm _ (zero_le _),
  refine (lintegral_nnnorm_condexp_L2_le hm hs hμs f).trans (le_of_eq _),
  rw lintegral_eq_zero_iff,
  { refine hf.mono (λ x hx, _),
    dsimp only,
    rw hx,
    simp, },
  { exact (Lp.measurable _).nnnorm.coe_nnreal_ennreal, },
end

lemma lintegral_nnnorm_condexp_L2_indicator_le (hm : m ≤ m0) {s : set α} (hs : measurable_set s)
  (hμs : μ s ≠ ∞) {t : set α} (ht : measurable_set[m] t) (hμt : μ t ≠ ∞) :
  ∫⁻ a in t, ∥condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)) a∥₊ ∂μ ≤ μ (s ∩ t) :=
begin
  refine (lintegral_nnnorm_condexp_L2_le hm ht hμt _).trans (le_of_eq _),
  have h_eq : ∫⁻ x in t, ∥(indicator_const_Lp 2 hs hμs (1 : ℝ)) x∥₊ ∂μ
    = ∫⁻ x in t, s.indicator (λ x, (1 : ℝ≥0∞)) x ∂μ,
  { refine lintegral_congr_ae (ae_restrict_of_ae _),
    refine (@indicator_const_Lp_coe_fn _ _ _ 2 _ _ _ _ hs hμs (1 : ℝ) _ _).mono (λ x hx, _),
    rw hx,
    simp_rw set.indicator_apply,
    split_ifs; simp, },
  rw [h_eq, lintegral_indicator _ hs, lintegral_const, measure.restrict_restrict hs],
  simp only [one_mul, set.univ_inter, measurable_set.univ, measure.restrict_apply],
end

end real

lemma norm_inner_le (a b : E) : ∥⟪a, b⟫∥ ≤ ∥a∥ * ∥b∥ :=
(is_R_or_C.norm_eq_abs _).le.trans (abs_inner_le_norm _ _)

lemma mem_ℒp_const_inner (p : ℝ≥0∞) (c : E) {f : α → E} (hf : mem_ℒp f p μ) :
  mem_ℒp (λ a, ⟪c, f a⟫) p μ :=
begin
  refine ⟨ae_measurable.inner ae_measurable_const hf.1, _⟩,
  have snorm_norm_inner_le : snorm (λ x, ⟪c, f x⟫) p μ ≤ snorm (λ x, ∥c∥ * ∥f x∥) p μ,
  { refine snorm_mono_ae (eventually_of_forall (λ x, _)),
    simp only [normed_field.norm_mul, norm_norm],
    exact norm_inner_le _ _, },
  refine snorm_norm_inner_le.trans_lt _,
  simp_rw ← smul_eq_mul ℝ,
  rw [← pi.smul_def, @snorm_const_smul _ _ _ p μ _ _ _ _ (λ x, ∥f x∥) (∥c∥)],
  refine ennreal.mul_lt_top ennreal.coe_lt_top _,
  rw snorm_norm,
  exact hf.snorm_lt_top,
end

lemma condexp_const_inner (hm : m ≤ m0) (f : Lp E' 2 μ) (c : E') :
  condexp_L2 𝕜 hm (mem_ℒp.to_Lp (λ a, ⟪c, f a⟫') (mem_ℒp_const_inner 2 c (Lp.mem_ℒp f)))
    =ᵐ[μ] λ a, ⟪c, condexp_L2 𝕜 hm f a⟫' :=
begin
  sorry,
end

lemma integral_condexp_L2_eq_of_fin_meas' [is_scalar_tower ℝ 𝕜 E'] (hm : m ≤ m0) (f : Lp E' 2 μ)
  {s : set α} (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) :
  ∫ x in s, condexp_L2 𝕜 hm f x ∂μ = ∫ x in s, f x ∂μ :=
begin
  rw ← sub_eq_zero,
  rw ← integral_sub',
  swap, { exact integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs, },
  swap, { exact integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs, },
  refine integral_eq_zero_of_forall_integral_inner_eq_zero _ _ _,
  sorry,
  intro c,
  simp_rw pi.sub_apply,
  simp_rw inner_sub_right,
  rw integral_sub,
  swap,
  { refine integrable.const_inner _ c,
    exact integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs, },
  swap,
  { refine integrable.const_inner _ c,
    exact integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs, },
  rw sub_eq_zero,
  rw ← set_integral_congr_ae (hm s hs) ((condexp_const_inner hm f c).mono (λ x hx _, hx)),
  have h_ae_eq_f := mem_ℒp.coe_fn_to_Lp (mem_ℒp_const_inner 2 c (Lp.mem_ℒp f)),
  rw ← set_integral_congr_ae (hm s hs) (h_ae_eq_f.mono (λ x hx _, hx)),
  exact integral_condexp_L2_eq_of_fin_meas hm _ hs hμs,
end

end condexp_L2

end measure_theory
