/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import measure_theory.function.l2_space
import measure_theory.function.ae_eq_of_integral

/-! # Conditional expectation

We build the conditional expectation with respect to a sub-sigma-algebra `m` in three steps:
* Define the conditional expectation of an `L²` function, as an element of `L²`. This is the
  orthogonal projection on the subspace of almost everywhere `m`-measurable functions.
* Show that the conditional expectation of the indicator of a measurable set with finite measure
  is integrable and define a map `set α → (E →L[ℝ] (α →₁[μ] E))` which to a set associates a linear
  map. That linear map sends `x ∈ E` to the conditional expectation of the indicator of the set
  with value `x`.
* Extend that map to `(α →₁[μ] E) →L[𝕜] (α →₁[μ] E)`. This is done using the same construction as
  the Bochner integral. TODO.

-/

noncomputable theory
open topological_space measure_theory.Lp filter continuous_linear_map
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
  exact ⟨f' + g', @measurable.add _ _ _ _ m _ f' g' h_f'_meas h_g'_meas, hff'.add hgg'⟩,
end

lemma neg [has_neg β] [has_measurable_neg β] {f : α → β} (hfm : ae_measurable' m f μ) :
  ae_measurable' m (-f) μ :=
begin
  rcases hfm with ⟨f', hf'_meas, hf_ae⟩,
  refine ⟨-f', @measurable.neg _ _ _ _ _ m _ hf'_meas, hf_ae.mono (λ x hx, _)⟩,
  simp_rw pi.neg_apply,
  rw hx,
end

lemma sub [has_sub β] [has_measurable_sub₂ β] {f g : α → β}
  (hfm : ae_measurable' m f μ) (hgm : ae_measurable' m g μ) :
  ae_measurable' m (f - g) μ :=
begin
  rcases hfm with ⟨f', hf'_meas, hf_ae⟩,
  rcases hgm with ⟨g', hg'_meas, hg_ae⟩,
  refine ⟨f'-g', @measurable.sub _ _ _ _ m _ _ _ hf'_meas hg'_meas,
    hf_ae.mp (hg_ae.mono (λ x hx1 hx2, _))⟩,
  simp_rw pi.sub_apply,
  rw [hx1, hx2],
end

lemma const_smul [has_scalar 𝕜 β] [has_measurable_smul 𝕜 β] (c : 𝕜) (hf : ae_measurable' m f μ) :
  ae_measurable' m (c • f) μ :=
begin
  rcases hf with ⟨f', h_f'_meas, hff'⟩,
  refine ⟨c • f', @measurable.const_smul _ _ _ _ _ _ m _ f' h_f'_meas c, _⟩,
  exact eventually_eq.fun_comp hff' (λ x, c • x),
end

lemma const_inner [is_R_or_C 𝕜] [borel_space 𝕜] [inner_product_space 𝕜 β]
  [second_countable_topology β] [opens_measurable_space β]
  {f : α → β} (hfm : ae_measurable' m f μ) (c : β) :
  ae_measurable' m (λ x, (inner c (f x) : 𝕜)) μ :=
begin
  rcases hfm with ⟨f', hf'_meas, hf_ae⟩,
  refine ⟨λ x, (inner c (f' x) : 𝕜),
    @measurable.inner _ _ _ _ _ m _ _ _ _ _ _ _ (@measurable_const _ _ _ m _) hf'_meas,
    hf_ae.mono (λ x hx, _)⟩,
  dsimp only,
  rw hx,
end

/-- A m-measurable function almost everywhere equal to `f`. -/
def mk (f : α → β) (hfm : ae_measurable' m f μ) : α → β := hfm.some

lemma measurable_mk {f : α → β} (hfm : ae_measurable' m f μ) : measurable[m] (hfm.mk f) :=
hfm.some_spec.1

lemma ae_eq_mk {f : α → β} (hfm : ae_measurable' m f μ) : f =ᵐ[μ] hfm.mk f :=
hfm.some_spec.2

lemma measurable_comp {γ} [measurable_space γ] {f : α → β} {g : β → γ}
  (hg : measurable g) (hf : ae_measurable' m f μ) :
  ae_measurable' m (g ∘ f) μ :=
⟨λ x, g (hf.mk _ x), @measurable.comp _ _ _ m _ _ _ _ hg hf.measurable_mk,
  hf.ae_eq_mk.mono (λ x hx, by rw [function.comp_apply, hx])⟩

end ae_measurable'

lemma ae_measurable'_of_ae_measurable'_trim {α β} {m m0 m0' : measurable_space α}
  [measurable_space β] (hm0 : m0 ≤ m0') {μ : measure α} {f : α → β}
  (hf : ae_measurable' m f (μ.trim hm0)) :
  ae_measurable' m f μ :=
by { obtain ⟨g, hg_meas, hfg⟩ := hf, exact ⟨g, hg_meas, ae_eq_of_ae_eq_trim hfg⟩, }

lemma measurable.ae_measurable' {α β} {m m0 : measurable_space α} [measurable_space β]
  {μ : measure α} {f : α → β} (hf : measurable[m] f) :
  ae_measurable' m f μ :=
⟨f, hf, ae_eq_refl _⟩

lemma ae_eq_trim_iff_of_ae_measurable' {α β} [add_group β] [measurable_space β]
  [measurable_singleton_class β] [has_measurable_sub₂ β]
  {m m0 : measurable_space α} {μ : measure α} {f g : α → β}
  (hm : m ≤ m0) (hfm : ae_measurable' m f μ) (hgm : ae_measurable' m g μ) :
  hfm.mk f =ᵐ[μ.trim hm] hgm.mk g ↔ f =ᵐ[μ] g :=
(ae_eq_trim_iff hm hfm.measurable_mk hgm.measurable_mk).trans
⟨λ h, hfm.ae_eq_mk.trans (h.trans hgm.ae_eq_mk.symm),
  λ h, hfm.ae_eq_mk.symm.trans (h.trans hgm.ae_eq_mk)⟩


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

/-! ## The subset `Lp_meas` of `Lp` functions a.e. measurable with respect to a sub-sigma-algebra -/

variables (F)

/-- `Lp_meas_subgroup F m p μ` is the subspace of `Lp F p μ` containing functions `f` verifying
`ae_measurable' m f μ`, i.e. functions which are `μ`-a.e. equal to an `m`-measurable function. -/
def Lp_meas_subgroup (m : measurable_space α) [measurable_space α] (p : ℝ≥0∞) (μ : measure α) :
  add_subgroup (Lp F p μ) :=
{ carrier   := {f : (Lp F p μ) | ae_measurable' m f μ} ,
  zero_mem' := ⟨(0 : α → F), @measurable_zero _ α _ m _, Lp.coe_fn_zero _ _ _⟩,
  add_mem'  := λ f g hf hg, (hf.add hg).congr (Lp.coe_fn_add f g).symm,
  neg_mem' := λ f hf, ae_measurable'.congr hf.neg (Lp.coe_fn_neg f).symm, }

variables (𝕜)
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

lemma mem_Lp_meas_subgroup_iff_ae_measurable' {m m0 : measurable_space α} {μ : measure α}
  {f : Lp F p μ} :
  f ∈ Lp_meas_subgroup F m p μ ↔ ae_measurable' m f μ :=
by rw [← add_subgroup.mem_carrier, Lp_meas_subgroup, set.mem_set_of_eq]

lemma mem_Lp_meas_iff_ae_measurable' {m m0 : measurable_space α} {μ : measure α} {f : Lp F p μ} :
  f ∈ Lp_meas F 𝕜 m p μ ↔ ae_measurable' m f μ :=
by rw [← set_like.mem_coe, ← submodule.mem_carrier, Lp_meas, set.mem_set_of_eq]

lemma Lp_meas.ae_measurable' {m m0 : measurable_space α} {μ : measure α} (f : Lp_meas F 𝕜 m p μ) :
  ae_measurable' m f μ :=
mem_Lp_meas_iff_ae_measurable'.mp f.mem

lemma mem_Lp_meas_self {m0 : measurable_space α} (μ : measure α) (f : Lp F p μ) :
  f ∈ Lp_meas F 𝕜 m0 p μ :=
mem_Lp_meas_iff_ae_measurable'.mpr (Lp.ae_measurable f)

lemma Lp_meas_subgroup_coe {m m0 : measurable_space α} {μ : measure α}
  {f : Lp_meas_subgroup F m p μ} :
  ⇑f = (f : Lp F p μ) :=
coe_fn_coe_base f

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

We define an `isometric` between `Lp_meas_subgroup` and the `Lp` space corresponding to the
measure `μ.trim hm`. As a consequence, the completeness of `Lp` implies completeness of
`Lp_meas_subgroup` (and `Lp_meas`). -/

variables {ι : Type*} {m m0 : measurable_space α} {μ : measure α}

/-- If `f` belongs to `Lp_meas_subgroup F m p μ`, then the measurable function it is almost
everywhere equal to (given by `ae_measurable.mk`) belongs to `ℒp` for the measure `μ.trim hm`. -/
lemma mem_ℒp_trim_of_mem_Lp_meas_subgroup (hm : m ≤ m0) (f : Lp F p μ)
  (hf_meas : f ∈ Lp_meas_subgroup F m p μ) :
  mem_ℒp (mem_Lp_meas_subgroup_iff_ae_measurable'.mp hf_meas).some p (μ.trim hm) :=
begin
  have hf : ae_measurable' m f μ, from (mem_Lp_meas_subgroup_iff_ae_measurable'.mp hf_meas),
  let g := hf.some,
  obtain ⟨hg, hfg⟩ := hf.some_spec,
  change mem_ℒp g p (μ.trim hm),
  refine ⟨hg.ae_measurable, _⟩,
  have h_snorm_fg : snorm g p (μ.trim hm) = snorm f p μ,
    by { rw snorm_trim hm hg, exact snorm_congr_ae hfg.symm, },
  rw h_snorm_fg,
  exact Lp.snorm_lt_top f,
end

/-- If `f` belongs to `Lp` for the measure `μ.trim hm`, then it belongs to the subgroup
`Lp_meas_subgroup F m p μ`. -/
lemma mem_Lp_meas_subgroup_to_Lp_of_trim (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) :
  (mem_ℒp_of_mem_ℒp_trim hm (Lp.mem_ℒp f)).to_Lp f ∈ Lp_meas_subgroup F m p μ :=
begin
  let hf_mem_ℒp := mem_ℒp_of_mem_ℒp_trim hm (Lp.mem_ℒp f),
  rw mem_Lp_meas_subgroup_iff_ae_measurable',
  refine ae_measurable'.congr _ (mem_ℒp.coe_fn_to_Lp hf_mem_ℒp).symm,
  refine ae_measurable'_of_ae_measurable'_trim hm _,
  exact (Lp.ae_measurable f),
end

variables (F p μ)
/-- Map from `Lp_meas_subgroup` to `Lp F p (μ.trim hm)`. -/
def Lp_meas_subgroup_to_Lp_trim (hm : m ≤ m0) (f : Lp_meas_subgroup F m p μ) : Lp F p (μ.trim hm) :=
mem_ℒp.to_Lp (mem_Lp_meas_subgroup_iff_ae_measurable'.mp f.mem).some
  (mem_ℒp_trim_of_mem_Lp_meas_subgroup hm f f.mem)

/-- Map from `Lp F p (μ.trim hm)` to `Lp_meas_subgroup`, inverse of
`Lp_meas_subgroup_to_Lp_trim`. -/
def Lp_trim_to_Lp_meas_subgroup (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) : Lp_meas_subgroup F m p μ :=
⟨(mem_ℒp_of_mem_ℒp_trim hm (Lp.mem_ℒp f)).to_Lp f, mem_Lp_meas_subgroup_to_Lp_of_trim hm f⟩

variables {F p μ}

lemma Lp_meas_subgroup_to_Lp_trim_ae_eq (hm : m ≤ m0) (f : Lp_meas_subgroup F m p μ) :
  Lp_meas_subgroup_to_Lp_trim F p μ hm f =ᵐ[μ] f :=
(ae_eq_of_ae_eq_trim (mem_ℒp.coe_fn_to_Lp (mem_ℒp_trim_of_mem_Lp_meas_subgroup hm ↑f f.mem))).trans
  (mem_Lp_meas_subgroup_iff_ae_measurable'.mp f.mem).some_spec.2.symm

lemma Lp_trim_to_Lp_meas_subgroup_ae_eq (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) :
  Lp_trim_to_Lp_meas_subgroup F p μ hm f =ᵐ[μ] f :=
mem_ℒp.coe_fn_to_Lp _

/-- `Lp_trim_to_Lp_meas_subgroup` is a right inverse of `Lp_meas_subgroup_to_Lp_trim`. -/
lemma Lp_meas_subgroup_to_Lp_trim_right_inv (hm : m ≤ m0) :
  function.right_inverse (Lp_trim_to_Lp_meas_subgroup F p μ hm)
    (Lp_meas_subgroup_to_Lp_trim F p μ hm) :=
begin
  intro f,
  ext1,
  refine ae_eq_trim_of_measurable hm (Lp.measurable _) (Lp.measurable _) _,
  exact (Lp_meas_subgroup_to_Lp_trim_ae_eq hm _).trans (Lp_trim_to_Lp_meas_subgroup_ae_eq hm _),
end

/-- `Lp_trim_to_Lp_meas_subgroup` is a left inverse of `Lp_meas_subgroup_to_Lp_trim`. -/
lemma Lp_meas_subgroup_to_Lp_trim_left_inv (hm : m ≤ m0) :
  function.left_inverse (Lp_trim_to_Lp_meas_subgroup F p μ hm)
    (Lp_meas_subgroup_to_Lp_trim F p μ hm) :=
begin
  intro f,
  ext1,
  ext1,
  rw ← Lp_meas_subgroup_coe,
  exact (Lp_trim_to_Lp_meas_subgroup_ae_eq hm _).trans (Lp_meas_subgroup_to_Lp_trim_ae_eq hm _),
end

lemma Lp_meas_subgroup_to_Lp_trim_add (hm : m ≤ m0) (f g : Lp_meas_subgroup F m p μ) :
  Lp_meas_subgroup_to_Lp_trim F p μ hm (f + g)
    = Lp_meas_subgroup_to_Lp_trim F p μ hm f + Lp_meas_subgroup_to_Lp_trim F p μ hm g :=
begin
  ext1,
  refine eventually_eq.trans _ (Lp.coe_fn_add _ _).symm,
  refine ae_eq_trim_of_measurable hm (Lp.measurable _) _ _,
  { exact @measurable.add _ _ _ _ m _ _ _ (Lp.measurable _) (Lp.measurable _), },
  refine (Lp_meas_subgroup_to_Lp_trim_ae_eq hm _).trans _,
  refine eventually_eq.trans _
    (eventually_eq.add (Lp_meas_subgroup_to_Lp_trim_ae_eq hm f).symm
      (Lp_meas_subgroup_to_Lp_trim_ae_eq hm g).symm),
  refine (Lp.coe_fn_add _ _).trans _,
  simp_rw Lp_meas_subgroup_coe,
  exact eventually_of_forall (λ x, by refl),
end

lemma Lp_meas_subgroup_to_Lp_trim_neg (hm : m ≤ m0) (f : Lp_meas_subgroup F m p μ) :
  Lp_meas_subgroup_to_Lp_trim F p μ hm (-f)
    = -Lp_meas_subgroup_to_Lp_trim F p μ hm f :=
begin
  ext1,
  refine eventually_eq.trans _ (Lp.coe_fn_neg _).symm,
  refine ae_eq_trim_of_measurable hm (Lp.measurable _) _ _,
  { exact @measurable.neg _ _ _ _ _ m _ (Lp.measurable _), },
  refine (Lp_meas_subgroup_to_Lp_trim_ae_eq hm _).trans _,
  refine eventually_eq.trans _
    (eventually_eq.neg (Lp_meas_subgroup_to_Lp_trim_ae_eq hm f).symm),
  refine (Lp.coe_fn_neg _).trans _,
  simp_rw Lp_meas_subgroup_coe,
  exact eventually_of_forall (λ x, by refl),
end

lemma Lp_meas_subgroup_to_Lp_trim_sub (hm : m ≤ m0) (f g : Lp_meas_subgroup F m p μ) :
  Lp_meas_subgroup_to_Lp_trim F p μ hm (f - g)
    = Lp_meas_subgroup_to_Lp_trim F p μ hm f - Lp_meas_subgroup_to_Lp_trim F p μ hm g :=
by rw [sub_eq_add_neg, sub_eq_add_neg, Lp_meas_subgroup_to_Lp_trim_add,
  Lp_meas_subgroup_to_Lp_trim_neg]

/-- `Lp_meas_subgroup_to_Lp_trim` preserves the norm. -/
lemma Lp_meas_subgroup_to_Lp_trim_norm_map [hp : fact (1 ≤ p)] (hm : m ≤ m0)
  (f : Lp_meas_subgroup F m p μ) :
  ∥Lp_meas_subgroup_to_Lp_trim F p μ hm f∥ = ∥f∥ :=
begin
  rw [Lp.norm_def, snorm_trim hm (Lp.measurable _)],
  swap, { apply_instance, },
  rw [snorm_congr_ae (Lp_meas_subgroup_to_Lp_trim_ae_eq hm _), Lp_meas_subgroup_coe, ← Lp.norm_def],
  congr,
end

lemma isometry_Lp_meas_subgroup_to_Lp_trim [hp : fact (1 ≤ p)] (hm : m ≤ m0) :
  isometry (Lp_meas_subgroup_to_Lp_trim F p μ hm) :=
begin
  rw isometry_emetric_iff_metric,
  intros f g,
  rw [dist_eq_norm, ← Lp_meas_subgroup_to_Lp_trim_sub, Lp_meas_subgroup_to_Lp_trim_norm_map,
    dist_eq_norm],
end

variables (F p μ)
/-- `Lp_meas_subgroup` and `Lp F p (μ.trim hm)` are isometric. -/
def Lp_meas_subgroup_to_Lp_trim_iso [hp : fact (1 ≤ p)] (hm : m ≤ m0) :
  Lp_meas_subgroup F m p μ ≃ᵢ Lp F p (μ.trim hm) :=
{ to_fun    := Lp_meas_subgroup_to_Lp_trim F p μ hm,
  inv_fun   := Lp_trim_to_Lp_meas_subgroup F p μ hm,
  left_inv  := Lp_meas_subgroup_to_Lp_trim_left_inv hm,
  right_inv := Lp_meas_subgroup_to_Lp_trim_right_inv hm,
  isometry_to_fun := isometry_Lp_meas_subgroup_to_Lp_trim hm, }

variables (𝕜)
/-- `Lp_meas_subgroup` and `Lp_meas` are isometric. -/
def Lp_meas_subgroup_to_Lp_meas_iso [hp : fact (1 ≤ p)] :
  Lp_meas_subgroup F m p μ ≃ᵢ Lp_meas F 𝕜 m p μ :=
isometric.refl (Lp_meas_subgroup F m p μ)
variables {F 𝕜 p μ}

instance [hm : fact (m ≤ m0)] [complete_space F] [hp : fact (1 ≤ p)] :
  complete_space (Lp_meas_subgroup F m p μ) :=
by { rw (Lp_meas_subgroup_to_Lp_trim_iso F p μ hm.elim).complete_space_iff, apply_instance, }

instance [hm : fact (m ≤ m0)] [complete_space F] [hp : fact (1 ≤ p)] :
  complete_space (Lp_meas F 𝕜 m p μ) :=
by { rw (Lp_meas_subgroup_to_Lp_meas_iso F 𝕜 p μ).symm.complete_space_iff, apply_instance, }

lemma is_complete_ae_measurable' [hp : fact (1 ≤ p)] [complete_space F] (hm : m ≤ m0) :
  is_complete {f : Lp F p μ | ae_measurable' m f μ} :=
begin
  rw ← complete_space_coe_iff_is_complete,
  haveI : fact (m ≤ m0) := ⟨hm⟩,
  change complete_space (Lp_meas_subgroup F m p μ),
  apply_instance,
end

lemma is_closed_ae_measurable' [hp : fact (1 ≤ p)] [complete_space F] (hm : m ≤ m0) :
  is_closed {f : Lp F p μ | ae_measurable' m f μ} :=
is_complete.is_closed (is_complete_ae_measurable' hm)

end complete_subspace

section strongly_measurable

variables {m m0 : measurable_space α} {μ : measure α}

/-- We do not get `ae_fin_strongly_measurable f (μ.trim hm)`, since we don't have
`f =ᵐ[μ.trim hm] Lp_meas_to_Lp_trim F 𝕜 p μ hm f` but only the weaker
`f =ᵐ[μ] Lp_meas_to_Lp_trim F 𝕜 p μ hm f`. -/
lemma Lp_meas.ae_fin_strongly_measurable' (hm : m ≤ m0) (f : Lp_meas F 𝕜 m p μ) (hp_ne_zero : p ≠ 0)
  (hp_ne_top : p ≠ ∞) :
  ∃ g, fin_strongly_measurable g (μ.trim hm) ∧ f =ᵐ[μ] g :=
⟨Lp_meas_subgroup_to_Lp_trim F p μ hm f, Lp.fin_strongly_measurable _ hp_ne_zero hp_ne_top,
  (Lp_meas_subgroup_to_Lp_trim_ae_eq hm f).symm⟩

end strongly_measurable

end Lp_meas


section uniqueness_of_conditional_expectation

/-! ## Uniqueness of the conditional expectation -/

variables {m m0 : measurable_space α} {μ : measure α} [borel_space 𝕜]

lemma Lp_meas.ae_eq_zero_of_forall_set_integral_eq_zero
  (hm : m ≤ m0) (f : Lp_meas E' 𝕜 m p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
  (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s : set α, measurable_set[m] s → μ s < ∞ → ∫ x in s, f x ∂μ = 0) :
  f =ᵐ[μ] 0 :=
begin
  obtain ⟨g, hg_sm, hfg⟩ := Lp_meas.ae_fin_strongly_measurable' hm f hp_ne_zero hp_ne_top,
  refine hfg.trans _,
  refine ae_eq_zero_of_forall_set_integral_eq_of_fin_strongly_measurable_trim hm _ _ hg_sm,
  { intros s hs hμs,
    have hfg_restrict : f =ᵐ[μ.restrict s] g, from ae_restrict_of_ae hfg,
    rw [integrable_on, integrable_congr hfg_restrict.symm],
    exact hf_int_finite s hs hμs, },
  { intros s hs hμs,
    have hfg_restrict : f =ᵐ[μ.restrict s] g, from ae_restrict_of_ae hfg,
    rw integral_congr_ae hfg_restrict.symm,
    exact hf_zero s hs hμs, },
end

include 𝕜

lemma Lp.ae_eq_zero_of_forall_set_integral_eq_zero'
  (hm : m ≤ m0) (f : Lp E' p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
  (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s : set α, measurable_set[m] s → μ s < ∞ → ∫ x in s, f x ∂μ = 0)
  (hf_meas : ae_measurable' m f μ) :
  f =ᵐ[μ] 0 :=
begin
  let f_meas : Lp_meas E' 𝕜 m p μ := ⟨f, hf_meas⟩,
  have hf_f_meas : f =ᵐ[μ] f_meas, by simp only [coe_fn_coe_base, subtype.coe_mk],
  refine hf_f_meas.trans _,
  refine Lp_meas.ae_eq_zero_of_forall_set_integral_eq_zero hm f_meas hp_ne_zero hp_ne_top _ _,
  { intros s hs hμs,
    have hfg_restrict : f =ᵐ[μ.restrict s] f_meas, from ae_restrict_of_ae hf_f_meas,
    rw [integrable_on, integrable_congr hfg_restrict.symm],
    exact hf_int_finite s hs hμs, },
  { intros s hs hμs,
    have hfg_restrict : f =ᵐ[μ.restrict s] f_meas, from ae_restrict_of_ae hf_f_meas,
    rw integral_congr_ae hfg_restrict.symm,
    exact hf_zero s hs hμs, },
end

/-- **Uniqueness of the conditional expectation** -/
lemma Lp.ae_eq_of_forall_set_integral_eq'
  (hm : m ≤ m0) (f g : Lp E' p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
  (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → integrable_on f s μ)
  (hg_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → integrable_on g s μ)
  (hfg : ∀ s : set α, measurable_set[m] s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ)
  (hf_meas : ae_measurable' m f μ) (hg_meas : ae_measurable' m g μ) :
  f =ᵐ[μ] g :=
begin
  suffices h_sub : ⇑(f-g) =ᵐ[μ] 0,
    by { rw ← sub_ae_eq_zero, exact (Lp.coe_fn_sub f g).symm.trans h_sub, },
  have hfg' : ∀ s : set α, measurable_set[m] s → μ s < ∞ → ∫ x in s, (f - g) x ∂μ = 0,
  { intros s hs hμs,
    rw integral_congr_ae (ae_restrict_of_ae (Lp.coe_fn_sub f g)),
    rw integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs),
    exact sub_eq_zero.mpr (hfg s hs hμs), },
  have hfg_int : ∀ s, measurable_set[m] s → μ s < ∞ → integrable_on ⇑(f-g) s μ,
  { intros s hs hμs,
    rw [integrable_on, integrable_congr (ae_restrict_of_ae (Lp.coe_fn_sub f g))],
    exact (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs), },
  have hfg_meas : ae_measurable' m ⇑(f - g) μ,
    from ae_measurable'.congr (hf_meas.sub hg_meas) (Lp.coe_fn_sub f g).symm,
  exact Lp.ae_eq_zero_of_forall_set_integral_eq_zero' hm (f-g) hp_ne_zero hp_ne_top hfg_int hfg'
    hfg_meas,
end

omit 𝕜

lemma ae_eq_of_forall_set_integral_eq_of_sigma_finite' (hm : m ≤ m0) [sigma_finite (μ.trim hm)]
  {f g : α → F'}
  (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → integrable_on f s μ)
  (hg_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → integrable_on g s μ)
  (hfg_eq : ∀ s : set α, measurable_set[m] s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ)
  (hfm : ae_measurable' m f μ) (hgm : ae_measurable' m g μ) :
  f =ᵐ[μ] g :=
begin
  rw ← ae_eq_trim_iff_of_ae_measurable' hm hfm hgm,
  have hf_mk_int_finite : ∀ s, measurable_set[m] s → μ.trim hm s < ∞ →
    @integrable_on _ _ m _ _ (hfm.mk f) s (μ.trim hm),
  { intros s hs hμs,
    rw trim_measurable_set_eq hm hs at hμs,
    rw [integrable_on, restrict_trim hm _ hs],
    refine integrable.trim hm _ hfm.measurable_mk,
    exact integrable.congr (hf_int_finite s hs hμs) (ae_restrict_of_ae hfm.ae_eq_mk), },
  have hg_mk_int_finite : ∀ s, measurable_set[m] s → μ.trim hm s < ∞ →
    @integrable_on _ _ m _ _ (hgm.mk g) s (μ.trim hm),
  { intros s hs hμs,
    rw trim_measurable_set_eq hm hs at hμs,
    rw [integrable_on, restrict_trim hm _ hs],
    refine integrable.trim hm _ hgm.measurable_mk,
    exact integrable.congr (hg_int_finite s hs hμs) (ae_restrict_of_ae hgm.ae_eq_mk), },
  have hfg_mk_eq : ∀ s : set α, measurable_set[m] s → μ.trim hm s < ∞ →
    ∫ x in s, (hfm.mk f x) ∂(μ.trim hm) = ∫ x in s, (hgm.mk g x) ∂(μ.trim hm),
  { intros s hs hμs,
    rw trim_measurable_set_eq hm hs at hμs,
    rw [restrict_trim hm _ hs, ← integral_trim hm hfm.measurable_mk,
      ← integral_trim hm hgm.measurable_mk, integral_congr_ae (ae_restrict_of_ae hfm.ae_eq_mk.symm),
      integral_congr_ae (ae_restrict_of_ae hgm.ae_eq_mk.symm)],
    exact hfg_eq s hs hμs, },
  exact ae_eq_of_forall_set_integral_eq_of_sigma_finite hf_mk_int_finite hg_mk_int_finite hfg_mk_eq,
end

end uniqueness_of_conditional_expectation


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
  rw [integral_norm_eq_pos_sub_neg (hg.mono hm le_rfl) hgi, integral_norm_eq_pos_sub_neg hf hfi],
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

/-! ## Conditional expectation in L2

We define a conditional expectation in `L2`: it is the orthogonal projection on the subspace
`Lp_meas`. -/

section condexp_L2

local attribute [instance] fact_one_le_two_ennreal

variables [complete_space E] [borel_space 𝕜] {m m0 : measurable_space α} {μ : measure α}
  {s t : set α}

local notation `⟪`x`, `y`⟫` := @inner 𝕜 E _ x y
local notation `⟪`x`, `y`⟫₂` := @inner 𝕜 (α →₂[μ] E) _ x y

variables (𝕜)
/-- Conditional expectation of a function in L2 with respect to a sigma-algebra -/
def condexp_L2 (hm : m ≤ m0) : (α →₂[μ] E) →L[𝕜] (Lp_meas E 𝕜 m 2 μ) :=
@orthogonal_projection 𝕜 (α →₂[μ] E) _ _ (Lp_meas E 𝕜 m 2 μ)
  (by { haveI : fact (m ≤ m0) := ⟨hm⟩, exact infer_instance, })
variables {𝕜}

lemma ae_measurable'_condexp_L2 (hm : m ≤ m0) (f : α →₂[μ] E) :
  ae_measurable' m (condexp_L2 𝕜 hm f) μ :=
Lp_meas.ae_measurable' _

lemma integrable_on_condexp_L2_of_measure_ne_top (hm : m ≤ m0) (hμs : μ s ≠ ∞) (f : α →₂[μ] E) :
  integrable_on (condexp_L2 𝕜 hm f) s μ :=
integrable_on_Lp_of_measure_ne_top ((condexp_L2 𝕜 hm f) : α →₂[μ] E)
  fact_one_le_two_ennreal.elim hμs

lemma integrable_condexp_L2_of_is_finite_measure (hm : m ≤ m0) [is_finite_measure μ]
  {f : α →₂[μ] E} :
  integrable (condexp_L2 𝕜 hm f) μ :=
integrable_on_univ.mp $ integrable_on_condexp_L2_of_measure_ne_top hm (measure_ne_top _ _) f

lemma norm_condexp_L2_le_one (hm : m ≤ m0) : ∥@condexp_L2 α E 𝕜 _ _ _ _ _ _ _ _ _ _ μ hm∥ ≤ 1 :=
by { haveI : fact (m ≤ m0) := ⟨hm⟩, exact orthogonal_projection_norm_le _, }

lemma norm_condexp_L2_le (hm : m ≤ m0) (f : α →₂[μ] E) : ∥condexp_L2 𝕜 hm f∥ ≤ ∥f∥ :=
((@condexp_L2 _ E 𝕜 _ _ _ _ _ _ _ _ _ _ μ hm).le_op_norm f).trans
  (mul_le_of_le_one_left (norm_nonneg _) (norm_condexp_L2_le_one hm))

lemma snorm_condexp_L2_le (hm : m ≤ m0) (f : α →₂[μ] E) :
  snorm (condexp_L2 𝕜 hm f) 2 μ ≤ snorm f 2 μ :=
begin
  rw [Lp_meas_coe, ← ennreal.to_real_le_to_real (Lp.snorm_ne_top _) (Lp.snorm_ne_top _),
    ← Lp.norm_def, ← Lp.norm_def, submodule.norm_coe],
  exact norm_condexp_L2_le hm f,
end

lemma norm_condexp_L2_coe_le (hm : m ≤ m0) (f : α →₂[μ] E) :
  ∥(condexp_L2 𝕜 hm f : α →₂[μ] E)∥ ≤ ∥f∥ :=
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

lemma inner_condexp_L2_eq_inner_fun (hm : m ≤ m0) (f g : α →₂[μ] E) (hg : ae_measurable' m g μ) :
  ⟪(condexp_L2 𝕜 hm f : α →₂[μ] E), g⟫₂ = ⟪f, g⟫₂ :=
begin
  symmetry,
  rw [← sub_eq_zero, ← inner_sub_left, condexp_L2],
  simp only [mem_Lp_meas_iff_ae_measurable'.mpr hg, orthogonal_projection_inner_eq_zero],
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
  ∫⁻ x in s, ∥condexp_L2 ℝ hm f x∥₊ ∂μ ≤ ∫⁻ x in s, ∥f x∥₊ ∂μ :=
begin
  let h_meas := Lp_meas.ae_measurable' (condexp_L2 ℝ hm f),
  let g := h_meas.some,
  have hg_meas : measurable[m] g, from h_meas.some_spec.1,
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
    rw ← integral_condexp_L2_eq_of_fin_meas_real f ht hμt.ne,
    exact set_integral_congr_ae (hm t ht) (hg_eq.mono (λ x hx _, hx)), },
end

lemma condexp_L2_ae_eq_zero_of_ae_eq_zero (hs : measurable_set[m] s) (hμs : μ s ≠ ∞)
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
  refine (lintegral_nnnorm_condexp_L2_le hs hμs f).trans (le_of_eq _),
  rw lintegral_eq_zero_iff,
  { refine hf.mono (λ x hx, _),
    dsimp only,
    rw hx,
    simp, },
  { exact (Lp.measurable _).nnnorm.coe_nnreal_ennreal, },
end

lemma lintegral_nnnorm_condexp_L2_indicator_le_real
  (hs : measurable_set s) (hμs : μ s ≠ ∞) (ht : measurable_set[m] t) (hμt : μ t ≠ ∞) :
  ∫⁻ a in t, ∥condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)) a∥₊ ∂μ ≤ μ (s ∩ t) :=
begin
  refine (lintegral_nnnorm_condexp_L2_le ht hμt _).trans (le_of_eq _),
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
  refine Lp.ae_eq_of_forall_set_integral_eq' hm _ _ ennreal.zero_lt_two.ne.symm ennreal.coe_ne_top
    (λ s hs hμs, integrable_on_condexp_L2_of_measure_ne_top hm hμs.ne _) _ _ _ _,
  { intros s hs hμs,
    rw [integrable_on, integrable_congr (ae_restrict_of_ae h_eq)],
    exact (integrable_on_condexp_L2_of_measure_ne_top hm hμs.ne _).const_inner _, },
  { intros s hs hμs,
    rw [← Lp_meas_coe, integral_condexp_L2_eq_of_fin_meas_real _ hs hμs.ne,
      integral_congr_ae (ae_restrict_of_ae h_eq), Lp_meas_coe,
      ← L2.inner_indicator_const_Lp_eq_set_integral_inner ↑(condexp_L2 𝕜 hm f) (hm s hs) c hμs.ne,
      ← inner_condexp_L2_left_eq_right, condexp_L2_indicator_of_measurable,
      L2.inner_indicator_const_Lp_eq_set_integral_inner f (hm s hs) c hμs.ne,
      set_integral_congr_ae (hm s hs)
        ((mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).const_inner c)).mono (λ x hx hxs, hx))], },
  { rw ← Lp_meas_coe, exact Lp_meas.ae_measurable' _, },
  { refine ae_measurable'.congr _ h_eq.symm, exact (Lp_meas.ae_measurable' _).const_inner _, },
end

/-- `condexp_L2` verifies the equality of integrals defining the conditional expectation. -/
lemma integral_condexp_L2_eq [is_scalar_tower ℝ 𝕜 E'] (hm : m ≤ m0)
  (f : Lp E' 2 μ) (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) :
  ∫ x in s, condexp_L2 𝕜 hm f x ∂μ = ∫ x in s, f x ∂μ :=
begin
  rw [← sub_eq_zero, Lp_meas_coe, ← integral_sub'
      (integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs)
      (integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs)],
  refine integral_eq_zero_of_forall_integral_inner_eq_zero _ _ _,
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

variables {E'' 𝕜' : Type*} [is_R_or_C 𝕜'] [measurable_space 𝕜'] [borel_space 𝕜']
  [measurable_space E''] [inner_product_space 𝕜' E''] [borel_space E'']
  [second_countable_topology E''] [complete_space E''] [normed_space ℝ E'']
  [is_scalar_tower ℝ 𝕜 E'] [is_scalar_tower ℝ 𝕜' E'']

variables (𝕜 𝕜')
lemma condexp_L2_comp_continuous_linear_map (hm : m ≤ m0) (T : E' →L[ℝ] E'') (f : α →₂[μ] E') :
  (condexp_L2 𝕜' hm (T.comp_Lp f) : α →₂[μ] E'') =ᵐ[μ] T.comp_Lp (condexp_L2 𝕜 hm f : α →₂[μ] E') :=
begin
  refine Lp.ae_eq_of_forall_set_integral_eq' hm _ _ ennreal.zero_lt_two.ne.symm ennreal.coe_ne_top
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
  { rw ← Lp_meas_coe, exact Lp_meas.ae_measurable' _, },
  { have h_coe := T.coe_fn_comp_Lp (condexp_L2 𝕜 hm f : α →₂[μ] E'),
    rw ← eventually_eq at h_coe,
    refine ae_measurable'.congr _ h_coe.symm,
    exact (Lp_meas.ae_measurable' (condexp_L2 𝕜 hm f)).measurable_comp T.measurable, },
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
  (hμs : μ s ≠ ∞) (x : E') {t : set α} (ht : @measurable_set _ m t) (hμt : μ t ≠ ∞) :
  ∫⁻ a in t, ∥condexp_L2 𝕜 hm (indicator_const_Lp 2 hs hμs x) a∥₊ ∂μ ≤ μ (s ∩ t) * ∥x∥₊ :=
calc ∫⁻ a in t, ∥condexp_L2 𝕜 hm (indicator_const_Lp 2 hs hμs x) a∥₊ ∂μ
    = ∫⁻ a in t, ∥(condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)) a) • x∥₊ ∂μ :
set_lintegral_congr_fun (hm t ht)
  ((condexp_L2_indicator_ae_eq_smul 𝕜 hm hs hμs x).mono (λ a ha hat, by rw ha))
... = ∫⁻ a in t, ∥condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)) a∥₊ ∂μ * ∥x∥₊ :
begin
  simp_rw [nnnorm_smul, ennreal.coe_mul],
  rw [lintegral_mul_const, Lp_meas_coe],
  exact (Lp.measurable _).nnnorm.coe_nnreal_ennreal,
end
... ≤ μ (s ∩ t) * ∥x∥₊ :
  ennreal.mul_le_mul (lintegral_nnnorm_condexp_L2_indicator_le_real hs hμs ht hμt) le_rfl

lemma lintegral_nnnorm_condexp_L2_indicator_le (hm : m ≤ m0) (hs : measurable_set s)
  (hμs : μ s ≠ ∞) (x : E') [sigma_finite (μ.trim hm)] :
  ∫⁻ a, ∥condexp_L2 𝕜 hm (indicator_const_Lp 2 hs hμs x) a∥₊ ∂μ ≤ μ s * ∥x∥₊ :=
begin
  refine lintegral_le_of_forall_fin_meas_le' hm (μ s * ∥x∥₊) _ (λ t ht hμt, _),
  { rw Lp_meas_coe,
    exact (Lp.ae_measurable _).nnnorm.coe_nnreal_ennreal, },
  refine (set_lintegral_nnnorm_condexp_L2_indicator_le hm hs hμs x ht hμt).trans _,
  refine ennreal.mul_le_mul _ le_rfl,
  exact measure_mono (set.inter_subset_left _ _),
end

/-- If the measure `μ.trim hm` is sigma-finite, then the conditional expectation of a measurable set
with finite measure is integrable. -/
lemma integrable_condexp_L2_indicator (hm : m ≤ m0) [sigma_finite (μ.trim hm)]
  (hs : measurable_set s) (hμs : μ s ≠ ∞) (x : E') :
  integrable (condexp_L2 𝕜 hm (indicator_const_Lp 2 hs hμs x)) μ :=
begin
  refine integrable_of_forall_fin_meas_le' hm (μ s * ∥x∥₊)
    (ennreal.mul_lt_top hμs ennreal.coe_ne_top) _ _,
  { rw Lp_meas_coe, exact Lp.ae_measurable _, },
  { refine λ t ht hμt, (set_lintegral_nnnorm_condexp_L2_indicator_le hm hs hμs x ht hμt).trans _,
    exact ennreal.mul_le_mul (measure_mono (set.inter_subset_left _ _)) le_rfl, },
end

end condexp_L2_indicator

section condexp_ind_smul

variables [normed_space ℝ G] {hm : m ≤ m0}

/-- Conditional expectation of the indicator of a measurable set with finite measure, in L2. -/
def condexp_ind_smul (hm : m ≤ m0) (hs : measurable_set s) (hμs : μ s ≠ ∞) (x : G) : Lp G 2 μ :=
(to_span_singleton ℝ x).comp_LpL 2 μ (condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)))

lemma ae_measurable'_condexp_ind_smul (hm : m ≤ m0) (hs : measurable_set s) (hμs : μ s ≠ ∞)
  (x : G) :
  ae_measurable' m (condexp_ind_smul hm hs hμs x) μ :=
begin
  have h : ae_measurable' m (condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ))) μ,
    from ae_measurable'_condexp_L2 _ _,
  rw condexp_ind_smul,
  suffices : ae_measurable' m
    ((to_span_singleton ℝ x) ∘ (condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)))) μ,
  { refine ae_measurable'.congr this _,
    refine eventually_eq.trans _ (coe_fn_comp_LpL _ _).symm,
    rw Lp_meas_coe, },
  exact ae_measurable'.measurable_comp (to_span_singleton ℝ x).measurable h,
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
  (to_span_singleton ℝ x).smul_comp_LpL_apply c
  ↑(condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)))]

lemma condexp_ind_smul_ae_eq_smul (hm : m ≤ m0) (hs : measurable_set s) (hμs : μ s ≠ ∞) (x : G) :
  condexp_ind_smul hm hs hμs x
    =ᵐ[μ] λ a, (condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)) a) • x :=
(to_span_singleton ℝ x).coe_fn_comp_LpL _

lemma set_lintegral_nnnorm_condexp_ind_smul_le (hm : m ≤ m0) (hs : measurable_set s)
  (hμs : μ s ≠ ∞) (x : G) {t : set α} (ht : @measurable_set _ m t) (hμt : μ t ≠ ∞) :
  ∫⁻ a in t, ∥condexp_ind_smul hm hs hμs x a∥₊ ∂μ ≤ μ (s ∩ t) * ∥x∥₊ :=
calc ∫⁻ a in t, ∥condexp_ind_smul hm hs hμs x a∥₊ ∂μ
    = ∫⁻ a in t, ∥condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)) a • x∥₊ ∂μ :
set_lintegral_congr_fun (hm t ht)
  ((condexp_ind_smul_ae_eq_smul hm hs hμs x).mono (λ a ha hat, by rw ha ))
... = ∫⁻ a in t, ∥condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)) a∥₊ ∂μ * ∥x∥₊ :
begin
  simp_rw [nnnorm_smul, ennreal.coe_mul],
  rw [lintegral_mul_const, Lp_meas_coe],
  exact (Lp.measurable _).nnnorm.coe_nnreal_ennreal,
end
... ≤ μ (s ∩ t) * ∥x∥₊ :
  ennreal.mul_le_mul (lintegral_nnnorm_condexp_L2_indicator_le_real hs hμs ht hμt) le_rfl

lemma lintegral_nnnorm_condexp_ind_smul_le (hm : m ≤ m0) (hs : measurable_set s)
  (hμs : μ s ≠ ∞) (x : G) [sigma_finite (μ.trim hm)] :
  ∫⁻ a, ∥condexp_ind_smul hm hs hμs x a∥₊ ∂μ ≤ μ s * ∥x∥₊ :=
begin
  refine lintegral_le_of_forall_fin_meas_le' hm (μ s * ∥x∥₊) _ (λ t ht hμt, _),
  { exact (Lp.ae_measurable _).nnnorm.coe_nnreal_ennreal, },
  refine (set_lintegral_nnnorm_condexp_ind_smul_le hm hs hμs x ht hμt).trans _,
  refine ennreal.mul_le_mul _ le_rfl,
  exact measure_mono (set.inter_subset_left _ _),
end

/-- If the measure `μ.trim hm` is sigma-finite, then the conditional expectation of a measurable set
with finite measure is integrable. -/
lemma integrable_condexp_ind_smul (hm : m ≤ m0) [sigma_finite (μ.trim hm)]
  (hs : measurable_set s) (hμs : μ s ≠ ∞) (x : G) :
  integrable (condexp_ind_smul hm hs hμs x) μ :=
begin
  refine integrable_of_forall_fin_meas_le' hm (μ s * ∥x∥₊)
    (ennreal.mul_lt_top hμs ennreal.coe_ne_top) _ _,
  { exact Lp.ae_measurable _, },
  { refine λ t ht hμt, (set_lintegral_nnnorm_condexp_ind_smul_le hm hs hμs x ht hμt).trans _,
    exact ennreal.mul_le_mul (measure_mono (set.inter_subset_left _ _)) le_rfl, },
end

lemma condexp_ind_smul_empty {x : G} :
  condexp_ind_smul hm measurable_set.empty
    ((@measure_empty _ _ μ).le.trans_lt ennreal.coe_lt_top).ne x = 0 :=
begin
  rw [condexp_ind_smul, indicator_const_empty],
  simp only [coe_fn_coe_base, submodule.coe_zero, continuous_linear_map.map_zero],
end

end condexp_ind_smul

end condexp_L2

section condexp_ind

/-! ## Conditional expectation of an indicator as a condinuous linear map.

The goal of this section is to build
`condexp_ind (hm : m ≤ m0) (μ : measure α) (s : set s) : G →L[ℝ] α →₁[μ] G`, which
takes `x : G` to the conditional expectation of the indicator of the set `s` with value `x`,
seen as an element of `α →₁[μ] G`.
-/

local attribute [instance] fact_one_le_two_ennreal

variables {m m0 : measurable_space α} {μ : measure α} [borel_space 𝕜] [is_scalar_tower ℝ 𝕜 E']
  {s t : set α} [normed_space ℝ G]

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
  ∥condexp_ind_L1_fin hm hs hμs x∥ ≤ (μ s).to_real * ∥x∥ :=
begin
  have : 0 ≤ ∫ (a : α), ∥condexp_ind_L1_fin hm hs hμs x a∥ ∂μ,
    from integral_nonneg (λ a, norm_nonneg _),
  rw [L1.norm_eq_integral_norm, ← ennreal.to_real_of_real (norm_nonneg x), ← ennreal.to_real_mul,
    ← ennreal.to_real_of_real this, ennreal.to_real_le_to_real ennreal.of_real_ne_top
      (ennreal.mul_ne_top hμs ennreal.of_real_ne_top),
    of_real_integral_norm_eq_lintegral_nnnorm],
  swap, { rw [← mem_ℒp_one_iff_integrable], exact Lp.mem_ℒp _, },
  have h_eq : ∫⁻ a, ∥condexp_ind_L1_fin hm hs hμs x a∥₊ ∂μ
    = ∫⁻ a, nnnorm (condexp_ind_smul hm hs hμs x a) ∂μ,
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
  ∥condexp_ind_L1 hm μ s x∥ ≤ (μ s).to_real * ∥x∥ :=
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

lemma ae_measurable'_condexp_ind (hs : measurable_set s) (hμs : μ s ≠ ∞) (x : G) :
  ae_measurable' m (condexp_ind hm μ s x) μ :=
ae_measurable'.congr (ae_measurable'_condexp_ind_smul hm hs hμs x)
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

lemma norm_condexp_ind_apply_le (x : G) : ∥condexp_ind hm μ s x∥ ≤ (μ s).to_real * ∥x∥ :=
norm_condexp_ind_L1_le x

lemma norm_condexp_ind_le : ∥(condexp_ind hm μ s : G →L[ℝ] α →₁[μ] G)∥ ≤ (μ s).to_real :=
continuous_linear_map.op_norm_le_bound _ ennreal.to_real_nonneg norm_condexp_ind_apply_le

lemma condexp_ind_disjoint_union_apply (hs : measurable_set s) (ht : measurable_set t)
  (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) (hst : s ∩ t = ∅) (x : G) :
  condexp_ind hm μ (s ∪ t) x = condexp_ind hm μ s x + condexp_ind hm μ t x :=
condexp_ind_L1_disjoint_union hs ht hμs hμt hst x

lemma condexp_ind_disjoint_union (hs : measurable_set s) (ht : measurable_set t) (hμs : μ s ≠ ∞)
  (hμt : μ t ≠ ∞) (hst : s ∩ t = ∅) :
  (condexp_ind hm μ (s ∪ t) : G →L[ℝ] α →₁[μ] G) = condexp_ind hm μ s + condexp_ind hm μ t :=
by { ext1, push_cast, exact condexp_ind_disjoint_union_apply hs ht hμs hμt hst x, }

end condexp_ind

end measure_theory
