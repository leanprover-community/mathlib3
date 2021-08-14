/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import measure_theory.l2_space
import measure_theory.strongly_measurable
import analysis.normed_space.dual
import analysis.normed_space.hahn_banach

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

lemma neg [has_neg β] [has_measurable_neg β] {f : α → β}
  (hfm : ae_measurable' m f μ) :
  ae_measurable' m (-f) μ :=
begin
  rcases hfm with ⟨f', hf'_meas, hf_ae⟩,
  refine ⟨-f', @measurable.neg _ m _ _ _ _ _ hf'_meas, hf_ae.mono (λ x hx, _)⟩,
  simp_rw pi.neg_apply,
  rw hx,
end

lemma sub [has_sub β] [has_measurable_sub₂ β] {f g : α → β}
  (hfm : ae_measurable' m f μ) (hgm : ae_measurable' m g μ) :
  ae_measurable' m (f - g) μ :=
begin
  rcases hfm with ⟨f', hf'_meas, hf_ae⟩,
  rcases hgm with ⟨g', hg'_meas, hg_ae⟩,
  refine ⟨f'-g', @measurable.sub _ m _ _ _ _ _ _ hf'_meas hg'_meas,
    hf_ae.mp (hg_ae.mono (λ x hx1 hx2, _))⟩,
  simp_rw pi.sub_apply,
  rw [hx1, hx2],
end

lemma const_smul [has_scalar 𝕜 β] [has_measurable_smul 𝕜 β] (c : 𝕜) (hf : ae_measurable' m f μ) :
  ae_measurable' m (c • f) μ :=
begin
  rcases hf with ⟨f', h_f'_meas, hff'⟩,
  refine ⟨c • f', @measurable.const_smul α m _ _ _ _ _ _ f' h_f'_meas c, _⟩,
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
  (hm : m ≤ m0) (hfm : ae_measurable' m f μ) (hgm : ae_measurable' m g μ):
  hfm.mk f =ᶠ[@measure.ae _ m (μ.trim hm)] hgm.mk g ↔ f =ᵐ[μ] g :=
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

section tools

variables {m : measurable_space α} {μ : measure α} {𝕜' : Type*} [is_R_or_C 𝕜']

lemma ae_eq_zero_of_forall_inner [inner_product_space 𝕜' γ] [second_countable_topology γ]
  {f : α → γ} (hf : ∀ c : γ, ∀ᵐ x ∂μ, inner c (f x) = (0 : 𝕜')) :
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

local notation `⟪`x`, `y`⟫` := y x
open normed_space

variables (𝕜)
lemma eq_zero_of_forall_dual [normed_group γ] [normed_space 𝕜' γ] {x : γ}
  (h : ∀ c : dual 𝕜' γ, ⟪x, c⟫ = (0 : 𝕜')) :
  x = 0 :=
begin
  by_cases hγ : nontrivial γ,
  { haveI : nontrivial γ := hγ,
    obtain ⟨g, norm_g, gx_eq⟩ := @exists_dual_vector' 𝕜' _ _ _ _ _ x,
    rw h at gx_eq,
    exact norm_eq_zero.mp ((@is_R_or_C.of_real_eq_zero 𝕜' _ _).mp gx_eq.symm), },
  { haveI : subsingleton γ := not_nontrivial_iff_subsingleton.mp hγ,
    exact subsingleton.elim x 0, },
end
variables {𝕜}

lemma ae_eq_zero_of_forall_dual [normed_group γ] [normed_space 𝕜' γ]
  [second_countable_topology (dual 𝕜' γ)]
  {f : α → γ} (hf : ∀ c : dual 𝕜' γ, ∀ᵐ x ∂μ, ⟪f x, c⟫ = (0 : 𝕜')) :
  f =ᵐ[μ] 0 :=
begin
  let s := dense_seq (dual 𝕜' γ),
  have hs : dense_range s := dense_range_dense_seq _,
  have hfs : ∀ n : ℕ, ∀ᵐ x ∂μ, ⟪f x, s n⟫ = (0 : 𝕜'), from λ n, hf (s n),
  have hf' : ∀ᵐ x ∂μ, ∀ n : ℕ, ⟪f x, s n⟫ = (0 : 𝕜'), by rwa ae_all_iff,
  refine hf'.mono (λ x hx, eq_zero_of_forall_dual_eq_zero 𝕜' (λ c, _)),
  have h_closed : is_closed {c : dual 𝕜' γ | ⟪f x, c⟫ = (0 : 𝕜')},
  { refine is_closed_eq _ continuous_const,
    have h_fun_eq : (λ (c : dual 𝕜' γ), ⟪f x, c⟫) = inclusion_in_double_dual' 𝕜' γ (f x),
      by { ext1 c, rw ← dual_def 𝕜' γ (f x) c, },
    rw h_fun_eq,
    continuity, },
  exact @is_closed_property ℕ (dual 𝕜' γ) _ s (λ c, ⟪f x, c⟫ = (0 : 𝕜')) hs h_closed (λ n, hx n) c,
end

end tools

local notation `⟪`x`, `y`⟫` := @inner 𝕜 E _ x y
local notation `⟪`x`, `y`⟫'` := @inner 𝕜 E' _ x y

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

section strongly_measurable

variables {m m0 : measurable_space α} {μ : measure α}

lemma Lp_meas.ae_fin_strongly_measurable' (hm : m ≤ m0) (f : Lp_meas F 𝕜 m p μ) (hp_ne_zero : p ≠ 0)
  (hp_ne_top : p ≠ ∞) :
  ∃ g, fin_strongly_measurable g (μ.trim hm) ∧ f =ᵐ[μ] g :=
⟨Lp_meas_to_Lp_trim F 𝕜 p μ hm f, Lp.fin_strongly_measurable _ hp_ne_zero hp_ne_top,
  (Lp_meas_to_Lp_trim_ae_eq hm f).symm⟩

end strongly_measurable

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

variables [borel_space 𝕜] {m m0 : measurable_space α} {μ : measure α}
  {s t : set α}

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

section real

section real_finite_measure

variables [finite_measure μ] {f : α → ℝ}

lemma ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure_of_measurable (hfm : measurable f)
  (hf : integrable f μ) (hf_zero : ∀ s, measurable_set s → 0 ≤ ∫ x in s, f x ∂μ) :
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

lemma ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure (hf : integrable f μ)
  (hf_zero : ∀ s, measurable_set s → 0 ≤ ∫ x in s, f x ∂μ) :
  0 ≤ᵐ[μ] f :=
begin
  rcases hf.1 with ⟨f', hf'_meas, hf_ae⟩,
  have hf'_integrable : integrable f' μ, from integrable.congr hf hf_ae,
  have hf'_zero : ∀ s, measurable_set s → 0 ≤ ∫ x in s, f' x ∂μ,
  { intros s hs,
    rw set_integral_congr_ae hs (hf_ae.mono (λ x hx hxs, hx.symm)),
    exact hf_zero s hs, },
  exact (ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure_of_measurable hf'_meas
    hf'_integrable hf'_zero).trans hf_ae.symm.le,
end

end real_finite_measure

lemma ae_nonneg_restrict_of_forall_set_integral_nonneg_inter {f : α → ℝ} {t : set α} (hμt : μ t ≠ ∞)
  (hf : integrable_on f t μ) (hf_zero : ∀ s, measurable_set s → 0 ≤ ∫ x in (s ∩ t), f x ∂μ) :
  0 ≤ᵐ[μ.restrict t] f :=
begin
  haveI : fact (μ t < ∞) := ⟨lt_top_iff_ne_top.mpr hμt⟩,
  refine ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure hf (λ s hs, _),
  simp_rw measure.restrict_restrict hs,
  exact hf_zero s hs,
end

lemma ae_nonneg_of_forall_set_integral_nonneg_of_sigma_finite [sigma_finite μ]
  {f : α → ℝ}
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s, measurable_set s → μ s < ∞ → 0 ≤ ∫ x in s, f x ∂μ) :
  0 ≤ᵐ[μ] f :=
begin
  let S := spanning_sets μ,
  rw [← @measure.restrict_univ _ _ μ, ← Union_spanning_sets μ, eventually_le, ae_iff,
    measure.restrict_apply'],
  swap,
  { exact measurable_set.Union (measurable_spanning_sets μ), },
  rw [set.inter_Union, measure_Union_null_iff],
  intro n,
  have h_meas_n : measurable_set (S n), from (measurable_spanning_sets μ n),
  have hμn : μ (S n) < ∞, from measure_spanning_sets_lt_top μ n,
  rw ← measure.restrict_apply' h_meas_n,
  refine ae_nonneg_restrict_of_forall_set_integral_nonneg_inter hμn.ne
    (hf_int_finite (S n) h_meas_n hμn) (λ s hs, _),
  exact hf_zero (s ∩ S n) (hs.inter h_meas_n)
    ((measure_mono (set.inter_subset_right _ _)).trans_lt hμn),
end

lemma integrable.ae_nonneg_of_forall_set_integral_nonneg_of_sigma_finite [sigma_finite μ]
  {f : α → ℝ}
  (hf : integrable f μ) (hf_zero : ∀ s, measurable_set s → μ s < ∞ → 0 ≤ ∫ x in s, f x ∂μ) :
  0 ≤ᵐ[μ] f :=
ae_nonneg_of_forall_set_integral_nonneg_of_sigma_finite (λ s hs hμs, hf.integrable_on) hf_zero

lemma ae_fin_strongly_measurable.ae_nonneg_of_forall_set_integral_nonneg {f : α → ℝ}
  (hf : ae_fin_strongly_measurable f μ)
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s, measurable_set s → μ s < ∞ → 0 ≤ ∫ x in s, f x ∂μ) :
  0 ≤ᵐ[μ] f :=
begin
  let t := hf.sigma_finite_set,
  suffices : 0 ≤ᵐ[μ.restrict t] f,
    from ae_of_ae_restrict_of_ae_restrict_compl hf.measurable_set this hf.ae_eq_zero_compl.symm.le,
  haveI : sigma_finite (μ.restrict t) := hf.sigma_finite_restrict,
  refine ae_nonneg_of_forall_set_integral_nonneg_of_sigma_finite (λ s hs hμts, _)
    (λ s hs hμts, _),
  { rw [integrable_on, measure.restrict_restrict hs],
    rw measure.restrict_apply hs at hμts,
    exact hf_int_finite (s ∩ t) (hs.inter hf.measurable_set) hμts, },
  { rw measure.restrict_restrict hs,
    rw measure.restrict_apply hs at hμts,
    exact hf_zero (s ∩ t) (hs.inter hf.measurable_set) hμts, },
end

lemma integrable.ae_nonneg_of_forall_set_integral_nonneg {f : α → ℝ} (hf : integrable f μ)
  (hf_zero : ∀ s, measurable_set s → μ s < ∞ → 0 ≤ ∫ x in s, f x ∂μ) :
  0 ≤ᵐ[μ] f :=
ae_fin_strongly_measurable.ae_nonneg_of_forall_set_integral_nonneg hf.ae_fin_strongly_measurable
  (λ s hs hμs, hf.integrable_on) hf_zero

lemma ae_nonneg_restrict_of_forall_set_integral_nonneg {f : α → ℝ}
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s, measurable_set s → μ s < ∞ → 0 ≤ ∫ x in s, f x ∂μ)
  {t : set α} (ht : measurable_set t) (hμt : μ t ≠ ∞) :
  0 ≤ᵐ[μ.restrict t] f :=
begin
  refine ae_nonneg_restrict_of_forall_set_integral_nonneg_inter hμt
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
    simpa using hx, },
  refine ae_nonneg_restrict_of_forall_set_integral_nonneg
    (λ s hs hμs, (hf_int_finite s hs hμs).neg) (λ s hs hμs, _) ht hμt,
  simp_rw pi.neg_apply,
  rw [integral_neg, neg_nonneg],
  exact (hf_zero s hs hμs).le,
end

end real

lemma ae_eq_zero_restrict_of_forall_set_integral_eq_zero_𝕜 {f : α → 𝕜}
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = 0)
  {t : set α} (ht : measurable_set t) (hμt : μ t ≠ ∞) :
  f =ᵐ[μ.restrict t] 0 :=
begin
  suffices h_re_im : (∀ᵐ x ∂(μ.restrict t), is_R_or_C.re (f x) = 0)
    ∧ ∀ᵐ x ∂(μ.restrict t), is_R_or_C.im (f x) = 0,
  { rw ← eventually_and at h_re_im,
    refine h_re_im.mono (λ x hx, _),
    rwa [is_R_or_C.ext_iff, pi.zero_apply, add_monoid_hom.map_zero, add_monoid_hom.map_zero], },
  have hf_re : ∀ s, measurable_set s → μ s < ∞ → integrable_on (λ x, is_R_or_C.re (f x)) s μ,
    from λ s hs hμs, (hf_int_finite s hs hμs).re,
  have hf_im : ∀ s, measurable_set s → μ s < ∞ → integrable_on (λ x, is_R_or_C.im (f x)) s μ,
    from λ s hs hμs, (hf_int_finite s hs hμs).im,
  have hf_zero_re : ∀ s, measurable_set s → μ s < ∞ → ∫ x in s, is_R_or_C.re (f x) ∂μ = 0,
  { intros s hs hμs,
    rw [integral_re (hf_int_finite s hs hμs), hf_zero s hs hμs, is_R_or_C.zero_re'], },
  have hf_zero_im : ∀ s, measurable_set s → μ s < ∞ → ∫ x in s, is_R_or_C.im (f x) ∂μ = 0,
  { intros s hs hμs,
    rw [integral_im (hf_int_finite s hs hμs), hf_zero s hs hμs],
    simp only [add_monoid_hom.map_zero], },
  exact ⟨ae_eq_zero_restrict_of_forall_set_integral_eq_zero_ℝ hf_re hf_zero_re ht hμt,
    ae_eq_zero_restrict_of_forall_set_integral_eq_zero_ℝ hf_im hf_zero_im ht hμt⟩,
end

lemma sigma_finite_restrict_union {α} {m : measurable_space α} {μ : measure α} {s t : set α}
  (hs : sigma_finite (μ.restrict s)) (ht : sigma_finite (μ.restrict t)) :
  sigma_finite (μ.restrict (s ∪ t)) :=
begin
  let S := spanning_sets (μ.restrict s),
  have hS_meas := λ n, measurable_spanning_sets (μ.restrict s) n,
  let T := spanning_sets (μ.restrict t),
  have hT_meas := λ n, measurable_spanning_sets (μ.restrict t) n,
  use (λ n, S n ∩ T n),
  { exact λ n, (hS_meas n).inter (hT_meas n), },
  { intros n,
    rw [measure.restrict_apply ((hS_meas n).inter (hT_meas n)), set.inter_union_distrib_left],
    refine (measure_union_le _ _).trans_lt (ennreal.add_lt_top.mpr ⟨_, _⟩),
    { have h_subset : S n ∩ T n ∩ s ⊆ S n ∩ s,
      { rw [set.inter_assoc, set.inter_comm, set.inter_assoc, set.inter_comm s],
        exact set.inter_subset_right _ _, },
      refine (measure_mono h_subset).trans_lt _,
      have h := measure_spanning_sets_lt_top (μ.restrict s) n,
      rwa measure.restrict_apply (hS_meas n) at h, },
    { have h_subset : S n ∩ T n ∩ t ⊆ T n ∩ t,
      { rw set.inter_assoc,
        exact set.inter_subset_right _ _, },
      refine (measure_mono h_subset).trans_lt _,
      have h := measure_spanning_sets_lt_top (μ.restrict t) n,
      rwa measure.restrict_apply (hT_meas n) at h, }, },
  { rw [set.Union_inter_of_monotone (monotone_spanning_sets (μ.restrict s))
      (monotone_spanning_sets (μ.restrict t)), Union_spanning_sets (μ.restrict s),
      Union_spanning_sets (μ.restrict t), set.univ_inter], },
end

lemma fin_strongly_measurable_iff_strongly_measurable_and_exists_set_sigma_finite {α β} {f : α → β}
  [topological_space β] [t2_space β] [has_zero β] {m : measurable_space α} {μ : measure α} :
  fin_strongly_measurable f μ ↔ (strongly_measurable f
    ∧ (∃ t, measurable_set t ∧ (∀ x ∈ tᶜ, f x = 0) ∧ sigma_finite (μ.restrict t))) :=
⟨λ hf, ⟨hf.strongly_measurable, hf.exists_set_sigma_finite⟩,
  λ hf, hf.1.fin_strongly_measurable_of_exists_set_sigma_finite hf.2⟩

lemma strongly_measurable.add {α β} [measurable_space α] [topological_space β] [has_add β]
  [has_continuous_add β] {f g : α → β}
  (hf : strongly_measurable f) (hg : strongly_measurable g) :
  strongly_measurable (f + g) :=
⟨λ n, hf.approx n + hg.approx n, λ x, (hf.tendsto_approx x).add (hg.tendsto_approx x)⟩

lemma strongly_measurable.neg {α β} [measurable_space α] [topological_space β] [add_group β]
  [topological_add_group β] {f : α → β} (hf : strongly_measurable f) :
  strongly_measurable (-f) :=
⟨λ n, - hf.approx n, λ x, (hf.tendsto_approx x).neg⟩

lemma strongly_measurable.sub {α β} [measurable_space α] [topological_space β] [has_sub β]
  [has_continuous_sub β] {f g : α → β}
  (hf : strongly_measurable f) (hg : strongly_measurable g) :
  strongly_measurable (f - g) :=
⟨λ n, hf.approx n - hg.approx n, λ x, (hf.tendsto_approx x).sub (hg.tendsto_approx x)⟩

lemma fin_strongly_measurable.add {α β} [topological_space β] [add_monoid β] [has_continuous_add β]
  {m : measurable_space α} {μ : measure α} {f g : α → β}
  (hf : fin_strongly_measurable f μ) (hg : fin_strongly_measurable g μ) :
  fin_strongly_measurable (f + g) μ :=
⟨λ n, hf.approx n + hg.approx n,
  λ n, (measure_mono (function.support_add _ _)).trans_lt ((measure_union_le _ _).trans_lt
    (ennreal.add_lt_top.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩)),
  λ x, (hf.tendsto_approx x).add (hg.tendsto_approx x)⟩

lemma fin_strongly_measurable.neg {α β} [topological_space β] [add_group β]
  [topological_add_group β] {m : measurable_space α} {μ : measure α} {f : α → β}
  (hf : fin_strongly_measurable f μ) :
  fin_strongly_measurable (-f) μ :=
begin
  refine ⟨λ n, -hf.approx n, λ n, _, λ x, (hf.tendsto_approx x).neg⟩,
  push_cast,
  suffices : μ (function.support (λ x, - (hf.approx n) x)) < ∞,
    by convert this,
  rw function.support_neg (hf.approx n),
  exact hf.fin_support_approx n,
end

lemma fin_strongly_measurable.sub {α β} [topological_space β] [add_group β] [has_continuous_sub β]
  {m : measurable_space α} {μ : measure α} {f g : α → β}
  (hf : fin_strongly_measurable f μ) (hg : fin_strongly_measurable g μ) :
  fin_strongly_measurable (f - g) μ :=
⟨λ n, hf.approx n - hg.approx n,
  λ n, (measure_mono (function.support_sub _ _)).trans_lt ((measure_union_le _ _).trans_lt
    (ennreal.add_lt_top.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩)),
  λ x, (hf.tendsto_approx x).sub (hg.tendsto_approx x)⟩

lemma ae_fin_strongly_measurable.add {α β} [topological_space β] [add_monoid β]
  [has_continuous_add β] {m : measurable_space α} {μ : measure α} {f g : α → β}
  (hf : ae_fin_strongly_measurable f μ) (hg : ae_fin_strongly_measurable g μ) :
  ae_fin_strongly_measurable (f + g) μ :=
⟨hf.some + hg.some, hf.some_spec.1.add hg.some_spec.1, hf.some_spec.2.add hg.some_spec.2⟩

lemma ae_fin_strongly_measurable.neg {α β} [topological_space β] [add_group β]
  [topological_add_group β] {m : measurable_space α} {μ : measure α} {f : α → β}
  (hf : ae_fin_strongly_measurable f μ) :
  ae_fin_strongly_measurable (-f) μ :=
⟨-hf.some, hf.some_spec.1.neg, hf.some_spec.2.neg⟩

lemma ae_fin_strongly_measurable.sub {α β} [topological_space β] [add_group β]
  [has_continuous_sub β] {m : measurable_space α} {μ : measure α} {f g : α → β}
  (hf : ae_fin_strongly_measurable f μ) (hg : ae_fin_strongly_measurable g μ) :
  ae_fin_strongly_measurable (f - g) μ :=
⟨hf.some - hg.some, hf.some_spec.1.sub hg.some_spec.1, hf.some_spec.2.sub hg.some_spec.2⟩

variables [is_scalar_tower ℝ 𝕜 E']
include 𝕜

lemma ae_eq_zero_restrict_of_forall_set_integral_eq_zero {f : α → E'}
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = 0)
  {t : set α} (ht : measurable_set t) (hμt : μ t ≠ ∞) :
  f =ᵐ[μ.restrict t] 0 :=
begin
  refine ae_eq_zero_of_forall_inner (λ c, _),
  refine ae_eq_zero_restrict_of_forall_set_integral_eq_zero_𝕜 _ _ ht hμt,
  { exact λ s hs hμs, (hf_int_finite s hs hμs).const_inner c, },
  { intros s hs hμs,
    rw integral_inner (hf_int_finite s hs hμs) c,
    simp [hf_zero s hs hμs], },
end

lemma ae_eq_restrict_of_forall_set_integral_eq {f g : α → E'}
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hg_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on g s μ)
  (hfg_zero : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ)
  {t : set α} (ht : measurable_set t) (hμt : μ t ≠ ∞) :
  f =ᵐ[μ.restrict t] g :=
begin
  rw ← sub_ae_eq_zero,
  have hfg' : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, (f - g) x ∂μ = 0,
  { intros s hs hμs,
    rw integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs),
    exact sub_eq_zero.mpr (hfg_zero s hs hμs), },
  have hfg_int : ∀ s, measurable_set s → μ s < ∞ → integrable_on (f-g) s μ,
    from λ s hs hμs, (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs),
  exact ae_eq_zero_restrict_of_forall_set_integral_eq_zero hfg_int hfg' ht hμt,
end

lemma ae_eq_zero_of_forall_set_integral_eq_of_sigma_finite [sigma_finite μ] {f : α → E'}
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = 0) :
  f =ᵐ[μ] 0 :=
begin
  let S := spanning_sets μ,
  rw [← @measure.restrict_univ _ _ μ, ← Union_spanning_sets μ, eventually_eq, ae_iff,
    measure.restrict_apply' (measurable_set.Union (measurable_spanning_sets μ))],
  rw [set.inter_Union, measure_Union_null_iff],
  intro n,
  have h_meas_n : measurable_set (S n), from (measurable_spanning_sets μ n),
  have hμn : μ (S n) < ∞, from measure_spanning_sets_lt_top μ n,
  rw ← measure.restrict_apply' h_meas_n,
  exact ae_eq_zero_restrict_of_forall_set_integral_eq_zero hf_int_finite hf_zero h_meas_n hμn.ne,
end

lemma ae_fin_strongly_measurable.ae_eq_zero_of_forall_set_integral_eq_zero {f : α → E'}
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = 0)
  (hf : ae_fin_strongly_measurable f μ) :
  f =ᵐ[μ] 0 :=
begin
  let t := hf.sigma_finite_set,
  suffices : f =ᵐ[μ.restrict t] 0,
    from ae_of_ae_restrict_of_ae_restrict_compl hf.measurable_set this hf.ae_eq_zero_compl,
  haveI : sigma_finite (μ.restrict t) := hf.sigma_finite_restrict,
  refine ae_eq_zero_of_forall_set_integral_eq_of_sigma_finite _ _,
  { intros s hs hμs,
    rw [integrable_on, measure.restrict_restrict hs],
    rw [measure.restrict_apply hs] at hμs,
    exact hf_int_finite _ (hs.inter hf.measurable_set) hμs, },
  { intros s hs hμs,
    rw [measure.restrict_restrict hs],
    rw [measure.restrict_apply hs] at hμs,
    exact hf_zero _ (hs.inter hf.measurable_set) hμs, },
end

lemma ae_fin_strongly_measurable.ae_eq_of_forall_set_integral_eq {f g : α → E'}
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hg_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on g s μ)
  (hfg_eq : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ)
  (hf : ae_fin_strongly_measurable f μ) (hg : ae_fin_strongly_measurable g μ) :
  f =ᵐ[μ] g :=
begin
  rw ← sub_ae_eq_zero,
  have hfg : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, (f - g) x ∂μ = 0,
  { intros s hs hμs,
    rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs),
      sub_eq_zero.mpr (hfg_eq s hs hμs)], },
  have hfg_int : ∀ s, measurable_set s → μ s < ∞ → integrable_on (f-g) s μ,
    from λ s hs hμs, (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs),
  exact (hf.sub hg).ae_eq_zero_of_forall_set_integral_eq_zero hfg_int hfg,
end

lemma Lp.ae_eq_zero_of_forall_set_integral_eq_zero
  (f : Lp E' p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = 0) :
  f =ᵐ[μ] 0 :=
ae_fin_strongly_measurable.ae_eq_zero_of_forall_set_integral_eq_zero hf_int_finite hf_zero
  (Lp.fin_strongly_measurable _ hp_ne_zero hp_ne_top).ae_fin_strongly_measurable

lemma Lp.ae_eq_of_forall_set_integral_eq (f g : Lp E' p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hg_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on g s μ)
  (hfg : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ) :
  f =ᵐ[μ] g :=
ae_fin_strongly_measurable.ae_eq_of_forall_set_integral_eq hf_int_finite hg_int_finite hfg
  (Lp.fin_strongly_measurable _ hp_ne_zero hp_ne_top).ae_fin_strongly_measurable
  (Lp.fin_strongly_measurable _ hp_ne_zero hp_ne_top).ae_fin_strongly_measurable

lemma ae_eq_zero_of_forall_set_integral_eq_of_fin_strongly_measurable_trim (hm : m ≤ m0)
  {f : α → E'} (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → integrable_on f s μ)
  (hf_zero : ∀ s : set α, measurable_set[m] s → μ s < ∞ → ∫ x in s, f x ∂μ = 0)
  (hf : fin_strongly_measurable f (μ.trim hm)) :
  f =ᵐ[μ] 0 :=
begin
  obtain ⟨t, ht_meas, htf_zero, htμ⟩ := hf.exists_set_sigma_finite,
  haveI : @sigma_finite _ m ((μ.restrict t).trim hm) := by rwa restrict_trim hm μ ht_meas at htμ,
  have htf_zero : f =ᵐ[μ.restrict tᶜ] 0,
  { rw [eventually_eq, ae_restrict_iff' (measurable_set.compl (hm _ ht_meas))],
    exact eventually_of_forall htf_zero, },
  have hf_meas_m : measurable[m] f, from hf.measurable,
  suffices : f =ᵐ[μ.restrict t] 0,
    from ae_of_ae_restrict_of_ae_restrict_compl (hm t ht_meas) this htf_zero,
  refine measure_eq_zero_of_trim_eq_zero hm _,
  refine ae_eq_zero_of_forall_set_integral_eq_of_sigma_finite _ _,
  { intros s hs hμs,
    rw [integrable_on, restrict_trim hm (μ.restrict t) hs, measure.restrict_restrict (hm s hs)],
    rw [← restrict_trim hm μ ht_meas, @measure.restrict_apply _ m _ _ _ hs,
      trim_measurable_set_eq hm (@measurable_set.inter _ m _ _ hs ht_meas)] at hμs,
    refine integrable.trim hm _ hf_meas_m,
    exact hf_int_finite _ (@measurable_set.inter _ m _ _ hs ht_meas) hμs, },
  { intros s hs hμs,
    rw [restrict_trim hm (μ.restrict t) hs, measure.restrict_restrict (hm s hs)],
    rw [← restrict_trim hm μ ht_meas, @measure.restrict_apply _ m _ _ _ hs,
      trim_measurable_set_eq hm (@measurable_set.inter _ m _ _ hs ht_meas)] at hμs,
    rw ← integral_trim hm hf_meas_m,
    exact hf_zero _ (@measurable_set.inter _ m _ _ hs ht_meas) hμs, },
end

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

/-- **Unicity of the conditional expectation**. -/
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

lemma ae_eq_of_forall_set_integral_eq_of_sigma_finite [sigma_finite μ] {f g : α → E'}
  (hf_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on f s μ)
  (hg_int_finite : ∀ s, measurable_set s → μ s < ∞ → integrable_on g s μ)
  (hfg_zero : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ) :
  f =ᵐ[μ] g :=
begin
  let S := spanning_sets μ,
  rw [← @measure.restrict_univ _ _ μ, ← Union_spanning_sets μ, eventually_eq, ae_iff,
    measure.restrict_apply'],
  swap,
  { refine measurable_set.Union _ ,
    exact measurable_spanning_sets μ, },
  rw [set.inter_Union, measure_Union_null_iff],
  intro n,
  have h_meas_n : measurable_set (S n), from measurable_spanning_sets μ n,
  have hμn : μ (S n) < ∞, from measure_spanning_sets_lt_top μ n,
  rw ← measure.restrict_apply' h_meas_n,
  exact ae_eq_restrict_of_forall_set_integral_eq hf_int_finite hg_int_finite hfg_zero h_meas_n
    hμn.ne,
end

lemma ae_eq_of_forall_set_integral_eq_of_sigma_finite' (hm : m ≤ m0) [@sigma_finite _ m (μ.trim hm)]
  {f g : α → E'}
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
    @integral _ _ m _ _ _ _ _ _ (@measure.restrict _ m (μ.trim hm) s) (hfm.mk f)
      = @integral _ _ m _ _ _ _ _ _ (@measure.restrict _ m (μ.trim hm) s) (hgm.mk g),
  { intros s hs hμs,
    rw trim_measurable_set_eq hm hs at hμs,
    rw [restrict_trim hm _ hs, ← integral_trim hm hfm.measurable_mk,
      ← integral_trim hm hgm.measurable_mk, integral_congr_ae (ae_restrict_of_ae hfm.ae_eq_mk.symm),
      integral_congr_ae (ae_restrict_of_ae hgm.ae_eq_mk.symm)],
    exact hfg_eq s hs hμs, },
  exact ae_eq_of_forall_set_integral_eq_of_sigma_finite hf_mk_int_finite hg_mk_int_finite hfg_mk_eq,
end

lemma integrable.ae_eq_zero_of_forall_set_integral_eq_zero {f : α → E'} (hf : integrable f μ)
  (hf_zero : ∀ s, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = 0) :
  f =ᵐ[μ] 0 :=
begin
  have hf_Lp : mem_ℒp f 1 μ, from mem_ℒp_one_iff_integrable.mpr hf,
  let f_Lp := hf_Lp.to_Lp f,
  have hf_f_Lp : f =ᵐ[μ] f_Lp, from (mem_ℒp.coe_fn_to_Lp hf_Lp).symm,
  refine hf_f_Lp.trans _,
  refine Lp.ae_eq_zero_of_forall_set_integral_eq_zero f_Lp one_ne_zero ennreal.coe_ne_top _ _,
  { exact λ s hs hμs, integrable.integrable_on (L1.integrable_coe_fn _), },
  { intros s hs hμs,
    rw integral_congr_ae (ae_restrict_of_ae hf_f_Lp.symm),
    exact hf_zero s hs hμs, },
end

lemma integrable.ae_eq_of_forall_set_integral_eq (f g : α → E')
  (hf : integrable f μ) (hg : integrable g μ)
  (hfg : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ) :
  f =ᵐ[μ] g :=
begin
  rw ← sub_ae_eq_zero,
  have hfg' : ∀ s : set α, measurable_set s → μ s < ∞ → ∫ x in s, (f - g) x ∂μ = 0,
  { intros s hs hμs,
    rw integral_sub' hf.integrable_on hg.integrable_on,
    exact sub_eq_zero.mpr (hfg s hs hμs), },
  exact integrable.ae_eq_zero_of_forall_set_integral_eq_zero (hf.sub hg) hfg',
end

omit 𝕜
end ae_eq_of_forall_set_integral_eq

/-! ## Conditional expectation in L2

We define a conditional expectation in `L2`: it is the orthogonal projection on the subspace
`Lp_meas`. -/

section condexp_L2

variables [complete_space E]

local notation `⟪`x`, `y`⟫₂` := @inner 𝕜 (α →₂[μ] E) _ x y

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

section real

lemma integral_condexp_L2_eq_of_fin_meas_real (hm : m ≤ m0) (f : Lp 𝕜 2 μ) {s : set α}
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
    rw ← integral_condexp_L2_eq_of_fin_meas_real hm f ht hμt.ne,
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

lemma condexp_const_inner (hm : m ≤ m0) (f : Lp E 2 μ) (c : E) :
  condexp_L2 𝕜 hm (((Lp.mem_ℒp f).const_inner c).to_Lp (λ a, ⟪c, f a⟫))
    =ᵐ[μ] λ a, ⟪c, condexp_L2 𝕜 hm f a⟫ :=
begin
  rw Lp_meas_coe,
  have h_mem_Lp : mem_ℒp (λ a, ⟪c, condexp_L2 𝕜 hm f a⟫) 2 μ,
  { refine mem_ℒp.const_inner _ _,
    rw Lp_meas_coe,
    exact Lp.mem_ℒp _, },
  let inner_condexp_Lp := h_mem_Lp.to_Lp _,
  have h_eq : inner_condexp_Lp =ᵐ[μ] λ a, ⟪c, condexp_L2 𝕜 hm f a⟫,
    from h_mem_Lp.coe_fn_to_Lp,
  refine eventually_eq.trans _ h_eq,
  refine Lp.ae_eq_of_forall_set_integral_eq' hm _ _ _ ennreal.coe_ne_top _ _ _ _ _,
  { simp only [ennreal.bit0_eq_zero_iff, ne.def, not_false_iff, one_ne_zero], },
  { exact λ s hs hμs, integrable_on_condexp_L2_of_measure_ne_top hm hμs.ne _, },
  { intros s hs hμs,
    rw [integrable_on, integrable_congr (ae_restrict_of_ae h_eq)],
    exact (integrable_on_condexp_L2_of_measure_ne_top hm hμs.ne _).const_inner _, },
  { intros s hs hμs,
    simp_rw ← Lp_meas_coe,
    rw integral_condexp_L2_eq_of_fin_meas_real hm _ hs hμs.ne,
    rw integral_congr_ae (ae_restrict_of_ae h_eq),
    simp_rw Lp_meas_coe,
    rw [← L2.inner_indicator_const_Lp_eq_set_integral_inner ↑(condexp_L2 𝕜 hm f) (hm s hs) c hμs.ne,
      ← inner_condexp_L2_left_eq_right, condexp_L2_indicator_of_measurable,
      L2.inner_indicator_const_Lp_eq_set_integral_inner f (hm s hs) c hμs.ne,
      set_integral_congr_ae (hm s hs)
        ((mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).const_inner c)).mono (λ x hx hxs, hx))], },
  { rw ← Lp_meas_coe,
    exact Lp_meas.ae_measurable' _, },
  { refine ae_measurable'.congr _ h_eq.symm,
    exact (Lp_meas.ae_measurable' _).const_inner _, },
end

lemma integral_condexp_L2_eq_of_fin_meas [is_scalar_tower ℝ 𝕜 E'] (hm : m ≤ m0)
  (f : Lp E' 2 μ) {s : set α} (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) :
  ∫ x in s, condexp_L2 𝕜 hm f x ∂μ = ∫ x in s, f x ∂μ :=
begin
  rw [← sub_eq_zero, ← integral_sub'],
  swap, { exact integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs, },
  swap, { exact integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs, },
  refine integral_eq_zero_of_forall_integral_inner_eq_zero _ _ _,
  { rw [Lp_meas_coe,
      integrable_congr (ae_restrict_of_ae (Lp.coe_fn_sub ↑(condexp_L2 𝕜 hm f) f).symm)],
    exact integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs, },
  intro c,
  simp_rw [pi.sub_apply, inner_sub_right],
  rw integral_sub,
  swap,
  { refine integrable.const_inner c _,
    exact integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs, },
  swap,
  { refine integrable.const_inner c _,
    exact integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs, },
  have h_ae_eq_f := mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).const_inner c),
  rw [sub_eq_zero,
    ← set_integral_congr_ae (hm s hs) ((condexp_const_inner hm f c).mono (λ x hx _, hx)),
    ← set_integral_congr_ae (hm s hs) (h_ae_eq_f.mono (λ x hx _, hx))],
  exact integral_condexp_L2_eq_of_fin_meas_real hm _ hs hμs,
end

end condexp_L2

end measure_theory
