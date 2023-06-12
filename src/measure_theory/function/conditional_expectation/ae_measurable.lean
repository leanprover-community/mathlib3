/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import measure_theory.function.l2_space
import measure_theory.function.strongly_measurable.lp

/-! # Functions a.e. measurable with respect to a sub-σ-algebra

A function `f` verifies `ae_strongly_measurable' m f μ` if it is `μ`-a.e. equal to
an `m`-strongly measurable function. This is similar to `ae_strongly_measurable`, but the
`measurable_space` structures used for the measurability statement and for the measure are
different.

We define `Lp_meas F 𝕜 m p μ`, the subspace of `Lp F p μ` containing functions `f` verifying
`ae_strongly_measurable' m f μ`, i.e. functions which are `μ`-a.e. equal to an `m`-strongly
measurable function.

## Main statements

We define an `isometry_equiv` between `Lp_meas_subgroup` and the `Lp` space corresponding to the
measure `μ.trim hm`. As a consequence, the completeness of `Lp` implies completeness of `Lp_meas`.

`Lp.induction_strongly_measurable` (see also `mem_ℒp.induction_strongly_measurable`):
To prove something for an `Lp` function a.e. strongly measurable with respect to a
sub-σ-algebra `m` in a normed space, it suffices to show that
* the property holds for (multiples of) characteristic functions which are measurable w.r.t. `m`;
* is closed under addition;
* the set of functions in `Lp` strongly measurable w.r.t. `m` for which the property holds is
  closed.

-/

open topological_space filter
open_locale ennreal measure_theory

namespace measure_theory

/-- A function `f` verifies `ae_strongly_measurable' m f μ` if it is `μ`-a.e. equal to
an `m`-strongly measurable function. This is similar to `ae_strongly_measurable`, but the
`measurable_space` structures used for the measurability statement and for the measure are
different. -/
def ae_strongly_measurable' {α β} [topological_space β]
  (m : measurable_space α) {m0 : measurable_space α}
  (f : α → β) (μ : measure α) : Prop :=
∃ g : α → β, strongly_measurable[m] g ∧ f =ᵐ[μ] g

namespace ae_strongly_measurable'

variables {α β 𝕜 : Type*} {m m0 : measurable_space α} {μ : measure α}
  [topological_space β] {f g : α → β}

lemma congr (hf : ae_strongly_measurable' m f μ) (hfg : f =ᵐ[μ] g) :
  ae_strongly_measurable' m g μ :=
by { obtain ⟨f', hf'_meas, hff'⟩ := hf, exact ⟨f', hf'_meas, hfg.symm.trans hff'⟩, }

lemma add [has_add β] [has_continuous_add β] (hf : ae_strongly_measurable' m f μ)
  (hg : ae_strongly_measurable' m g μ) :
  ae_strongly_measurable' m (f+g) μ :=
begin
  rcases hf with ⟨f', h_f'_meas, hff'⟩,
  rcases hg with ⟨g', h_g'_meas, hgg'⟩,
  exact ⟨f' + g', h_f'_meas.add h_g'_meas, hff'.add hgg'⟩,
end

lemma neg [add_group β] [topological_add_group β]
  {f : α → β} (hfm : ae_strongly_measurable' m f μ) :
  ae_strongly_measurable' m (-f) μ :=
begin
  rcases hfm with ⟨f', hf'_meas, hf_ae⟩,
  refine ⟨-f', hf'_meas.neg, hf_ae.mono (λ x hx, _)⟩,
  simp_rw pi.neg_apply,
  rw hx,
end

lemma sub [add_group β] [topological_add_group β] {f g : α → β}
  (hfm : ae_strongly_measurable' m f μ) (hgm : ae_strongly_measurable' m g μ) :
  ae_strongly_measurable' m (f - g) μ :=
begin
  rcases hfm with ⟨f', hf'_meas, hf_ae⟩,
  rcases hgm with ⟨g', hg'_meas, hg_ae⟩,
  refine ⟨f'-g', hf'_meas.sub hg'_meas, hf_ae.mp (hg_ae.mono (λ x hx1 hx2, _))⟩,
  simp_rw pi.sub_apply,
  rw [hx1, hx2],
end

lemma const_smul [has_smul 𝕜 β] [has_continuous_const_smul 𝕜 β]
  (c : 𝕜) (hf : ae_strongly_measurable' m f μ) :
  ae_strongly_measurable' m (c • f) μ :=
begin
  rcases hf with ⟨f', h_f'_meas, hff'⟩,
  refine ⟨c • f', h_f'_meas.const_smul c, _⟩,
  exact eventually_eq.fun_comp hff' (λ x, c • x),
end

lemma const_inner {𝕜 β} [is_R_or_C 𝕜] [normed_add_comm_group β] [inner_product_space 𝕜 β]
  {f : α → β} (hfm : ae_strongly_measurable' m f μ) (c : β) :
  ae_strongly_measurable' m (λ x, (inner c (f x) : 𝕜)) μ :=
begin
  rcases hfm with ⟨f', hf'_meas, hf_ae⟩,
  refine ⟨λ x, (inner c (f' x) : 𝕜), (@strongly_measurable_const _ _ m _ _).inner hf'_meas,
    hf_ae.mono (λ x hx, _)⟩,
  dsimp only,
  rw hx,
end

/-- An `m`-strongly measurable function almost everywhere equal to `f`. -/
noncomputable
def mk (f : α → β) (hfm : ae_strongly_measurable' m f μ) : α → β := hfm.some

lemma strongly_measurable_mk {f : α → β} (hfm : ae_strongly_measurable' m f μ) :
  strongly_measurable[m] (hfm.mk f) :=
hfm.some_spec.1

lemma ae_eq_mk {f : α → β} (hfm : ae_strongly_measurable' m f μ) : f =ᵐ[μ] hfm.mk f :=
hfm.some_spec.2

lemma continuous_comp {γ} [topological_space γ] {f : α → β} {g : β → γ}
  (hg : continuous g) (hf : ae_strongly_measurable' m f μ) :
  ae_strongly_measurable' m (g ∘ f) μ :=
⟨λ x, g (hf.mk _ x),
  @continuous.comp_strongly_measurable _ _ _ m _ _ _ _ hg hf.strongly_measurable_mk,
  hf.ae_eq_mk.mono (λ x hx, by rw [function.comp_apply, hx])⟩

end ae_strongly_measurable'

lemma ae_strongly_measurable'_of_ae_strongly_measurable'_trim {α β} {m m0 m0' : measurable_space α}
  [topological_space β] (hm0 : m0 ≤ m0') {μ : measure α} {f : α → β}
  (hf : ae_strongly_measurable' m f (μ.trim hm0)) :
  ae_strongly_measurable' m f μ :=
by { obtain ⟨g, hg_meas, hfg⟩ := hf, exact ⟨g, hg_meas, ae_eq_of_ae_eq_trim hfg⟩, }

lemma strongly_measurable.ae_strongly_measurable'
  {α β} {m m0 : measurable_space α} [topological_space β]
  {μ : measure α} {f : α → β} (hf : strongly_measurable[m] f) :
  ae_strongly_measurable' m f μ :=
⟨f, hf, ae_eq_refl _⟩

lemma ae_eq_trim_iff_of_ae_strongly_measurable' {α β} [topological_space β] [metrizable_space β]
  {m m0 : measurable_space α} {μ : measure α} {f g : α → β}
  (hm : m ≤ m0) (hfm : ae_strongly_measurable' m f μ) (hgm : ae_strongly_measurable' m g μ) :
  hfm.mk f =ᵐ[μ.trim hm] hgm.mk g ↔ f =ᵐ[μ] g :=
(ae_eq_trim_iff hm hfm.strongly_measurable_mk hgm.strongly_measurable_mk).trans
⟨λ h, hfm.ae_eq_mk.trans (h.trans hgm.ae_eq_mk.symm),
  λ h, hfm.ae_eq_mk.symm.trans (h.trans hgm.ae_eq_mk)⟩

lemma ae_strongly_measurable.comp_ae_measurable'
  {α β γ : Type*} [topological_space β] {mα : measurable_space α} {mγ : measurable_space γ}
  {f : α → β} {μ : measure γ} {g : γ → α}
  (hf : ae_strongly_measurable f (μ.map g)) (hg : ae_measurable g μ) :
  ae_strongly_measurable' (mα.comap g) (f ∘ g) μ :=
⟨(hf.mk f) ∘ g, hf.strongly_measurable_mk.comp_measurable (measurable_iff_comap_le.mpr le_rfl),
  ae_eq_comp hg hf.ae_eq_mk⟩

/-- If the restriction to a set `s` of a σ-algebra `m` is included in the restriction to `s` of
another σ-algebra `m₂` (hypothesis `hs`), the set `s` is `m` measurable and a function `f` almost
everywhere supported on `s` is `m`-ae-strongly-measurable, then `f` is also
`m₂`-ae-strongly-measurable. -/
lemma ae_strongly_measurable'.ae_strongly_measurable'_of_measurable_space_le_on
  {α E} {m m₂ m0 : measurable_space α} {μ : measure α}
  [topological_space E] [has_zero E] (hm : m ≤ m0) {s : set α} {f : α → E}
  (hs_m : measurable_set[m] s) (hs : ∀ t, measurable_set[m] (s ∩ t) → measurable_set[m₂] (s ∩ t))
  (hf : ae_strongly_measurable' m f μ) (hf_zero : f =ᵐ[μ.restrict sᶜ] 0) :
  ae_strongly_measurable' m₂ f μ :=
begin
  let f' := hf.mk f,
  have h_ind_eq : s.indicator (hf.mk f) =ᵐ[μ] f,
  { refine filter.eventually_eq.trans _
      (indicator_ae_eq_of_restrict_compl_ae_eq_zero (hm _ hs_m) hf_zero),
    filter_upwards [hf.ae_eq_mk] with x hx,
    by_cases hxs : x ∈ s,
    { simp [hxs, hx], },
    { simp [hxs], }, },
  suffices : strongly_measurable[m₂] (s.indicator (hf.mk f)),
    from ae_strongly_measurable'.congr this.ae_strongly_measurable' h_ind_eq,
  have hf_ind : strongly_measurable[m] (s.indicator (hf.mk f)),
    from hf.strongly_measurable_mk.indicator hs_m,
  exact hf_ind.strongly_measurable_of_measurable_space_le_on hs_m hs
    (λ x hxs, set.indicator_of_not_mem hxs _),
end

variables {α E' F F' 𝕜 : Type*} {p : ℝ≥0∞}
  [is_R_or_C 𝕜] -- 𝕜 for ℝ or ℂ
  -- E' for an inner product space on which we compute integrals
  [normed_add_comm_group E'] [inner_product_space 𝕜 E']
  [complete_space E'] [normed_space ℝ E']
  -- F for a Lp submodule
  [normed_add_comm_group F] [normed_space 𝕜 F]
  -- F' for integrals on a Lp submodule
  [normed_add_comm_group F'] [normed_space 𝕜 F'] [normed_space ℝ F'] [complete_space F']

section Lp_meas

/-! ## The subset `Lp_meas` of `Lp` functions a.e. measurable with respect to a sub-sigma-algebra -/

variables (F)

/-- `Lp_meas_subgroup F m p μ` is the subspace of `Lp F p μ` containing functions `f` verifying
`ae_strongly_measurable' m f μ`, i.e. functions which are `μ`-a.e. equal to
an `m`-strongly measurable function. -/
def Lp_meas_subgroup (m : measurable_space α) [measurable_space α] (p : ℝ≥0∞) (μ : measure α) :
  add_subgroup (Lp F p μ) :=
{ carrier   := {f : (Lp F p μ) | ae_strongly_measurable' m f μ} ,
  zero_mem' := ⟨(0 : α → F), @strongly_measurable_zero _ _ m _ _, Lp.coe_fn_zero _ _ _⟩,
  add_mem'  := λ f g hf hg, (hf.add hg).congr (Lp.coe_fn_add f g).symm,
  neg_mem' := λ f hf, ae_strongly_measurable'.congr hf.neg (Lp.coe_fn_neg f).symm, }

variables (𝕜)
/-- `Lp_meas F 𝕜 m p μ` is the subspace of `Lp F p μ` containing functions `f` verifying
`ae_strongly_measurable' m f μ`, i.e. functions which are `μ`-a.e. equal to
an `m`-strongly measurable function. -/
def Lp_meas (m : measurable_space α) [measurable_space α] (p : ℝ≥0∞)
  (μ : measure α) :
  submodule 𝕜 (Lp F p μ) :=
{ carrier   := {f : (Lp F p μ) | ae_strongly_measurable' m f μ} ,
  zero_mem' := ⟨(0 : α → F), @strongly_measurable_zero _ _ m _ _, Lp.coe_fn_zero _ _ _⟩,
  add_mem'  := λ f g hf hg, (hf.add hg).congr (Lp.coe_fn_add f g).symm,
  smul_mem' := λ c f hf, (hf.const_smul c).congr (Lp.coe_fn_smul c f).symm, }
variables {F 𝕜}

variables

lemma mem_Lp_meas_subgroup_iff_ae_strongly_measurable' {m m0 : measurable_space α} {μ : measure α}
  {f : Lp F p μ} :
  f ∈ Lp_meas_subgroup F m p μ ↔ ae_strongly_measurable' m f μ :=
by rw [← add_subgroup.mem_carrier, Lp_meas_subgroup, set.mem_set_of_eq]

lemma mem_Lp_meas_iff_ae_strongly_measurable'
  {m m0 : measurable_space α} {μ : measure α} {f : Lp F p μ} :
  f ∈ Lp_meas F 𝕜 m p μ ↔ ae_strongly_measurable' m f μ :=
by rw [← set_like.mem_coe, ← submodule.mem_carrier, Lp_meas, set.mem_set_of_eq]

lemma Lp_meas.ae_strongly_measurable'
  {m m0 : measurable_space α} {μ : measure α} (f : Lp_meas F 𝕜 m p μ) :
  ae_strongly_measurable' m f μ :=
mem_Lp_meas_iff_ae_strongly_measurable'.mp f.mem

lemma mem_Lp_meas_self
  {m0 : measurable_space α} (μ : measure α) (f : Lp F p μ) :
  f ∈ Lp_meas F 𝕜 m0 p μ :=
mem_Lp_meas_iff_ae_strongly_measurable'.mpr (Lp.ae_strongly_measurable f)

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
⟨s.indicator (λ x : α, c), (@strongly_measurable_const _ _ m _ _).indicator hs,
  indicator_const_Lp_coe_fn⟩

section complete_subspace

/-! ## The subspace `Lp_meas` is complete.

We define an `isometry_equiv` between `Lp_meas_subgroup` and the `Lp` space corresponding to the
measure `μ.trim hm`. As a consequence, the completeness of `Lp` implies completeness of
`Lp_meas_subgroup` (and `Lp_meas`). -/

variables {ι : Type*} {m m0 : measurable_space α} {μ : measure α}

/-- If `f` belongs to `Lp_meas_subgroup F m p μ`, then the measurable function it is almost
everywhere equal to (given by `ae_measurable.mk`) belongs to `ℒp` for the measure `μ.trim hm`. -/
lemma mem_ℒp_trim_of_mem_Lp_meas_subgroup (hm : m ≤ m0) (f : Lp F p μ)
  (hf_meas : f ∈ Lp_meas_subgroup F m p μ) :
  mem_ℒp (mem_Lp_meas_subgroup_iff_ae_strongly_measurable'.mp hf_meas).some p (μ.trim hm) :=
begin
  have hf : ae_strongly_measurable' m f μ,
    from (mem_Lp_meas_subgroup_iff_ae_strongly_measurable'.mp hf_meas),
  let g := hf.some,
  obtain ⟨hg, hfg⟩ := hf.some_spec,
  change mem_ℒp g p (μ.trim hm),
  refine ⟨hg.ae_strongly_measurable, _⟩,
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
  rw mem_Lp_meas_subgroup_iff_ae_strongly_measurable',
  refine ae_strongly_measurable'.congr _ (mem_ℒp.coe_fn_to_Lp hf_mem_ℒp).symm,
  refine ae_strongly_measurable'_of_ae_strongly_measurable'_trim hm _,
  exact Lp.ae_strongly_measurable f,
end

variables (F p μ)
/-- Map from `Lp_meas_subgroup` to `Lp F p (μ.trim hm)`. -/
noncomputable
def Lp_meas_subgroup_to_Lp_trim (hm : m ≤ m0) (f : Lp_meas_subgroup F m p μ) : Lp F p (μ.trim hm) :=
mem_ℒp.to_Lp (mem_Lp_meas_subgroup_iff_ae_strongly_measurable'.mp f.mem).some
  (mem_ℒp_trim_of_mem_Lp_meas_subgroup hm f f.mem)

variables (𝕜)
/-- Map from `Lp_meas` to `Lp F p (μ.trim hm)`. -/
noncomputable
def Lp_meas_to_Lp_trim (hm : m ≤ m0) (f : Lp_meas F 𝕜 m p μ) : Lp F p (μ.trim hm) :=
mem_ℒp.to_Lp (mem_Lp_meas_iff_ae_strongly_measurable'.mp f.mem).some
  (mem_ℒp_trim_of_mem_Lp_meas_subgroup hm f f.mem)
variables {𝕜}

/-- Map from `Lp F p (μ.trim hm)` to `Lp_meas_subgroup`, inverse of
`Lp_meas_subgroup_to_Lp_trim`. -/
noncomputable
def Lp_trim_to_Lp_meas_subgroup (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) : Lp_meas_subgroup F m p μ :=
⟨(mem_ℒp_of_mem_ℒp_trim hm (Lp.mem_ℒp f)).to_Lp f, mem_Lp_meas_subgroup_to_Lp_of_trim hm f⟩

variables (𝕜)
/-- Map from `Lp F p (μ.trim hm)` to `Lp_meas`, inverse of `Lp_meas_to_Lp_trim`. -/
noncomputable
def Lp_trim_to_Lp_meas (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) : Lp_meas F 𝕜 m p μ :=
⟨(mem_ℒp_of_mem_ℒp_trim hm (Lp.mem_ℒp f)).to_Lp f, mem_Lp_meas_subgroup_to_Lp_of_trim hm f⟩

variables {F 𝕜 p μ}

lemma Lp_meas_subgroup_to_Lp_trim_ae_eq (hm : m ≤ m0) (f : Lp_meas_subgroup F m p μ) :
  Lp_meas_subgroup_to_Lp_trim F p μ hm f =ᵐ[μ] f :=
(ae_eq_of_ae_eq_trim (mem_ℒp.coe_fn_to_Lp (mem_ℒp_trim_of_mem_Lp_meas_subgroup hm ↑f f.mem))).trans
  (mem_Lp_meas_subgroup_iff_ae_strongly_measurable'.mp f.mem).some_spec.2.symm

lemma Lp_trim_to_Lp_meas_subgroup_ae_eq (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) :
  Lp_trim_to_Lp_meas_subgroup F p μ hm f =ᵐ[μ] f :=
mem_ℒp.coe_fn_to_Lp _

lemma Lp_meas_to_Lp_trim_ae_eq (hm : m ≤ m0) (f : Lp_meas F 𝕜 m p μ) :
  Lp_meas_to_Lp_trim F 𝕜 p μ hm f =ᵐ[μ] f :=
(ae_eq_of_ae_eq_trim (mem_ℒp.coe_fn_to_Lp (mem_ℒp_trim_of_mem_Lp_meas_subgroup hm ↑f f.mem))).trans
  (mem_Lp_meas_subgroup_iff_ae_strongly_measurable'.mp f.mem).some_spec.2.symm

lemma Lp_trim_to_Lp_meas_ae_eq (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) :
  Lp_trim_to_Lp_meas F 𝕜 p μ hm f =ᵐ[μ] f :=
mem_ℒp.coe_fn_to_Lp _

/-- `Lp_trim_to_Lp_meas_subgroup` is a right inverse of `Lp_meas_subgroup_to_Lp_trim`. -/
lemma Lp_meas_subgroup_to_Lp_trim_right_inv (hm : m ≤ m0) :
  function.right_inverse (Lp_trim_to_Lp_meas_subgroup F p μ hm)
    (Lp_meas_subgroup_to_Lp_trim F p μ hm) :=
begin
  intro f,
  ext1,
  refine ae_eq_trim_of_strongly_measurable hm
    (Lp.strongly_measurable _) (Lp.strongly_measurable _) _,
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
  refine ae_eq_trim_of_strongly_measurable hm (Lp.strongly_measurable _) _ _,
  { exact (Lp.strongly_measurable _).add (Lp.strongly_measurable _), },
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
  refine ae_eq_trim_of_strongly_measurable hm (Lp.strongly_measurable _) _ _,
  { exact @strongly_measurable.neg _ _ _ m _ _ _ (Lp.strongly_measurable _), },
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

lemma Lp_meas_to_Lp_trim_smul (hm : m ≤ m0) (c : 𝕜) (f : Lp_meas F 𝕜 m p μ) :
  Lp_meas_to_Lp_trim F 𝕜 p μ hm (c • f) = c • Lp_meas_to_Lp_trim F 𝕜 p μ hm f :=
begin
  ext1,
  refine eventually_eq.trans _ (Lp.coe_fn_smul _ _).symm,
  refine ae_eq_trim_of_strongly_measurable hm (Lp.strongly_measurable _) _ _,
  { exact (Lp.strongly_measurable _).const_smul c, },
  refine (Lp_meas_to_Lp_trim_ae_eq hm _).trans _,
  refine (Lp.coe_fn_smul _ _).trans _,
  refine (Lp_meas_to_Lp_trim_ae_eq hm f).mono (λ x hx, _),
  rw [pi.smul_apply, pi.smul_apply, hx],
  refl,
end

/-- `Lp_meas_subgroup_to_Lp_trim` preserves the norm. -/
lemma Lp_meas_subgroup_to_Lp_trim_norm_map [hp : fact (1 ≤ p)] (hm : m ≤ m0)
  (f : Lp_meas_subgroup F m p μ) :
  ‖Lp_meas_subgroup_to_Lp_trim F p μ hm f‖ = ‖f‖ :=
begin
  rw [Lp.norm_def, snorm_trim hm (Lp.strongly_measurable _),
    snorm_congr_ae (Lp_meas_subgroup_to_Lp_trim_ae_eq hm _), Lp_meas_subgroup_coe, ← Lp.norm_def],
  congr,
end

lemma isometry_Lp_meas_subgroup_to_Lp_trim [hp : fact (1 ≤ p)] (hm : m ≤ m0) :
  isometry (Lp_meas_subgroup_to_Lp_trim F p μ hm) :=
isometry.of_dist_eq $ λ f g, by rw [dist_eq_norm, ← Lp_meas_subgroup_to_Lp_trim_sub,
  Lp_meas_subgroup_to_Lp_trim_norm_map, dist_eq_norm]

variables (F p μ)
/-- `Lp_meas_subgroup` and `Lp F p (μ.trim hm)` are isometric. -/
noncomputable
def Lp_meas_subgroup_to_Lp_trim_iso [hp : fact (1 ≤ p)] (hm : m ≤ m0) :
  Lp_meas_subgroup F m p μ ≃ᵢ Lp F p (μ.trim hm) :=
{ to_fun    := Lp_meas_subgroup_to_Lp_trim F p μ hm,
  inv_fun   := Lp_trim_to_Lp_meas_subgroup F p μ hm,
  left_inv  := Lp_meas_subgroup_to_Lp_trim_left_inv hm,
  right_inv := Lp_meas_subgroup_to_Lp_trim_right_inv hm,
  isometry_to_fun := isometry_Lp_meas_subgroup_to_Lp_trim hm, }

variables (𝕜)
/-- `Lp_meas_subgroup` and `Lp_meas` are isometric. -/
noncomputable
def Lp_meas_subgroup_to_Lp_meas_iso [hp : fact (1 ≤ p)] :
  Lp_meas_subgroup F m p μ ≃ᵢ Lp_meas F 𝕜 m p μ :=
isometry_equiv.refl (Lp_meas_subgroup F m p μ)

/-- `Lp_meas` and `Lp F p (μ.trim hm)` are isometric, with a linear equivalence. -/
noncomputable
def Lp_meas_to_Lp_trim_lie [hp : fact (1 ≤ p)] (hm : m ≤ m0) :
  Lp_meas F 𝕜 m p μ ≃ₗᵢ[𝕜] Lp F p (μ.trim hm) :=
{ to_fun    := Lp_meas_to_Lp_trim F 𝕜 p μ hm,
  inv_fun   := Lp_trim_to_Lp_meas F 𝕜 p μ hm,
  left_inv  := Lp_meas_subgroup_to_Lp_trim_left_inv hm,
  right_inv := Lp_meas_subgroup_to_Lp_trim_right_inv hm,
  map_add'  := Lp_meas_subgroup_to_Lp_trim_add hm,
  map_smul' := Lp_meas_to_Lp_trim_smul hm,
  norm_map' := Lp_meas_subgroup_to_Lp_trim_norm_map hm, }
variables {F 𝕜 p μ}

instance [hm : fact (m ≤ m0)] [complete_space F] [hp : fact (1 ≤ p)] :
  complete_space (Lp_meas_subgroup F m p μ) :=
by { rw (Lp_meas_subgroup_to_Lp_trim_iso F p μ hm.elim).complete_space_iff, apply_instance, }

-- For now just no-lint this; lean4's tree-based logging will make this easier to debug.
-- One possible change might be to generalize `𝕜` from `is_R_or_C` to `normed_field`, as this
-- result may well hold there.
@[nolint fails_quickly]
instance [hm : fact (m ≤ m0)] [complete_space F] [hp : fact (1 ≤ p)] :
  complete_space (Lp_meas F 𝕜 m p μ) :=
by { rw (Lp_meas_subgroup_to_Lp_meas_iso F 𝕜 p μ).symm.complete_space_iff, apply_instance, }

lemma is_complete_ae_strongly_measurable' [hp : fact (1 ≤ p)] [complete_space F] (hm : m ≤ m0) :
  is_complete {f : Lp F p μ | ae_strongly_measurable' m f μ} :=
begin
  rw ← complete_space_coe_iff_is_complete,
  haveI : fact (m ≤ m0) := ⟨hm⟩,
  change complete_space (Lp_meas_subgroup F m p μ),
  apply_instance,
end

lemma is_closed_ae_strongly_measurable' [hp : fact (1 ≤ p)] [complete_space F] (hm : m ≤ m0) :
  is_closed {f : Lp F p μ | ae_strongly_measurable' m f μ} :=
is_complete.is_closed (is_complete_ae_strongly_measurable' hm)

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

/-- When applying the inverse of `Lp_meas_to_Lp_trim_lie` (which takes a function in the Lp space of
the sub-sigma algebra and returns its version in the larger Lp space) to an indicator of the
sub-sigma-algebra, we obtain an indicator in the Lp space of the larger sigma-algebra. -/
lemma Lp_meas_to_Lp_trim_lie_symm_indicator [one_le_p : fact (1 ≤ p)] [normed_space ℝ F]
  {hm : m ≤ m0} {s : set α} {μ : measure α}
  (hs : measurable_set[m] s) (hμs : μ.trim hm s ≠ ∞) (c : F) :
  ((Lp_meas_to_Lp_trim_lie F ℝ p μ hm).symm
      (indicator_const_Lp p hs hμs c) : Lp F p μ)
    = indicator_const_Lp p (hm s hs) ((le_trim hm).trans_lt hμs.lt_top).ne c :=
begin
  ext1,
  rw ← Lp_meas_coe,
  change Lp_trim_to_Lp_meas F ℝ p μ hm (indicator_const_Lp p hs hμs c)
    =ᵐ[μ] (indicator_const_Lp p _ _ c : α → F),
  refine (Lp_trim_to_Lp_meas_ae_eq hm _).trans _,
  exact (ae_eq_of_ae_eq_trim indicator_const_Lp_coe_fn).trans indicator_const_Lp_coe_fn.symm,
end

lemma Lp_meas_to_Lp_trim_lie_symm_to_Lp [one_le_p : fact (1 ≤ p)] [normed_space ℝ F]
  (hm : m ≤ m0) (f : α → F) (hf : mem_ℒp f p (μ.trim hm)) :
  ((Lp_meas_to_Lp_trim_lie F ℝ p μ hm).symm (hf.to_Lp f) : Lp F p μ)
    = (mem_ℒp_of_mem_ℒp_trim hm hf).to_Lp f :=
begin
  ext1,
  rw ← Lp_meas_coe,
  refine (Lp_trim_to_Lp_meas_ae_eq hm _).trans _,
  exact (ae_eq_of_ae_eq_trim (mem_ℒp.coe_fn_to_Lp hf)).trans (mem_ℒp.coe_fn_to_Lp _).symm,
end

end strongly_measurable

end Lp_meas


section induction

variables {m m0 : measurable_space α} {μ : measure α} [fact (1 ≤ p)] [normed_space ℝ F]

/-- Auxiliary lemma for `Lp.induction_strongly_measurable`. -/
@[elab_as_eliminator]
lemma Lp.induction_strongly_measurable_aux (hm : m ≤ m0) (hp_ne_top : p ≠ ∞) (P : Lp F p μ → Prop)
  (h_ind : ∀ (c : F) {s : set α} (hs : measurable_set[m] s) (hμs : μ s < ∞),
      P (Lp.simple_func.indicator_const p (hm s hs) hμs.ne c))
  (h_add : ∀ ⦃f g⦄, ∀ hf : mem_ℒp f p μ, ∀ hg : mem_ℒp g p μ,
    ∀ hfm : ae_strongly_measurable' m f μ, ∀ hgm : ae_strongly_measurable' m g μ,
    disjoint (function.support f) (function.support g) →
    P (hf.to_Lp f) → P (hg.to_Lp g) → P ((hf.to_Lp f) + (hg.to_Lp g)))
  (h_closed : is_closed {f : Lp_meas F ℝ m p μ | P f}) :
  ∀ f : Lp F p μ, ae_strongly_measurable' m f μ → P f :=
begin
  intros f hf,
  let f' := (⟨f, hf⟩ : Lp_meas F ℝ m p μ),
  let g := Lp_meas_to_Lp_trim_lie F ℝ p μ hm f',
  have hfg : f' = (Lp_meas_to_Lp_trim_lie F ℝ p μ hm).symm g,
    by simp only [linear_isometry_equiv.symm_apply_apply],
  change P ↑f',
  rw hfg,
  refine @Lp.induction α F m _ p (μ.trim hm) _ hp_ne_top
    (λ g, P ((Lp_meas_to_Lp_trim_lie F ℝ p μ hm).symm g)) _ _ _ g,
  { intros b t ht hμt,
    rw [Lp.simple_func.coe_indicator_const,
      Lp_meas_to_Lp_trim_lie_symm_indicator ht hμt.ne b],
      have hμt' : μ t < ∞, from (le_trim hm).trans_lt hμt,
    specialize h_ind b ht hμt',
    rwa Lp.simple_func.coe_indicator_const at h_ind, },
  { intros f g hf hg h_disj hfP hgP,
    rw linear_isometry_equiv.map_add,
    push_cast,
    have h_eq : ∀ (f : α → F) (hf : mem_ℒp f p (μ.trim hm)),
      ((Lp_meas_to_Lp_trim_lie F ℝ p μ hm).symm (mem_ℒp.to_Lp f hf) : Lp F p μ)
        = (mem_ℒp_of_mem_ℒp_trim hm hf).to_Lp f,
      from Lp_meas_to_Lp_trim_lie_symm_to_Lp hm,
    rw h_eq f hf at hfP ⊢,
    rw h_eq g hg at hgP ⊢,
    exact h_add (mem_ℒp_of_mem_ℒp_trim hm hf) (mem_ℒp_of_mem_ℒp_trim hm hg)
      (ae_strongly_measurable'_of_ae_strongly_measurable'_trim hm hf.ae_strongly_measurable)
      (ae_strongly_measurable'_of_ae_strongly_measurable'_trim hm hg.ae_strongly_measurable)
      h_disj hfP hgP, },
  { change is_closed ((Lp_meas_to_Lp_trim_lie F ℝ p μ hm).symm ⁻¹' {g : Lp_meas F ℝ m p μ | P ↑g}),
    exact is_closed.preimage (linear_isometry_equiv.continuous _) h_closed, },
end

/-- To prove something for an `Lp` function a.e. strongly measurable with respect to a
sub-σ-algebra `m` in a normed space, it suffices to show that
* the property holds for (multiples of) characteristic functions which are measurable w.r.t. `m`;
* is closed under addition;
* the set of functions in `Lp` strongly measurable w.r.t. `m` for which the property holds is
  closed.
-/
@[elab_as_eliminator]
lemma Lp.induction_strongly_measurable (hm : m ≤ m0) (hp_ne_top : p ≠ ∞) (P : Lp F p μ → Prop)
  (h_ind : ∀ (c : F) {s : set α} (hs : measurable_set[m] s) (hμs : μ s < ∞),
      P (Lp.simple_func.indicator_const p (hm s hs) hμs.ne c))
  (h_add : ∀ ⦃f g⦄, ∀ hf : mem_ℒp f p μ, ∀ hg : mem_ℒp g p μ,
    ∀ hfm : strongly_measurable[m] f, ∀ hgm : strongly_measurable[m] g,
    disjoint (function.support f) (function.support g) →
    P (hf.to_Lp f) → P (hg.to_Lp g) → P ((hf.to_Lp f) + (hg.to_Lp g)))
  (h_closed : is_closed {f : Lp_meas F ℝ m p μ | P f}) :
  ∀ f : Lp F p μ, ae_strongly_measurable' m f μ → P f :=
begin
  intros f hf,
  suffices h_add_ae : ∀ ⦃f g⦄, ∀ hf : mem_ℒp f p μ, ∀ hg : mem_ℒp g p μ,
      ∀ hfm : ae_strongly_measurable' m f μ, ∀ hgm : ae_strongly_measurable' m g μ,
      disjoint (function.support f) (function.support g) →
      P (hf.to_Lp f) → P (hg.to_Lp g) → P ((hf.to_Lp f) + (hg.to_Lp g)),
    from Lp.induction_strongly_measurable_aux hm hp_ne_top P h_ind h_add_ae h_closed f hf,
  intros f g hf hg hfm hgm h_disj hPf hPg,
  let s_f : set α := function.support (hfm.mk f),
  have hs_f : measurable_set[m] s_f := hfm.strongly_measurable_mk.measurable_set_support,
  have hs_f_eq : s_f =ᵐ[μ] function.support f := hfm.ae_eq_mk.symm.support,
  let s_g : set α := function.support (hgm.mk g),
  have hs_g : measurable_set[m] s_g := hgm.strongly_measurable_mk.measurable_set_support,
  have hs_g_eq : s_g =ᵐ[μ] function.support g := hgm.ae_eq_mk.symm.support,
  have h_inter_empty : ((s_f ∩ s_g) : set α) =ᵐ[μ] (∅ : set α),
  { refine (hs_f_eq.inter hs_g_eq).trans _,
    suffices : function.support f ∩ function.support g = ∅, by rw this,
    exact set.disjoint_iff_inter_eq_empty.mp h_disj, },
  let f' := (s_f \ s_g).indicator (hfm.mk f),
  have hff' : f =ᵐ[μ] f',
  { have : s_f \ s_g =ᵐ[μ] s_f,
    { rw [← set.diff_inter_self_eq_diff, set.inter_comm],
      refine ((ae_eq_refl s_f).diff h_inter_empty).trans _,
      rw set.diff_empty, },
    refine ((indicator_ae_eq_of_ae_eq_set this).trans _).symm,
    rw set.indicator_support,
    exact hfm.ae_eq_mk.symm, },
  have hf'_meas : strongly_measurable[m] f',
    from hfm.strongly_measurable_mk.indicator (hs_f.diff hs_g),
  have hf'_Lp : mem_ℒp f' p μ := hf.ae_eq hff',
  let g' := (s_g \ s_f).indicator (hgm.mk g),
  have hgg' : g =ᵐ[μ] g',
  { have : s_g \ s_f =ᵐ[μ] s_g,
    { rw [← set.diff_inter_self_eq_diff],
      refine ((ae_eq_refl s_g).diff h_inter_empty).trans _,
      rw set.diff_empty, },
    refine ((indicator_ae_eq_of_ae_eq_set this).trans _).symm,
    rw set.indicator_support,
    exact hgm.ae_eq_mk.symm, },
  have hg'_meas : strongly_measurable[m] g',
    from hgm.strongly_measurable_mk.indicator (hs_g.diff hs_f),
  have hg'_Lp : mem_ℒp g' p μ := hg.ae_eq hgg',
  have h_disj : disjoint (function.support f') (function.support g'),
  { have : disjoint (s_f \ s_g) (s_g \ s_f) := disjoint_sdiff_sdiff,
    exact this.mono set.support_indicator_subset set.support_indicator_subset, },
  rw ← mem_ℒp.to_Lp_congr hf'_Lp hf hff'.symm at ⊢ hPf,
  rw ← mem_ℒp.to_Lp_congr hg'_Lp hg hgg'.symm at ⊢ hPg,
  exact h_add hf'_Lp hg'_Lp hf'_meas hg'_meas h_disj hPf hPg,
end

/-- To prove something for an arbitrary `mem_ℒp` function a.e. strongly measurable with respect
to a sub-σ-algebra `m` in a normed space, it suffices to show that
* the property holds for (multiples of) characteristic functions which are measurable w.r.t. `m`;
* is closed under addition;
* the set of functions in the `Lᵖ` space strongly measurable w.r.t. `m` for which the property
  holds is closed.
* the property is closed under the almost-everywhere equal relation.
-/
@[elab_as_eliminator]
lemma mem_ℒp.induction_strongly_measurable (hm : m ≤ m0) (hp_ne_top : p ≠ ∞)
  (P : (α → F) → Prop)
  (h_ind : ∀ (c : F) ⦃s⦄, measurable_set[m] s → μ s < ∞ → P (s.indicator (λ _, c)))
  (h_add : ∀ ⦃f g : α → F⦄, disjoint (function.support f) (function.support g)
    → mem_ℒp f p μ → mem_ℒp g p μ → strongly_measurable[m] f → strongly_measurable[m] g →
    P f → P g → P (f + g))
  (h_closed : is_closed {f : Lp_meas F ℝ m p μ | P f} )
  (h_ae : ∀ ⦃f g⦄, f =ᵐ[μ] g → mem_ℒp f p μ → P f → P g) :
  ∀ ⦃f : α → F⦄ (hf : mem_ℒp f p μ) (hfm : ae_strongly_measurable' m f μ), P f :=
begin
  intros f hf hfm,
  let f_Lp := hf.to_Lp f,
  have hfm_Lp : ae_strongly_measurable' m f_Lp μ, from hfm.congr hf.coe_fn_to_Lp.symm,
  refine h_ae (hf.coe_fn_to_Lp) (Lp.mem_ℒp _) _,
  change P f_Lp,
  refine Lp.induction_strongly_measurable hm hp_ne_top (λ f, P ⇑f) _ _ h_closed f_Lp hfm_Lp,
  { intros c s hs hμs,
    rw Lp.simple_func.coe_indicator_const,
    refine h_ae (indicator_const_Lp_coe_fn).symm _ (h_ind c hs hμs),
    exact mem_ℒp_indicator_const p (hm s hs) c (or.inr hμs.ne), },
  { intros f g hf_mem hg_mem hfm hgm h_disj hfP hgP,
    have hfP' : P f := h_ae (hf_mem.coe_fn_to_Lp) (Lp.mem_ℒp _) hfP,
    have hgP' : P g := h_ae (hg_mem.coe_fn_to_Lp) (Lp.mem_ℒp _) hgP,
    specialize h_add h_disj hf_mem hg_mem hfm hgm hfP' hgP',
    refine h_ae _ (hf_mem.add hg_mem) h_add,
    exact ((hf_mem.coe_fn_to_Lp).symm.add (hg_mem.coe_fn_to_Lp).symm).trans
      (Lp.coe_fn_add _ _).symm, },
end

end induction

end measure_theory
