/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import measure_theory.lp_space

/-! # Conditional expectation


-/

noncomputable theory
open topological_space measure_theory measure_theory.Lp filter
open_locale nnreal ennreal topological_space big_operators measure_theory

/-- Like `ae_measurable`, but the `measurable_space` structures used for the measurability
statement and for the measure are different.

TODO: change the definition of ae_measurable to use ae_measurable' ? -/
def ae_measurable' {α β} [measurable_space β] (m : measurable_space α) {m0 : measurable_space α}
  (f : α → β) (μ : measure α) :
  Prop :=
∃ g : α → β, @measurable α β m _ g ∧ f =ᵐ[μ] g

lemma measurable.ae_measurable' {α β} [measurable_space β] {m m0 : measurable_space α} {f : α → β}
  {μ : measure α} (hf : @measurable α β m _ f) :
  ae_measurable' m f μ :=
⟨f, hf, eventually_eq.rfl⟩

namespace ae_measurable'

variables {α β : Type*} [measurable_space β] {f : α → β}

lemma mono {m2 m m0 : measurable_space α} (hm : m2 ≤ m)
  {μ : measure α} (hf : ae_measurable' m2 f μ) :
  ae_measurable' m f μ :=
by { obtain ⟨g, hg_meas, hfg⟩ := hf, exact ⟨g, measurable.mono hg_meas hm le_rfl, hfg⟩, }

lemma ae_measurable {m m0 : measurable_space α} (hm : m ≤ m0)
  {μ : measure α} (hf : ae_measurable' m f μ) :
  ae_measurable f μ :=
ae_measurable'.mono hm hf

lemma ae_measurable'_of_ae_measurable'_trim {m m0 m0' : measurable_space α} (hm0 : m0 ≤ m0')
  {μ : measure α} (hf : ae_measurable' m f (μ.trim hm0)) :
  ae_measurable' m f μ :=
by { obtain ⟨g, hg_meas, hfg⟩ := hf, exact ⟨g, hg_meas, ae_eq_of_ae_eq_trim hfg⟩, }

lemma congr_ae {m m0 : measurable_space α} {μ : measure α}
  {f g : α → β} (hf : ae_measurable' m f μ) (hfg : f =ᵐ[μ] g) :
  ae_measurable' m g μ :=
by { obtain ⟨f', hf'_meas, hff'⟩ := hf, exact ⟨f', hf'_meas, hfg.symm.trans hff'⟩, }

lemma add [has_add β] [has_measurable_add₂ β] {m m0 : measurable_space α}
  {μ : measure α} {f g : α → β} (hf : ae_measurable' m f μ) (hg : ae_measurable' m g μ) :
  ae_measurable' m (f+g) μ :=
begin
  rcases hf with ⟨f', h_f'_meas, hff'⟩,
  rcases hg with ⟨g', h_g'_meas, hgg'⟩,
  refine ⟨f' + g', @measurable.add α m _ _ _ _ f' g' h_f'_meas h_g'_meas, _⟩,
  exact hff'.add hgg',
end

lemma sub [add_group β] [has_measurable_sub₂ β] {m m0 : measurable_space α}
  {μ : measure α} {f g : α → β} (hf : ae_measurable' m f μ) (hg : ae_measurable' m g μ) :
  ae_measurable' m (f - g) μ :=
begin
  rcases hf with ⟨f', h_f'_meas, hff'⟩,
  rcases hg with ⟨g', h_g'_meas, hgg'⟩,
  refine ⟨f' - g', @measurable.sub α m _ _ _ _ f' g' h_f'_meas h_g'_meas, _⟩,
  exact hff'.sub hgg',
end

lemma neg [has_neg β] [has_measurable_neg β] {m m0 : measurable_space α}
  {μ : measure α} {f : α → β} (hf : ae_measurable' m f μ) :
  ae_measurable' m (-f) μ :=
begin
  rcases hf with ⟨f', h_f'_meas, hff'⟩,
  exact ⟨-f', @measurable.neg α m _ _ _ _ f' h_f'_meas, hff'.neg⟩,
end

lemma smul₂ {δ} [has_scalar δ β] [measurable_space δ] [has_measurable_smul₂ δ β]
  {m m0 : measurable_space α} {μ : measure α}
  {f : α → δ} (hf : ae_measurable' m f μ) {g : α → β} (hg : ae_measurable' m g μ) :
  ae_measurable' m (λ x, f x • (g x)) μ :=
begin
  obtain ⟨f', hf_meas, hff'⟩ := hf,
  obtain ⟨g', hg_meas, hgg'⟩ := hg,
  refine ⟨λ x, (f' x) • (g' x), _, eventually_eq.comp₂ hff' (λ x y, x • y) hgg'⟩,
  exact @measurable.smul _ m _ _ _ _ _ _ _ _ hf_meas hg_meas,
end

lemma const_smul {δ} [has_scalar δ β] [measurable_space δ] [has_measurable_smul δ β]
  {m m0 : measurable_space α} {μ : measure α} (c : δ) {f : α → β} (hf : ae_measurable' m f μ) :
  ae_measurable' m (c • f) μ :=
begin
  rcases hf with ⟨f', h_f'_meas, hff'⟩,
  refine ⟨c • f', @measurable.const_smul α m _ _ _ _ _ _ f' h_f'_meas c, _⟩,
  exact eventually_eq.fun_comp hff' (λ x, c • x),
end

lemma restrict {m m0 : measurable_space α} {μ : measure α} (hf : ae_measurable' m f μ) (s : set α) :
  ae_measurable' m f (μ.restrict s) :=
by { obtain ⟨g, hg_meas, hfg⟩ := hf, exact ⟨g, hg_meas, ae_restrict_of_ae hfg⟩, }

lemma indicator [has_zero β] {m m0 : measurable_space α} {μ : measure α} (hf : ae_measurable' m f μ)
  {s : set α} (hs : @measurable_set α m s) :
  ae_measurable' m (s.indicator f) μ :=
begin
  rcases hf with ⟨f', h_f'_meas, hff'⟩,
  refine ⟨s.indicator f', @measurable.indicator α _ m _ _ s _ h_f'_meas hs, _⟩,
  refine hff'.mono (λ x hx, _),
  rw [set.indicator_apply, set.indicator_apply, hx],
end

lemma const {m m0 : measurable_space α} {μ : measure α} (c : β) : ae_measurable' m (λ x : α, c) μ :=
(@measurable_const _ _ _ m c).ae_measurable'

lemma smul_const {δ} [has_scalar δ β] [measurable_space δ] [has_measurable_smul₂ δ β]
  {m m0 : measurable_space α} {μ : measure α} {f : α → δ} (hf : ae_measurable' m f μ) (c : β) :
  ae_measurable' m (λ x, f x • c) μ :=
ae_measurable'.smul₂ hf (const c)

end ae_measurable'

namespace measure_theory

variables {α β γ E E' F F' G G' H 𝕜 𝕂 : Type*} {p : ℝ≥0∞}
  [is_R_or_C 𝕜] -- 𝕜 for ℝ or ℂ
  [is_R_or_C 𝕂] [measurable_space 𝕂] -- 𝕂 for ℝ or ℂ, together with a measurable_space
  [measurable_space β] -- β for a generic measurable space
  -- F for Lp submodule
  [normed_group F] [normed_space 𝕂 F] [measurable_space F] [borel_space F]
  [second_countable_topology F]
  -- F' for integrals on F
  [normed_group F'] [normed_space 𝕂 F'] [measurable_space F'] [borel_space F']
  [second_countable_topology F'] [normed_space ℝ F'] [complete_space F']
  -- G for Lp add_subgroup
  [normed_group G] [measurable_space G] [borel_space G] [second_countable_topology G]
  -- G' for integrals on G
  [normed_group G'] [measurable_space G'] [borel_space G'] [second_countable_topology G']
  [normed_space ℝ G'] [complete_space G']
  -- H for measurable space and normed group (hypotheses of mem_ℒp)
  [measurable_space H] [normed_group H]

section Lp_sub

variables (𝕂 F)
/-- Lp subspace of functions `f` verifying `ae_measurable' m f μ`. -/
def Lp_sub [opens_measurable_space 𝕂] (m : measurable_space α) [measurable_space α] (p : ℝ≥0∞)
  (μ : measure α) :
  submodule 𝕂 (Lp F p μ) :=
{ carrier   := {f : (Lp F p μ) | ae_measurable' m f μ} ,
  zero_mem' := ⟨(0 : α → F), @measurable_zero _ α _ m _, Lp.coe_fn_zero _ _ _⟩,
  add_mem'  := λ f g hf hg, (hf.add hg).congr_ae (Lp.coe_fn_add f g).symm,
  smul_mem' := λ c f hf, (hf.const_smul c).congr_ae (Lp.coe_fn_smul c f).symm, }
variables {𝕂 F}

variables [opens_measurable_space 𝕂]

lemma mem_Lp_sub_iff_ae_measurable' {m m0 : measurable_space α} {μ : measure α} {f : Lp F p μ} :
  f ∈ Lp_sub F 𝕂 m p μ ↔ ae_measurable' m f μ :=
by simp_rw [← set_like.mem_coe, ← submodule.mem_carrier, Lp_sub, set.mem_set_of_eq]

lemma Lp_sub.ae_measurable' {m m0 : measurable_space α} {μ : measure α} (f : Lp_sub F 𝕂 m p μ) :
  ae_measurable' m f μ :=
mem_Lp_sub_iff_ae_measurable'.mp f.mem

lemma mem_Lp_sub_self {m0 : measurable_space α} (μ : measure α) (f : Lp F p μ) :
  f ∈ Lp_sub F 𝕂 m0 p μ :=
mem_Lp_sub_iff_ae_measurable'.mpr (Lp.ae_measurable f)

lemma Lp_sub_coe {m m0 : measurable_space α} {p : ℝ≥0∞} {μ : measure α} {f : Lp_sub F 𝕂 m p μ} :
  ⇑f = (f : Lp F p μ) :=
coe_fn_coe_base f

section complete_subspace

variables {ι : Type*} {m m0 : measurable_space α} {μ : measure α}

lemma ae_measurable'_of_tendsto'_aux_mem_Lp (hm : m ≤ m0) (f : ι → Lp G p μ) (g : ι → α → G)
  (hfg : ∀ n, f n =ᵐ[μ] g n) (hg : ∀ n, @measurable α _ m _ (g n)) (n : ι) :
  @mem_ℒp α G m _ _ (g n) p (μ.trim hm) :=
begin
  refine ⟨@measurable.ae_measurable α _ m _ _ _ (hg n), _⟩,
  have h_snorm_fg : @snorm α _ m _ (g n) p (μ.trim hm) = snorm (f n) p μ,
    by { rw snorm_trim hm (hg n), exact snorm_congr_ae (hfg n).symm, },
  rw h_snorm_fg,
  exact Lp.snorm_lt_top (f n),
end

lemma ae_measurable'_of_tendsto'_aux_cauchy (hm : m ≤ m0) [nonempty ι] [semilattice_sup ι]
  [hp : fact (1 ≤ p)] (f : ι → Lp G p μ) (g : ι → α → G) (hfg : ∀ n, f n =ᵐ[μ] g n)
  (hg : ∀ n, @measurable α _ m _ (g n)) (h_cauchy_seq : cauchy_seq f) :
  cauchy_seq (λ n, @mem_ℒp.to_Lp α G m p _ _ _ _ _ (g n)
    (ae_measurable'_of_tendsto'_aux_mem_Lp hm f g hfg hg n)) :=
begin
  have mem_Lp_g : ∀ n, @mem_ℒp α G m _ _ (g n) p (μ.trim hm),
    from ae_measurable'_of_tendsto'_aux_mem_Lp hm f g hfg hg,
  let g_Lp := λ n, @mem_ℒp.to_Lp α G m p _ _ _ _ _ (g n) (mem_Lp_g n),
  have h_g_ae_m := λ n, @mem_ℒp.coe_fn_to_Lp α G m p _ _ _ _ _ _ (mem_Lp_g n),
  have h_cau_g : tendsto (λ (n : ι × ι), snorm (g n.fst - g n.snd) p μ) at_top (𝓝 0),
  { rw cauchy_seq_Lp_iff_cauchy_seq_ℒp at h_cauchy_seq,
    suffices h_snorm_eq : ∀ n : ι × ι, snorm (⇑(f n.fst) - ⇑(f n.snd)) p μ
        = snorm (g n.fst - g n.snd) p μ,
      by { simp_rw h_snorm_eq at h_cauchy_seq, exact h_cauchy_seq, },
    exact λ n, snorm_congr_ae ((hfg n.fst).sub (hfg n.snd)), },
  have h_cau_g_m : tendsto (λ (n : ι × ι), @snorm α _ m _ (g n.fst - g n.snd) p (μ.trim hm))
      at_top (𝓝 0),
    { suffices h_snorm_trim : ∀ n : ι × ι, @snorm α _ m _ (g n.fst - g n.snd) p (μ.trim hm)
        = snorm (g n.fst - g n.snd) p μ,
      { simp_rw h_snorm_trim, exact h_cau_g, },
      refine λ n, snorm_trim _ _,
      exact @measurable.sub α m _ _ _ _ (g n.fst) (g n.snd) (hg n.fst) (hg n.snd), },
  rw cauchy_seq_Lp_iff_cauchy_seq_ℒp,
  suffices h_eq : ∀ n : ι × ι, @snorm α _ m _ ((g_Lp n.fst) - (g_Lp n.snd)) p (μ.trim hm)
      = @snorm α _ m _ (g n.fst - g n.snd) p (μ.trim hm),
    by { simp_rw h_eq, exact h_cau_g_m, },
  exact λ n, @snorm_congr_ae α _ m _ _ _ _ _ ((h_g_ae_m n.fst).sub (h_g_ae_m n.snd)),
end

lemma ae_measurable'_of_tendsto' (hm : m ≤ m0) [nonempty ι] [semilattice_sup ι] [hp : fact (1 ≤ p)]
  [complete_space G] (f : ι → Lp G p μ) (g : ι → α → G) (f_lim : Lp G p μ)
  (hfg : ∀ n, f n =ᵐ[μ] g n) (hg : ∀ n, @measurable α _ m _ (g n))
  (h_tendsto : filter.at_top.tendsto f (𝓝 f_lim)) :
  ae_measurable' m f_lim μ :=
begin
  -- as sequence of functions of Lp, g is cauchy since f is.
  have mem_Lp_g : ∀ n, @mem_ℒp α G m _ _ (g n) p (μ.trim hm),
    from ae_measurable'_of_tendsto'_aux_mem_Lp hm f g hfg hg,
  let g_Lp := λ n, @mem_ℒp.to_Lp α G m p _ _ _ _ _ (g n) (mem_Lp_g n),
  have h_g_ae_m := λ n, @mem_ℒp.coe_fn_to_Lp α G m p _ _ _ _ _ _ (mem_Lp_g n),
  have h_cau_seq_g_Lp : cauchy_seq g_Lp,
    from ae_measurable'_of_tendsto'_aux_cauchy hm f g hfg hg h_tendsto.cauchy_seq,
  -- we now obtain a limit g_Lp_lim, which will be the measurable function used to prove
  -- `ae_measurable' m f_lim μ`
  obtain ⟨g_Lp_lim, g_tendsto⟩ := cauchy_seq_tendsto_of_complete h_cau_seq_g_Lp,
  have h_g_lim_meas_m : @measurable α _ m _ g_Lp_lim,
    from @Lp.measurable α G m p (μ.trim hm) _ _ _ _ g_Lp_lim,
  refine ⟨g_Lp_lim, h_g_lim_meas_m, _⟩,
  -- the measurability part of `ae_measurable'` is ensured. Now we prove `f_lim =ᵐ[μ] g_Lp_lim`
  have h_g_lim_meas : measurable g_Lp_lim, from h_g_lim_meas_m.mono hm le_rfl,
  rw tendsto_Lp_iff_tendsto_ℒp' at g_tendsto h_tendsto,
  suffices h_snorm_zero : snorm (⇑f_lim - ⇑g_Lp_lim) p μ = 0,
  { rw @snorm_eq_zero_iff α G m0 p μ _ _ _ _ _ (ennreal.zero_lt_one.trans_le hp.elim).ne.symm
      at h_snorm_zero,
    { have h_add_sub : ⇑f_lim - ⇑g_Lp_lim + ⇑g_Lp_lim =ᵐ[μ] 0 + ⇑g_Lp_lim,
        from h_snorm_zero.add eventually_eq.rfl,
      simpa using h_add_sub, },
    { exact (Lp.ae_measurable f_lim).sub h_g_lim_meas.ae_measurable, }, },
  suffices sub_tendsto : tendsto (λ (n : ι), snorm (⇑f_lim - ⇑g_Lp_lim) p μ) at_top (𝓝 0),
    from tendsto_nhds_unique tendsto_const_nhds sub_tendsto,
  -- `g` tends to `f_lim` since it is equal to `f` and `f` tends to `f_lim`
  have h_tendsto' : tendsto (λ (n : ι), snorm (g n - ⇑f_lim) p μ) at_top (𝓝 0),
  { suffices h_eq : ∀ (n : ι), snorm (g n - ⇑f_lim) p μ = snorm (⇑(f n) - ⇑f_lim) p μ,
      by { simp_rw h_eq, exact h_tendsto, },
    exact λ n, snorm_congr_ae ((hfg n).symm.sub eventually_eq.rfl), },
  -- `g` tends to `g_Lp_lim` by definition of `g_Lp_lim`
  have g_tendsto' : tendsto (λ (n : ι), snorm (g n - ⇑g_Lp_lim) p μ) at_top (𝓝 0),
  { suffices h_eq : ∀ (n : ι), snorm (g n - ⇑g_Lp_lim) p μ
        = @snorm α _ m _ (⇑(g_Lp n) - ⇑g_Lp_lim) p (μ.trim hm),
      by { simp_rw h_eq, exact g_tendsto, },
    intro n,
    have h_eq_g : snorm (g n - ⇑g_Lp_lim) p μ = snorm (⇑(g_Lp n) - ⇑g_Lp_lim) p μ,
      from snorm_congr_ae ((ae_eq_of_ae_eq_trim (h_g_ae_m n).symm).sub eventually_eq.rfl),
    rw h_eq_g,
    refine (snorm_trim hm _).symm,
    refine @measurable.sub α m _ _ _ _ (g_Lp n) g_Lp_lim _ h_g_lim_meas_m,
    exact @Lp.measurable α G m p (μ.trim hm) _ _ _ _ (g_Lp n), },
  -- we now conclude that the two limits of `g` are equal
  let snorm_add := λ (n : ι), snorm (g n - ⇑f_lim) p μ + snorm (g n - ⇑g_Lp_lim) p μ,
  have h_add_tendsto : tendsto snorm_add at_top (𝓝 0),
    by { rw ← add_zero (0 : ℝ≥0∞), exact tendsto.add h_tendsto' g_tendsto', },
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_add_tendsto
    (λ n, zero_le _) _,
  have h_add : (λ n, snorm (f_lim - g_Lp_lim) p μ)
      = λ n, snorm (f_lim - g n + (g n - g_Lp_lim)) p μ,
    by { ext1 n, congr, abel, },
  simp_rw h_add,
  refine λ n, (snorm_add_le _ _ hp.elim).trans _,
  { exact ((Lp.measurable f_lim).sub ((hg n).mono hm le_rfl)).ae_measurable, },
  { exact (((hg n).mono hm le_rfl).sub h_g_lim_meas).ae_measurable, },
  refine add_le_add_right (le_of_eq _) _,
  rw [← neg_sub, snorm_neg],
end

lemma ae_measurable'_of_tendsto (hm : m ≤ m0) [nonempty ι] [semilattice_sup ι] [hp : fact (1 ≤ p)]
  [complete_space G] (f : ι → Lp G p μ) (hf : ∀ n, ae_measurable' m (f n) μ) (f_lim : Lp G p μ)
  (h_tendsto : filter.at_top.tendsto f (𝓝 f_lim)) :
  ae_measurable' m f_lim μ :=
ae_measurable'_of_tendsto' hm f (λ n, (hf n).some) f_lim (λ n, (hf n).some_spec.2)
  (λ n, (hf n).some_spec.1) h_tendsto

lemma is_seq_closed_ae_measurable' [complete_space G] (hm : m ≤ m0) [hp : fact (1 ≤ p)] :
  is_seq_closed {f : Lp G p μ | ae_measurable' m f μ} :=
is_seq_closed_of_def (λ F f F_mem F_tendsto_f, ae_measurable'_of_tendsto hm F F_mem f F_tendsto_f)

lemma is_closed_ae_measurable' [complete_space G] (hm : m ≤ m0) [hp : fact (1 ≤ p)] :
  is_closed {f : Lp G p μ | ae_measurable' m f μ} :=
is_seq_closed_iff_is_closed.mp (is_seq_closed_ae_measurable' hm)

instance [hm : fact (m ≤ m0)] [complete_space F] [hp : fact (1 ≤ p)] :
  complete_space (Lp_sub F 𝕂 m p μ) :=
is_closed.complete_space_coe (is_closed_ae_measurable' hm.elim)

end complete_subspace

end Lp_sub

end measure_theory
