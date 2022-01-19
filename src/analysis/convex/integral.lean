/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import analysis.convex.function
import measure_theory.integral.set_integral

/-!
# Jensen's inequality for integrals

In this file we prove several versions of Jensen's inequality. Here we list key differences between
these lemmas and explain how they affect names of the lemmas.

- We prove inequalities for convex functions (in the namespaces `convex_on` and `strict_convex_on`):
  `g ((μ univ)⁻¹ • ∫ x, f x ∂μ) ≤ (μ univ)⁻¹ • ∫ x, g (f x) ∂μ`, and for convex sets (int the
  namespace `convex`): if `∀ᵐ x ∂μ, f x ∈ s`, then `(μ univ)⁻¹ • ∫ x, f x ∂μ ∈ s`.

- We prove inequalities for average values over the whole space w.r.t. to a finite measure
  (`...smul_integral...`), to a probability measure (`...integral...`), or over a set
  (`...smul_set_integral...`).

- We prove strict inequality (has `lt` in the name, all versions but one are in the
  `strict_convex_on` namespace) and non-strict inequalities.

## Tags

convex, integral, center mass, Jensen's inequality
-/

open measure_theory metric set filter topological_space
open_locale topological_space big_operators ennreal

variables {α E : Type*} [measurable_space α] {μ : measure α}
  [normed_group E] [normed_space ℝ E] [complete_space E]
  [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]

/-!
### Non-strict Jensen's inequality
-/

/-- An auxiliary lemma for `convex.smul_integral_mem`. -/
protected lemma convex.smul_integral_mem_of_measurable
  [is_finite_measure μ] {s : set E} (hs : convex ℝ s) (hsc : is_closed s)
  (hμ : μ ≠ 0) {f : α → E} (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : integrable f μ) (hfm : measurable f) :
  (μ univ).to_real⁻¹ • ∫ x, f x ∂μ ∈ s :=
begin
  unfreezingI { rcases eq_empty_or_nonempty s with rfl|⟨y₀, h₀⟩ },
  { refine (hμ _).elim, simpa using hfs },
  rw ← hsc.closure_eq at hfs,
  have hc : integrable (λ _, y₀) μ := integrable_const _,
  set F : ℕ → simple_func α E := simple_func.approx_on f hfm s y₀ h₀,
  have : tendsto (λ n, (F n).integral μ) at_top (𝓝 $ ∫ x, f x ∂μ),
  { simp only [simple_func.integral_eq_integral _
      (simple_func.integrable_approx_on hfm hfi h₀ hc _)],
    exact tendsto_integral_of_L1 _ hfi
      (eventually_of_forall $ simple_func.integrable_approx_on hfm hfi h₀ hc)
      (simple_func.tendsto_approx_on_L1_nnnorm hfm h₀ hfs (hfi.sub hc).2) },
  refine hsc.mem_of_tendsto (tendsto_const_nhds.smul this) (eventually_of_forall $ λ n, _),
  have : ∑ y in (F n).range, (μ ((F n) ⁻¹' {y})).to_real = (μ univ).to_real,
    by rw [← (F n).sum_range_measure_preimage_singleton, @ennreal.to_real_sum _ _
      (λ y, μ ((F n) ⁻¹' {y})) (λ _ _, (measure_ne_top _ _))],
  rw [← this, simple_func.integral],
  refine hs.center_mass_mem (λ _ _, ennreal.to_real_nonneg) _ _,
  { rw this,
    exact ennreal.to_real_pos (mt measure.measure_univ_eq_zero.mp hμ) (measure_ne_top _ _) },
  { simp only [simple_func.mem_range],
    rintros _ ⟨x, rfl⟩,
    exact simple_func.approx_on_mem hfm h₀ n x }
end

/-- If `μ` is a non-zero finite measure on `α`, `s` is a convex closed set in `E`, and `f` is an
integrable function sending `μ`-a.e. points to `s`, then the average value of `f` belongs to `s`:
`(μ univ).to_real⁻¹ • ∫ x, f x ∂μ ∈ s`. See also `convex.center_mass_mem` for a finite sum version
of this lemma. -/
lemma convex.smul_integral_mem
  [is_finite_measure μ] {s : set E} (hs : convex ℝ s) (hsc : is_closed s)
  (hμ : μ ≠ 0) {f : α → E} (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : integrable f μ) :
  (μ univ).to_real⁻¹ • ∫ x, f x ∂μ ∈ s :=
begin
  have : ∀ᵐ (x : α) ∂μ, hfi.ae_measurable.mk f x ∈ s,
  { filter_upwards [hfs, hfi.ae_measurable.ae_eq_mk],
    assume a ha h,
    rwa ← h },
  convert convex.smul_integral_mem_of_measurable hs hsc hμ this
    (hfi.congr hfi.ae_measurable.ae_eq_mk) (hfi.ae_measurable.measurable_mk) using 2,
  apply integral_congr_ae,
  exact hfi.ae_measurable.ae_eq_mk
end

/-- If `μ` is a non-zero finite measure on `α`, `s` is a convex closed set in `E`, and `f` is an
integrable function sending `μ`-a.e. points to `s`, then the average value of `f` belongs to `s`:
`(μ univ).to_real⁻¹ • ∫ x, f x ∂μ ∈ s`. See also `convex.center_mass_mem` for a finite sum version
of this lemma. -/
lemma convex.smul_set_integral_mem {t : set α} {s : set E} (hs : convex ℝ s) (hsc : is_closed s)
  (h0 : μ t ≠ 0) (ht : μ t ≠ ∞) {f : α → E} (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s)
  (hfi : integrable_on f t μ) :
  (μ t).to_real⁻¹ • ∫ x in t, f x ∂μ ∈ s :=
begin
  haveI : fact (μ t < ∞) := ⟨ht.lt_top⟩,
  rw ← measure.restrict_apply_univ t at h0 ⊢,
  refine hs.smul_integral_mem hsc _ hfs hfi,
  rwa [ne.def, ← measure.measure_univ_eq_zero]
end

/-- If `μ` is a probability measure on `α`, `s` is a convex closed set in `E`, and `f` is an
integrable function sending `μ`-a.e. points to `s`, then the expected value of `f` belongs to `s`:
`∫ x, f x ∂μ ∈ s`. See also `convex.sum_mem` for a finite sum version of this lemma. -/
lemma convex.integral_mem [is_probability_measure μ] {s : set E} (hs : convex ℝ s)
  (hsc : is_closed s) {f : α → E} (hf : ∀ᵐ x ∂μ, f x ∈ s) (hfi : integrable f μ) :
  ∫ x, f x ∂μ ∈ s :=
by simpa [measure_univ] using hs.smul_integral_mem hsc (is_probability_measure.ne_zero μ) hf hfi

/-- Jensen's inequality: if a function `g : E → ℝ` is convex and continuous on a convex closed set
`s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function sending `μ`-a.e. points
to `s`, then the value of `g` at the average value of `f` is less than or equal to the average value
of `g ∘ f` provided that both `f` and `g ∘ f` are integrable. See also `convex.map_center_mass_le`
for a finite sum version of this lemma. -/
lemma convex_on.map_smul_integral_le [is_finite_measure μ] {s : set E} {g : E → ℝ}
  (hg : convex_on ℝ s g) (hgc : continuous_on g s) (hsc : is_closed s) (hμ : μ ≠ 0) {f : α → E}
  (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : integrable f μ) (hgi : integrable (g ∘ f) μ) :
  g ((μ univ).to_real⁻¹ • ∫ x, f x ∂μ) ≤ (μ univ).to_real⁻¹ • ∫ x, g (f x) ∂μ :=
begin
  set t := {p : E × ℝ | p.1 ∈ s ∧ g p.1 ≤ p.2},
  have ht_conv : convex ℝ t := hg.convex_epigraph,
  have ht_closed : is_closed t :=
    (hsc.preimage continuous_fst).is_closed_le (hgc.comp continuous_on_fst (subset.refl _))
      continuous_on_snd,
  have ht_mem : ∀ᵐ x ∂μ, (f x, g (f x)) ∈ t := hfs.mono (λ x hx, ⟨hx, le_rfl⟩),
  simpa [integral_pair hfi hgi]
    using (ht_conv.smul_integral_mem ht_closed hμ ht_mem (hfi.prod_mk hgi)).2
end

/-- Jensen's inequality: if a function `g : E → ℝ` is convex and continuous on a convex closed set
`s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function sending `μ`-a.e. points
of a set `t` to `s`, then the value of `g` at the average value of `f` over `t` is less than or
equal to the average value of `g ∘ f` over `t` provided that both `f` and `g ∘ f` are
integrable. -/
lemma convex_on.map_smul_set_integral_le [is_finite_measure μ] {s : set E} {g : E → ℝ}
  (hg : convex_on ℝ s g) (hgc : continuous_on g s) (hsc : is_closed s) {t : set α} (h0 : μ t ≠ 0)
  (ht : μ t ≠ ∞) {f : α → E} (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s) (hfi : integrable_on f t μ)
  (hgi : integrable_on (g ∘ f) t μ) :
  g ((μ t).to_real⁻¹ • ∫ x in t, f x ∂μ) ≤ (μ t).to_real⁻¹ • ∫ x in t, g (f x) ∂μ :=
begin
  haveI : fact (μ t < ∞) := ⟨ht.lt_top⟩,
  rw ← measure.restrict_apply_univ t at h0 ⊢,
  refine hg.map_smul_integral_le hgc hsc _ hfs hfi hgi,
  rwa [ne.def, ← measure.measure_univ_eq_zero]
end

/-- Convex **Jensen's inequality**: if a function `g : E → ℝ` is convex and continuous on a convex
closed set `s`, `μ` is a probability measure on `α`, and `f : α → E` is a function sending `μ`-a.e.
points to `s`, then the value of `g` at the expected value of `f` is less than or equal to the
expected value of `g ∘ f` provided that both `f` and `g ∘ f` are integrable. See also
`convex_on.map_center_mass_le` for a finite sum version of this lemma. -/
lemma convex_on.map_integral_le [is_probability_measure μ] {s : set E} {g : E → ℝ}
  (hg : convex_on ℝ s g) (hgc : continuous_on g s) (hsc : is_closed s) {f : α → E}
  (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : integrable f μ) (hgi : integrable (g ∘ f) μ) :
  g (∫ x, f x ∂μ) ≤ ∫ x, g (f x) ∂μ :=
by simpa [measure_univ]
  using hg.map_smul_integral_le hgc hsc (is_probability_measure.ne_zero μ) hfs hfi hgi

/-- Strict **Jensen's inequality**. Suppose that a function `g : E → ℝ` is convex and continuous on
a convex closed set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function
sending `μ`-a.e. points to `s`. Also assume that for some set `t` of nonzero measure, the value of
`g` at the average value of `f` over `t` is strictly less than the average value of `g ∘ f` over
`t`. Then the value of `g` at the average value of `f` over the whole space is strictly less than
the average value of `g ∘ f` provided that both `f` and `g ∘ f` are integrable. -/
lemma convex_on.map_smul_integral_lt_of_exists_set [is_finite_measure μ] {s : set E} {g : E → ℝ}
  (hg : convex_on ℝ s g) (hgc : continuous_on g s) (hsc : is_closed s) (hμ : μ ≠ 0) {f : α → E}
  (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : integrable f μ) (hgi : integrable (g ∘ f) μ)
  (H : ∃ t, μ t ≠ 0 ∧
    g ((μ t).to_real⁻¹ • ∫ x in t, f x ∂μ) < (μ t).to_real⁻¹ * ∫ x in t, g (f x) ∂μ) :
  g ((μ univ).to_real⁻¹ • ∫ x, f x ∂μ) < (μ univ).to_real⁻¹ * ∫ x, g (f x) ∂μ :=
begin
  obtain ⟨t, htm, ht₀, ht_lt⟩ : ∃ t, measurable_set t ∧ μ t ≠ 0 ∧
    g ((μ t).to_real⁻¹ • ∫ x in t, f x ∂μ) < (μ t).to_real⁻¹ • ∫ x in t, g (f x) ∂μ,
  { rcases H with ⟨t, ht⟩,
    refine ⟨to_measurable μ t, measurable_set_to_measurable _ _, _⟩,
    rwa [measure_to_measurable, measure.restrict_to_measurable (measure_ne_top μ t)] },
  clear H,
  set ν : set α → ℝ := λ u, (μ u).to_real,
  set I : set α → E := λ u, (ν u)⁻¹ • ∫ x in u, f x ∂μ,
  set J : set α → ℝ := λ u, (ν u)⁻¹ * ∫ x in u, g (f x) ∂μ,
  have hν₀ : 0 < ν t, from ennreal.to_real_pos ht₀ (measure_ne_top _ _),
  cases (@ennreal.to_real_nonneg (μ tᶜ)).eq_or_lt with hν₀' hν₀',
  { have A : t =ᵐ[μ] univ,
      by simpa only [eventually_eq_univ, mem_ae_iff, ennreal.to_real_eq_zero_iff,
        measure_ne_top, or_false] using hν₀'.symm,
    simpa only [measure_congr A, set_integral_congr_set_ae A, integral_univ] using ht_lt },
  have ht₀' : μ tᶜ ≠ 0, from λ H, hν₀'.ne' ((ennreal.to_real_eq_zero_iff _).2 $ or.inl H),
  have hνt_add : ν t + ν tᶜ = ν univ,
    by rw [← ennreal.to_real_add (measure_ne_top μ _) (measure_ne_top μ _),
      measure_add_measure_compl htm],
  have hν₀_add : 0 < ν t + ν tᶜ, from add_pos hν₀ hν₀',
  calc g ((ν univ)⁻¹ • ∫ x, f x ∂μ)
      = g ((ν t / (ν t + ν tᶜ)) • I t + (ν tᶜ / (ν t + ν tᶜ)) • I tᶜ) :
    by rw [smul_smul, smul_smul, hνt_add, ← mul_div_right_comm, mul_inv_cancel hν₀.ne',
      ← mul_div_right_comm, mul_inv_cancel hν₀'.ne', one_div, ← smul_add,
      integral_add_compl htm hfi]
  ... ≤ (ν t / (ν t + ν tᶜ)) * g (I t) + (ν tᶜ / (ν t + ν tᶜ)) * g (I tᶜ) :
    (convex_on_iff_div.1 hg).2
      (hg.1.smul_set_integral_mem hsc ht₀ (measure_ne_top _ _) (ae_restrict_of_ae hfs)
        hfi.integrable_on)
      (hg.1.smul_set_integral_mem hsc ht₀' (measure_ne_top _ _) (ae_restrict_of_ae hfs)
        hfi.integrable_on) ennreal.to_real_nonneg ennreal.to_real_nonneg hν₀_add
  ... < (ν t / (ν t + ν tᶜ)) * J t + (ν tᶜ / (ν t + ν tᶜ)) * J tᶜ :
    add_lt_add_of_lt_of_le ((mul_lt_mul_left $ div_pos hν₀ hν₀_add).2 ht_lt) $
      flip mul_le_mul_of_nonneg_left (div_pos hν₀' hν₀_add).le $
        hg.map_smul_set_integral_le hgc hsc ht₀' (measure_ne_top _ _) (ae_restrict_of_ae hfs)
          hfi.integrable_on hgi.integrable_on
  ... = (μ univ).to_real⁻¹ * ∫ x, g (f x) ∂μ :
    by rw [← mul_assoc, ← mul_assoc, hνt_add, ← mul_div_right_comm, mul_inv_cancel hν₀.ne', one_div,
      ← mul_div_right_comm, mul_inv_cancel hν₀'.ne', one_div, ← mul_add,
      integral_add_compl htm hgi]
end

/-- Strict **Jensen's inequality**. Suppose that a function `g : E → ℝ` is strictly convex and
continuous on a convex closed set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a
function sending `μ`-a.e. points to `s`. Also assume that both `f` and `g ∘ f` are integrable. Then
either `f` is a.e. constant, or the value of `g` at the average value of `f` over the whole space is
strictly less than the average value of `g ∘ f`. -/
lemma strict_convex_on.ae_eq_const_or_map_smul_integral_lt [is_finite_measure μ] {s : set E}
  {g : E → ℝ} (hg : strict_convex_on ℝ s g) (hgc : continuous_on g s) (hsc : is_closed s)
  {f : α → E} (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : integrable f μ)
  (hgi : integrable (g ∘ f) μ) :
  (∃ c : E, f =ᵐ[μ] function.const α c) ∨
    g ((μ univ).to_real⁻¹ • ∫ x, f x ∂μ) < (μ univ).to_real⁻¹ • ∫ x, g (f x) ∂μ :=
begin
  cases eq_or_ne μ 0 with hμ hμ, { refine or.inl ⟨0, _⟩, simp [hμ] },
  refine or_iff_not_imp_left.mpr (λ H, _),
  apply hg.convex_on.map_smul_integral_lt_of_exists_set hgc hsc hμ hfs hfi hgi,
  simp only [not_exists, eventually_eq, not_eventually] at H,
  rcases exists_ne_forall_mem_nhds_pos_measure_preimage H
    with ⟨a, b, hne, ha : ∀ s ∈ 𝓝 a, 0 < μ (f ⁻¹' s), hb : ∀ s ∈ 𝓝 b, 0 < μ (f ⁻¹' s)⟩,
  obtain ⟨r, hr₀, hd⟩ : ∃ r : ℝ, 0 < r ∧ disjoint (closed_ball a r) (closed_ball b r),
  { rcases exists_pos_mul_lt (dist_pos.2 hne) 2 with ⟨r, hr₀, hr⟩,
    exact ⟨r, hr₀, closed_ball_disjoint_closed_ball $ two_mul r ▸ hr⟩ },
  set Ba := f ⁻¹' closed_ball a r, set Bb := f ⁻¹' closed_ball b r,
  have hBa : 0 < μ Ba, from ha _ (closed_ball_mem_nhds _ hr₀),
  have hBb : 0 < μ Bb, from hb _ (closed_ball_mem_nhds _ hr₀),
  have hBa' : 0 < (μ Ba).to_real, from ennreal.to_real_pos hBa.ne' (measure_ne_top _ _),
  have hBb' : 0 < (μ Bb).to_real, from ennreal.to_real_pos hBb.ne' (measure_ne_top _ _),
  have hBab : 0 < μ (Ba ∪ Bb), from hBa.trans_le (measure_mono $ subset_union_left _ _),
  refine ⟨Ba ∪ Bb, hBab.ne', _⟩,
  have hBd : ae_disjoint μ Ba Bb, from (hd.preimage f).ae_disjoint,
  have hBam : null_measurable_set Ba μ, from hfi.1.null_measurable measurable_set_closed_ball,
  have hBbm : null_measurable_set Bb μ, from hfi.1.null_measurable measurable_set_closed_ball,
  obtain ⟨has, har⟩  : (μ Ba).to_real⁻¹ • ∫ x in Ba, f x ∂μ ∈ s ∩ closed_ball a r,
    from (hg.1.inter (convex_closed_ball _ _)).smul_set_integral_mem (hsc.inter is_closed_ball)
      hBa.ne' (measure_ne_top _ _) ((ae_restrict_of_ae hfs).and (ae_restrict_mem₀ hBam))
      hfi.integrable_on,
  obtain ⟨hbs, hbr⟩ : (μ Bb).to_real⁻¹ • ∫ x in Bb, f x ∂μ ∈ s ∩ closed_ball b r,
    from (hg.1.inter (convex_closed_ball _ _)).smul_set_integral_mem (hsc.inter is_closed_ball)
      hBb.ne' (measure_ne_top _ _) ((ae_restrict_of_ae hfs).and (ae_restrict_mem₀ hBbm))
      hfi.integrable_on,
  rw [measure_union₀ hBbm hBd, ennreal.to_real_add (measure_ne_top μ _) (measure_ne_top μ _),
      integral_union_ae hBd hBbm hfi.integrable_on hfi.integrable_on, smul_add,
      integral_union_ae hBd hBbm hgi.integrable_on hgi.integrable_on, mul_add],
  set ca := (μ Ba).to_real, set cb := (μ Bb).to_real,
  have hca : (ca / (ca + cb)) * ca⁻¹ = (ca + cb)⁻¹,
    by rw [← mul_div_right_comm, mul_inv_cancel hBa'.ne', one_div],
  have hcb : (cb / (ca + cb)) * cb⁻¹ = (ca + cb)⁻¹,
    by rw [← mul_div_right_comm, mul_inv_cancel hBb'.ne', one_div],
  calc g ((ca + cb)⁻¹ • ∫ x in Ba, f x ∂μ + (ca + cb)⁻¹ • ∫ x in Bb, f x ∂μ)
      = g ((ca / (ca + cb)) • ca⁻¹ • ∫ x in Ba, f x ∂μ +
          (cb / (ca + cb)) • cb⁻¹ • ∫ x in Bb, f x ∂μ) :
    by rw [smul_smul, smul_smul, hca, hcb]
  ... < (ca / (ca + cb)) * g (ca⁻¹ • ∫ x in Ba, f x ∂μ) +
          (cb / (ca + cb)) * g (cb⁻¹ • ∫ x in Bb, f x ∂μ) :
    (strict_convex_on_iff_div.1 hg).2 has hbs (hd.ne_of_mem har hbr) hBa' hBb'
  ... ≤ (ca / (ca + cb)) * (ca⁻¹ * ∫ x in Ba, g (f x) ∂μ) +
          (cb / (ca + cb)) * (cb⁻¹ * ∫ x in Bb, g (f x) ∂μ) :
    add_le_add
      (mul_le_mul_of_nonneg_left (hg.convex_on.map_smul_set_integral_le hgc hsc hBa.ne'
        (measure_ne_top _ _) (ae_restrict_of_ae hfs) hfi.integrable_on hgi.integrable_on)
        (div_pos hBa' (add_pos hBa' hBb')).le)
      (mul_le_mul_of_nonneg_left (hg.convex_on.map_smul_set_integral_le hgc hsc hBb.ne'
        (measure_ne_top _ _) (ae_restrict_of_ae hfs) hfi.integrable_on hgi.integrable_on)
        (div_pos hBb' (add_pos hBa' hBb')).le)
  ... = (ca + cb)⁻¹ * ∫ x in Ba, g (f x) ∂μ + (ca + cb)⁻¹ * ∫ x in Bb, g (f x) ∂μ :
    by simp only [← mul_assoc, hca, hcb]
end

/-- If the norm of a function `f : α → E` taking values in a strictly convex normed space is
a.e. less than or equal to `C`, then either this function is a constant, or the norm of its integral
is strictly less than `μ univ * C`. -/
lemma ae_eq_const_or_norm_integral_lt_of_norm_le_const [is_finite_measure μ] {f : α → E} {C : ℝ}
  (h_le : ∀ᵐ x ∂μ, ∥f x∥ ≤ C)
  (h_convex : strict_convex_on ℝ (closed_ball (0 : E) C) (norm : E → ℝ)) :
  (∃ c : E, f =ᵐ[μ] function.const α c) ∨ ∥∫ x, f x ∂μ∥ < (μ univ).to_real * C :=
begin
  cases le_or_lt C 0 with hC0 hC0,
  { exact or.inl ⟨0, h_le.mono $ λ x hx, norm_le_zero_iff.1 $ hx.trans hC0⟩ },
  cases eq_or_ne μ 0 with hμ hμ,
  { rw hμ, exact or.inl ⟨0, rfl⟩ },
  by_cases hfi : integrable f μ, swap,
  { right,
    simpa [integral_undef hfi, hC0, measure_lt_top, ennreal.to_real_pos_iff, pos_iff_ne_zero]
      using hμ },
  refine (h_convex.ae_eq_const_or_map_smul_integral_lt continuous_norm.continuous_on is_closed_ball
    _ hfi hfi.norm).imp_right (λ h, _),
  { rw [norm_smul, normed_field.norm_inv, real.norm_eq_abs, abs_of_nonneg ennreal.to_real_nonneg,
      smul_eq_mul, mul_lt_mul_left] at h,
    { calc ∥∫ x, f x ∂μ∥ < ∫ x, ∥f x∥ ∂μ : h
      ... ≤ ∫ x, C ∂μ : integral_mono_ae hfi.norm (integrable_const _) h_le
      ... = _ : integral_const _ },
    { refine inv_pos.2 (ennreal.to_real_pos _ (measure_ne_top _ _)),
      rwa [ne.def, measure.measure_univ_eq_zero] } },
  { simpa }
end
