/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.constructions.borel_space.basic
import topology.metric_space.metrizable

/-!
# Measurable functions in (pseudo-)metrizable Borel spaces
-/

open filter measure_theory topological_space
open_locale classical topology nnreal ennreal measure_theory

variables {α β : Type*} [measurable_space α]

section limits

variables [topological_space β] [pseudo_metrizable_space β] [measurable_space β] [borel_space β]

open metric

/-- A limit (over a general filter) of measurable `ℝ≥0∞` valued functions is measurable. -/
lemma measurable_of_tendsto_ennreal' {ι} {f : ι → α → ℝ≥0∞} {g : α → ℝ≥0∞} (u : filter ι)
  [ne_bot u] [is_countably_generated u] (hf : ∀ i, measurable (f i)) (lim : tendsto f u (𝓝 g)) :
  measurable g :=
begin
  rcases u.exists_seq_tendsto with ⟨x, hx⟩,
  rw [tendsto_pi_nhds] at lim,
  have : (λ y, liminf (λ n, (f (x n) y : ℝ≥0∞)) at_top) = g :=
    by { ext1 y, exact ((lim y).comp hx).liminf_eq, },
  rw ← this,
  show measurable (λ y, liminf (λ n, (f (x n) y : ℝ≥0∞)) at_top),
  exact measurable_liminf (λ n, hf (x n)),
end

/-- A sequential limit of measurable `ℝ≥0∞` valued functions is measurable. -/
lemma measurable_of_tendsto_ennreal {f : ℕ → α → ℝ≥0∞} {g : α → ℝ≥0∞}
  (hf : ∀ i, measurable (f i)) (lim : tendsto f at_top (𝓝 g)) : measurable g :=
measurable_of_tendsto_ennreal' at_top hf lim

/-- A limit (over a general filter) of measurable `ℝ≥0` valued functions is measurable. -/
lemma measurable_of_tendsto_nnreal' {ι} {f : ι → α → ℝ≥0} {g : α → ℝ≥0} (u : filter ι)
  [ne_bot u] [is_countably_generated u] (hf : ∀ i, measurable (f i)) (lim : tendsto f u (𝓝 g)) :
  measurable g :=
begin
  simp_rw [← measurable_coe_nnreal_ennreal_iff] at hf ⊢,
  refine measurable_of_tendsto_ennreal' u hf _,
  rw tendsto_pi_nhds at lim ⊢,
  exact λ x, (ennreal.continuous_coe.tendsto (g x)).comp (lim x),
end

/-- A sequential limit of measurable `ℝ≥0` valued functions is measurable. -/
lemma measurable_of_tendsto_nnreal {f : ℕ → α → ℝ≥0} {g : α → ℝ≥0}
  (hf : ∀ i, measurable (f i)) (lim : tendsto f at_top (𝓝 g)) : measurable g :=
measurable_of_tendsto_nnreal' at_top hf lim

/-- A limit (over a general filter) of measurable functions valued in a (pseudo) metrizable space is
measurable. -/
lemma measurable_of_tendsto_metrizable' {ι} {f : ι → α → β} {g : α → β}
  (u : filter ι) [ne_bot u] [is_countably_generated u]
  (hf : ∀ i, measurable (f i)) (lim : tendsto f u (𝓝 g)) :
  measurable g :=
begin
  letI : pseudo_metric_space β := pseudo_metrizable_space_pseudo_metric β,
  apply measurable_of_is_closed', intros s h1s h2s h3s,
  have : measurable (λ x, inf_nndist (g x) s),
  { suffices : tendsto (λ i x, inf_nndist (f i x) s) u (𝓝 (λ x, inf_nndist (g x) s)),
      from measurable_of_tendsto_nnreal' u (λ i, (hf i).inf_nndist) this,
    rw [tendsto_pi_nhds] at lim ⊢, intro x,
    exact ((continuous_inf_nndist_pt s).tendsto (g x)).comp (lim x) },
  have h4s : g ⁻¹' s = (λ x, inf_nndist (g x) s) ⁻¹' {0},
  { ext x, simp [h1s, ← h1s.mem_iff_inf_dist_zero h2s, ← nnreal.coe_eq_zero] },
  rw [h4s], exact this (measurable_set_singleton 0),
end

/-- A sequential limit of measurable functions valued in a (pseudo) metrizable space is
measurable. -/
lemma measurable_of_tendsto_metrizable {f : ℕ → α → β} {g : α → β}
  (hf : ∀ i, measurable (f i)) (lim : tendsto f at_top (𝓝 g)) :
  measurable g :=
measurable_of_tendsto_metrizable' at_top hf lim

lemma ae_measurable_of_tendsto_metrizable_ae {ι}
  {μ : measure α} {f : ι → α → β} {g : α → β}
  (u : filter ι) [hu : ne_bot u] [is_countably_generated u]
  (hf : ∀ n, ae_measurable (f n) μ) (h_tendsto : ∀ᵐ x ∂μ, tendsto (λ n, f n x) u (𝓝 (g x))) :
  ae_measurable g μ :=
begin
  rcases u.exists_seq_tendsto with ⟨v, hv⟩,
  have h'f : ∀ n, ae_measurable (f (v n)) μ := λ n, hf (v n),
  set p : α → (ℕ → β) → Prop := λ x f', tendsto (λ n, f' n) at_top (𝓝 (g x)),
  have hp : ∀ᵐ x ∂μ, p x (λ n, f (v n) x),
    by filter_upwards [h_tendsto] with x hx using hx.comp hv,
  set ae_seq_lim := λ x, ite (x ∈ ae_seq_set h'f p) (g x) (⟨f (v 0) x⟩ : nonempty β).some with hs,
  refine ⟨ae_seq_lim, measurable_of_tendsto_metrizable' at_top (ae_seq.measurable h'f p)
    (tendsto_pi_nhds.mpr (λ x, _)), _⟩,
  { simp_rw [ae_seq, ae_seq_lim],
    split_ifs with hx,
    { simp_rw ae_seq.mk_eq_fun_of_mem_ae_seq_set h'f hx,
      exact @ae_seq.fun_prop_of_mem_ae_seq_set _ α β _ _ _ _ _ h'f x hx, },
    { exact tendsto_const_nhds } },
  { exact (ite_ae_eq_of_measure_compl_zero g (λ x, (⟨f (v 0) x⟩ : nonempty β).some)
      (ae_seq_set h'f p) (ae_seq.measure_compl_ae_seq_set_eq_zero h'f hp)).symm },
end

lemma ae_measurable_of_tendsto_metrizable_ae' {μ : measure α} {f : ℕ → α → β} {g : α → β}
  (hf : ∀ n, ae_measurable (f n) μ)
  (h_ae_tendsto : ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (𝓝 (g x))) :
  ae_measurable g μ :=
ae_measurable_of_tendsto_metrizable_ae at_top hf h_ae_tendsto

lemma ae_measurable_of_unif_approx {β} [measurable_space β] [pseudo_metric_space β] [borel_space β]
  {μ : measure α} {g : α → β}
  (hf : ∀ ε > (0 : ℝ), ∃ (f : α → β), ae_measurable f μ ∧ ∀ᵐ x ∂μ, dist (f x) (g x) ≤ ε) :
  ae_measurable g μ :=
begin
  obtain ⟨u, u_anti, u_pos, u_lim⟩ :
    ∃ (u : ℕ → ℝ), strict_anti u ∧ (∀ (n : ℕ), 0 < u n) ∧ tendsto u at_top (𝓝 0) :=
      exists_seq_strict_anti_tendsto (0 : ℝ),
  choose f Hf using λ (n : ℕ), hf (u n) (u_pos n),
  have : ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (𝓝 (g x)),
  { have : ∀ᵐ x ∂ μ, ∀ n, dist (f n x) (g x) ≤ u n := ae_all_iff.2 (λ n, (Hf n).2),
    filter_upwards [this],
    assume x hx,
    rw tendsto_iff_dist_tendsto_zero,
    exact squeeze_zero (λ n, dist_nonneg) hx u_lim },
  exact ae_measurable_of_tendsto_metrizable_ae' (λ n, (Hf n).1) this,
end

lemma measurable_of_tendsto_metrizable_ae {μ : measure α} [μ.is_complete] {f : ℕ → α → β}
  {g : α → β} (hf : ∀ n, measurable (f n))
  (h_ae_tendsto : ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (𝓝 (g x))) :
  measurable g :=
ae_measurable_iff_measurable.mp
  (ae_measurable_of_tendsto_metrizable_ae' (λ i, (hf i).ae_measurable) h_ae_tendsto)

lemma measurable_limit_of_tendsto_metrizable_ae {ι} [countable ι] [nonempty ι] {μ : measure α}
  {f : ι → α → β} {L : filter ι} [L.is_countably_generated] (hf : ∀ n, ae_measurable (f n) μ)
  (h_ae_tendsto : ∀ᵐ x ∂μ, ∃ l : β, tendsto (λ n, f n x) L (𝓝 l)) :
  ∃ (f_lim : α → β) (hf_lim_meas : measurable f_lim),
    ∀ᵐ x ∂μ, tendsto (λ n, f n x) L (𝓝 (f_lim x)) :=
begin
  inhabit ι,
  unfreezingI { rcases eq_or_ne L ⊥ with rfl | hL },
  { exact ⟨(hf default).mk _, (hf default).measurable_mk,
      eventually_of_forall $ λ x, tendsto_bot⟩ },
  haveI : ne_bot L := ⟨hL⟩,
  let p : α → (ι → β) → Prop := λ x f', ∃ l : β, tendsto (λ n, f' n) L (𝓝 l),
  have hp_mem : ∀ x ∈ ae_seq_set hf p, p x (λ n, f n x),
    from λ x hx, ae_seq.fun_prop_of_mem_ae_seq_set hf hx,
  have h_ae_eq : ∀ᵐ x ∂μ, ∀ n, ae_seq hf p n x = f n x,
    from ae_seq.ae_seq_eq_fun_ae hf h_ae_tendsto,
  let f_lim : α → β := λ x, dite (x ∈ ae_seq_set hf p) (λ h, (hp_mem x h).some)
    (λ h, (⟨f default x⟩ : nonempty β).some),
  have hf_lim : ∀ x, tendsto (λ n, ae_seq hf p n x) L (𝓝 (f_lim x)),
  { intros x,
    simp only [f_lim, ae_seq],
    split_ifs,
    { refine (hp_mem x h).some_spec.congr (λ n, _),
      exact (ae_seq.mk_eq_fun_of_mem_ae_seq_set hf h n).symm },
    { exact tendsto_const_nhds, }, },
  have h_ae_tendsto_f_lim : ∀ᵐ x ∂μ, tendsto (λ n, f n x) L (𝓝 (f_lim x)),
    from h_ae_eq.mono (λ x hx, (hf_lim x).congr hx),
  have h_f_lim_meas : measurable f_lim,
    from measurable_of_tendsto_metrizable' L (ae_seq.measurable hf p)
      (tendsto_pi_nhds.mpr (λ x, hf_lim x)),
  exact ⟨f_lim, h_f_lim_meas, h_ae_tendsto_f_lim⟩,
end

end limits
