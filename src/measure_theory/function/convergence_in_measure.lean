/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import measure_theory.function.uniform_integrable

/-!
# Convergence in measure

-/

open topological_space filter
open_locale nnreal ennreal measure_theory topological_space

namespace measure_theory

variables {α ι E : Type*} {m : measurable_space α} {μ : measure α}

/-
Update undergrad.yaml
- add Markov's inequality
- add convergence in Lp and in measure
-/

/-- TODO -/
def tendsto_locally_in_measure [preorder ι] [has_dist E] {m : measurable_space α}
  (μ : measure α) (f : ι → α → E) (g : α → E) : Prop :=
∀ s (hs : measurable_set s) (hμs : 0 < μ s), ∀ ε (hε : 0 < ε),
  tendsto (λ i, μ {x ∈ s | ε ≤ dist (f i x) (g x)}) at_top (𝓝 0)

/-- TODO -/
def tendsto_in_measure [preorder ι] [has_dist E] {m : measurable_space α}
  (μ : measure α) (f : ι → α → E) (g : α → E) : Prop :=
∀ ε (hε : 0 < ε), tendsto (λ i, μ {x | ε ≤ dist (f i x) (g x)}) at_top (𝓝 0)

section move

protected lemma ennreal.tendsto.rpow {f : filter α} {m : α → ℝ≥0∞} {a : ℝ≥0∞} (r : ℝ)
  (hm : tendsto m f (𝓝 a)) :
  tendsto (λ x, (m x) ^ r) f (𝓝 (a ^ r)) :=
(ennreal.continuous_rpow_const.tendsto a).comp hm

end move

section Lp

variables [measurable_space E] [normed_group E] [borel_space E] {p : ℝ≥0∞} {f : α → E}

variable (μ)

lemma mul_meas_ge_pow_le_snorm
  (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) (hf : measurable f) (ε : ℝ≥0∞) :
  (ε * μ {x | ε ≤ ∥f x∥₊ ^ p.to_real}) ^ (1 / p.to_real) ≤ snorm f p μ :=
begin
  rw snorm_eq_lintegral_rpow_nnnorm hp_ne_zero hp_ne_top,
  exact ennreal.rpow_le_rpow (mul_meas_ge_le_lintegral
      (measurable.pow_const (measurable.coe_nnreal_ennreal (hf.nnnorm)) _) ε)
      (one_div_nonneg.2 ennreal.to_real_nonneg),
end

lemma mul_meas_ge_le_snorm_pow
  (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) (hf : measurable f) (ε : ℝ≥0∞) :
  ε * μ {x | ε ≤ ∥f x∥₊ ^ p.to_real} ≤ snorm f p μ ^ p.to_real :=
begin
  have : 1 / p.to_real * p.to_real = 1,
  { refine one_div_mul_cancel _,
    rw [ne, ennreal.to_real_eq_zero_iff],
    exact not_or hp_ne_zero hp_ne_top },
  rw [← ennreal.rpow_one (ε * μ {x | ε ≤ ∥f x∥₊ ^ p.to_real}), ← this, ennreal.rpow_mul],
  exact ennreal.rpow_le_rpow (mul_meas_ge_pow_le_snorm μ hp_ne_zero hp_ne_top hf ε)
    ennreal.to_real_nonneg,
end

lemma mul_meas_ge_le_snorm_pow'
  (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) (hf : measurable f) (ε : ℝ≥0∞) :
  ε ^ p.to_real * μ {x | ε ≤ ∥f x∥₊} ≤ snorm f p μ ^ p.to_real :=
begin
  convert mul_meas_ge_le_snorm_pow μ hp_ne_zero hp_ne_top hf  (ε ^ p.to_real),
  ext x,
  rw ennreal.rpow_le_rpow_iff (ennreal.to_real_pos hp_ne_zero hp_ne_top),
end

end Lp

lemma tendsto_in_measure_iff_norm [preorder ι] [semi_normed_group E] {f : ι → α → E} {g : α → E} :
  tendsto_in_measure μ f g
    ↔ ∀ ε (hε : 0 < ε), tendsto (λ i, μ {x | ε ≤ ∥f i x - g x∥}) at_top (𝓝 0) :=
by simp_rw [tendsto_in_measure, dist_eq_norm]

namespace tendsto_in_measure

protected lemma tendsto_locally_in_measure [preorder ι] [has_dist E] {f : ι → α → E} {g : α → E}
  (h : tendsto_in_measure μ f g) :
  tendsto_locally_in_measure μ f g :=
begin
  intros s hs hμs ε hε,
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h ε hε) (λ i, zero_le _) _,
  exact λ i, measure_mono (λ x, by simp),
end

protected lemma congr [preorder ι] [has_dist E] {f f' : ι → α → E} {g g' : α → E}
  (h_left : ∀ i, f i =ᵐ[μ] f' i) (h_right : g =ᵐ[μ] g') (h_tendsto : tendsto_in_measure μ f g) :
  tendsto_in_measure μ f' g' :=
begin
  intros ε hε,
  specialize h_tendsto ε hε,
  suffices : (λ i, μ {x | ε ≤ dist (f' i x) (g' x)}) = (λ i, μ {x | ε ≤ dist (f i x) (g x)}),
    by rwa this,
  ext1 i,
  refine measure_congr _,
  refine (h_left i).mp _,
  refine h_right.mono (λ x hxg hxf, _),
  rw eq_iff_iff,
  change ε ≤ dist (f' i x) (g' x) ↔ ε ≤ dist (f i x) (g x),
  rw [hxg, hxf],
end

lemma congr_left [preorder ι] [has_dist E] {f f' : ι → α → E} {g : α → E}
  (h : ∀ i, f i =ᵐ[μ] f' i) (h_tendsto : tendsto_in_measure μ f g) :
  tendsto_in_measure μ f' g :=
h_tendsto.congr h (eventually_eq.rfl)

lemma congr_right [preorder ι] [has_dist E] {f : ι → α → E} {g g' : α → E}
  (h : g =ᵐ[μ] g') (h_tendsto : tendsto_in_measure μ f g) :
  tendsto_in_measure μ f g' :=
h_tendsto.congr (λ i, eventually_eq.rfl) h

end tendsto_in_measure

section

variables [metric_space E] [second_countable_topology E] [measurable_space E] [borel_space E]
variables {f : ℕ → α → E} {g : α → E}

/-- Convergence a.e. implies convergence in measure in a finite measure space. -/
lemma tendsto_in_measure_of_tendsto_ae [is_finite_measure μ]
  (hf : ∀ n, measurable (f n)) (hg : measurable g)
  (hfg : ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (𝓝 (g x))) :
  tendsto_in_measure μ f g :=
begin
  refine λ ε hε, ennreal.tendsto_at_top_zero.mpr (λ δ hδ, _),
  by_cases hδi : δ = ∞,
  { simp only [hδi, implies_true_iff, le_top, exists_const], },
  lift δ to ℝ≥0 using hδi,
  rw [gt_iff_lt, ennreal.coe_pos, ← nnreal.coe_pos] at hδ,
  obtain ⟨t, htm, ht, hunif⟩ := tendsto_uniformly_on_of_ae_tendsto' hf hg hfg hδ,
  rw ennreal.of_real_coe_nnreal at ht,
  rw metric.tendsto_uniformly_on_iff at hunif,
  obtain ⟨N, hN⟩ := eventually_at_top.1 (hunif ε hε),
  refine ⟨N, λ n hn, _⟩,
  suffices : {x : α | ε ≤ dist (f n x) (g x)} ⊆ t, from (measure_mono this).trans ht,
  rw ← set.compl_subset_compl,
  intros x hx,
  rw [set.mem_compl_eq, set.nmem_set_of_eq, dist_comm, not_le],
  exact hN n hn x hx,
end

lemma tendsto_in_measure.exists_seq_tendsto_ae [is_finite_measure μ]
  (hf : ∀ n, measurable (f n)) (hg : measurable g)
  (hfg : tendsto_in_measure μ f g) :
  ∃ ns : ℕ → ℕ, ∀ᵐ x ∂μ, tendsto (λ i, f (ns i) x) at_top (𝓝 (g x)) :=
begin
  have : ∀ k : ℕ, ∃ N, ∀ n ≥ N, μ {x | 2⁻¹ ^ k < dist (f n x) (g x)} < 2⁻¹ ^ k,
  { sorry, },
  have h_lt_ε_real : ∀ ε : ℝ, ∃ k : ℕ, 2⁻¹ ^ (k + 1) < ε,
  { sorry, },
  let ns := λ k, (this k).some,
  use ns,
  let S := λ k, {x | 2⁻¹ ^ k < dist (f (ns k) x) (g x)},
  have hμS_lt : ∀ k, μ (S k) < 2⁻¹ ^ k,
  { sorry, },
  let s := ⋂ k, ⋃ i (hik : k ≤ i), S i,
  have hμs : μ s = 0,
  { have : ∀ k, s ⊆ ⋃ i (hik : k ≤ i), S i, from λ k, infi_le (λ k, ⋃ i (hik : k ≤ i), S i) k,
    have hμs_le : ∀ k, μ s ≤ ennreal.of_real (2⁻¹ ^ (k + 1)),
    { refine λ k, (measure_mono (this k)).trans ((measure_Union_le _).trans _),
      have hμ_if_eq : ∀ i, μ (⋃ (hik : k ≤ i), S i) = if k ≤ i then μ (S i) else 0,
      sorry,
      rw tsum_congr hμ_if_eq,
      sorry,
       },
    refine le_antisymm _ (zero_le _),
    refine ennreal.le_of_forall_pos_le_add (λ ε hε _, _),
    rw zero_add,
    obtain ⟨k, hk_lt_ε⟩ := h_lt_ε_real ε,
    exact ((hμs_le k).trans (ennreal.of_real_le_of_real hk_lt_ε.le)).trans
      (ennreal.of_real_coe_nnreal).le, },
  have h_tendsto : ∀ x ∈ sᶜ, tendsto (λ i, f (ns i) x) at_top (𝓝 (g x)),
  { refine λ x hx, metric.tendsto_at_top.mpr (λ ε hε, _),
    simp_rw [s, set.compl_Inter, set.compl_Union, set.mem_Union, set.mem_Inter] at hx,
    obtain ⟨N, hNx⟩ := hx,
    obtain ⟨k, hk_lt_ε⟩ := h_lt_ε_real ε,
    refine ⟨max N (k + 1), λ n hn_ge, lt_of_le_of_lt _ hk_lt_ε⟩,
    specialize hNx n ((le_max_left _ _).trans hn_ge),
    have h_inv_n_le_k : (2 : ℝ)⁻¹ ^ n ≤ 2⁻¹ ^ (k + 1),
    { refine pow_le_pow_of_le_one _ _ ((le_max_right _ _).trans hn_ge); norm_num, },
    refine le_trans _ h_inv_n_le_k,
    rwa [set.mem_compl_iff, set.nmem_set_of_eq, not_lt] at hNx, },
  rw ae_iff,
  refine measure_mono_null (λ x, _) hμs,
  rw [set.mem_set_of_eq, ← @not_not (x ∈ s), not_imp_not],
  exact h_tendsto x,
end

end

section

variables [measurable_space E] [normed_group E] [borel_space E] [has_measurable_sub₂ E] {p : ℝ≥0∞}
variables {f : ℕ → α → E} {g : α → E}

/-- Convergence in Lp implies convergence in measure. -/
lemma tendsto_in_measure_of_tendsto_snorm
  (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
  (hf : ∀ n, measurable (f n)) (hg : measurable g)
  (hfg : tendsto (λ n, snorm (f n - g) p μ) at_top (𝓝 0)) :
  tendsto_in_measure μ f g :=
begin
  intros ε hε,
  replace hfg := ennreal.tendsto.const_mul (ennreal.tendsto.rpow p.to_real hfg)
    (or.inr $ @ennreal.of_real_ne_top (1 / ε ^ (p.to_real))),
  simp only [mul_zero, ennreal.zero_rpow_of_pos (ennreal.to_real_pos hp_ne_zero hp_ne_top)] at hfg,
  rw ennreal.tendsto_at_top_zero at hfg ⊢,
  intros δ hδ,
  obtain ⟨N, hN⟩ := hfg δ hδ,
  refine ⟨N, λ n hn, le_trans _ (hN n hn)⟩,
  rw [ennreal.of_real_div_of_pos, ennreal.of_real_one, mul_comm, mul_one_div,
      ennreal.le_div_iff_mul_le, mul_comm],
  { convert mul_meas_ge_le_snorm_pow' μ hp_ne_zero hp_ne_top ((hf n).sub hg)
      (ennreal.of_real ε),
    { exact (ennreal.of_real_rpow_of_pos hε).symm },
    { ext x,
      rw [dist_eq_norm, ← ennreal.of_real_le_of_real_iff (norm_nonneg _),
          of_real_norm_eq_coe_nnnorm] } },
  { refine or.inl _,
    rw [ne, ennreal.of_real_eq_zero, not_le],
    exact real.rpow_pos_of_pos hε _ },
  { exact or.inl (ennreal.of_real_ne_top) },
  { exact real.rpow_pos_of_pos hε _ }
end

end

end measure_theory
