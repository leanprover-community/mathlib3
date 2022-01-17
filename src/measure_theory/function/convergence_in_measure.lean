/-
Copyright (c) 2022 Rémy Degenne, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/

import measure_theory.function.uniform_integrable

/-!
# Convergence in measure

We define convergence in measure which is one of the many notions of convergence in probability.
Convergence in measure is most notably used in the formulation of the weak law of large numbers
and is also useful in theorems such as the Vitali convergence theorem. This file provides some
basic lemmas for working with convergence in measure and establishes some relations between
convergence in measure and other notions of convergence.

## Main definitions

* `measure_theory.tendsto_in_measure (μ : measure α) (f : ι → α → E) (g : α → E)`: `f` converges
  in `μ`-measure to `g`.

## Main results

* `measure_theory.tendsto_in_measure_of_tendsto_ae`: convergence almost everywhere in a finite
  measure space implies convergence in measure.
* `measure_theory.tendsto_in_measure.exists_seq_tendsto_ae`: in a finite measure space, `f`
  converges in measure to `g` implies `f` has a subsequence which convergence almost everywhere
  to `g`.
* `measure_theory.tendsto_in_measure_of_tendsto_snorm`: convergence in Lp implies convergence
  in measure.
-/

open topological_space filter
open_locale nnreal ennreal measure_theory topological_space

namespace measure_theory

variables {α ι E : Type*} {m : measurable_space α} {μ : measure α}

/-- A sequence of functions `f` is said to converge in measure to some function `g` if for all
`ε > 0`, the measure of the set `{x | ε ≤ dist (f i x) (g x)}` tends to 0 as `i` tends to
infinity. -/
def tendsto_in_measure [preorder ι] [has_dist E] {m : measurable_space α}
  (μ : measure α) (f : ι → α → E) (g : α → E) : Prop :=
∀ ε (hε : 0 < ε), tendsto (λ i, μ {x | ε ≤ dist (f i x) (g x)}) at_top (𝓝 0)

section Lp
-- PRed: #11478
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

lemma tendsto_in_measure.exists_seq_tendsto_ae (hf : ∀ n, measurable (f n)) (hg : measurable g)
  (hfg : tendsto_in_measure μ f g) :
  ∃ ns : ℕ → ℕ, ∀ᵐ x ∂μ, tendsto (λ i, f (ns i) x) at_top (𝓝 (g x)) :=
begin
  have : ∀ k : ℕ, ∃ N, ∀ n ≥ N, μ {x | 2⁻¹ ^ k ≤ dist (f n x) (g x)} ≤ 2⁻¹ ^ k,
  { intro k,
    have h_pos : 0 < (2 : ℝ)⁻¹ ^ k, by simp only [zero_lt_bit0, pow_pos, zero_lt_one, inv_pos],
    specialize hfg (2⁻¹ ^ k) h_pos,
    rw ennreal.tendsto_at_top_zero at hfg,
    refine hfg (2⁻¹ ^ k) _,
    exact pos_iff_ne_zero.mpr (λ h_zero, by simpa using pow_eq_zero h_zero), },
  have h_lt_ε_real : ∀ (ε : ℝ) (hε : 0 < ε), ∃ k : ℕ, 2⁻¹ ^ (k - 1) < ε,
  { intros ε hε,
    obtain ⟨k, h_k⟩ : ∃ (k : ℕ), 2⁻¹ ^ k < ε, from exists_pow_lt_of_lt_one hε (by norm_num),
    refine ⟨k+1, lt_of_le_of_lt (le_of_eq _) h_k⟩,
    rw [nat.add_succ_sub_one, add_zero], },
  let ns := λ k, (this k).some,
  use ns,
  let S := λ k, {x | 2⁻¹ ^ k ≤ dist (f (ns k) x) (g x)},
  have hμS_le : ∀ k, μ (S k) ≤ 2⁻¹ ^ k,
  { have h_ns_k : ∀ k, ∀ n, n ≥ ns k → μ {x | 2⁻¹ ^ k ≤ dist (f n x) (g x)} ≤ 2⁻¹ ^ k,
      from λ k, (this k).some_spec,
    exact λ k, h_ns_k k (ns k) (le_rfl), },
  let s := ⋂ k, ⋃ i (hik : k ≤ i), S i,
  have hμs : μ s = 0,
  { have : ∀ k, s ⊆ ⋃ i (hik : k ≤ i), S i, from λ k, infi_le (λ k, ⋃ i (hik : k ≤ i), S i) k,
    have hμs_le : ∀ k, μ s ≤ ennreal.of_real (2⁻¹ ^ (k - 1)),
    { refine λ k, (measure_mono (this k)).trans ((measure_Union_le _).trans _),
      have hμ_if_eq : ∀ i, μ (⋃ (hik : k ≤ i), S i) = if k ≤ i then μ (S i) else 0,
      { intro i, split_ifs; simp only [h, measure_empty, set.Union_true, set.Union_false], },
      rw tsum_congr hμ_if_eq,
      dsimp only,
      have tsum_le_tsum : ∑' i, ite (k ≤ i) (μ (S i)) 0
        ≤ ∑' i, ite (k ≤ i) (2⁻¹ ^ i) 0,
      { refine tsum_le_tsum (λ i, _) ennreal.summable ennreal.summable,
        split_ifs; simp only [hμS_le i, nonpos_iff_eq_zero], },
      refine tsum_le_tsum.trans _,
      have tsum_eq_of_real_tsum : ∑' i, ite (k ≤ i) ((2 : ℝ≥0∞)⁻¹ ^ i) 0
        = ennreal.of_real (∑' i, ite (k ≤ i) (2⁻¹ ^ i) 0),
      { rw ennreal.of_real_tsum_of_nonneg,
        swap, { intro n,
          split_ifs,
          { refine pow_nonneg _ _, norm_num, },
          { exact le_rfl, }, },
        swap, { refine summable.summable_of_eq_zero_or_self summable_geometric_two (λ i, _),
          split_ifs,
          { simp only [one_div, eq_self_iff_true, or_true], },
          { exact or.inl rfl, }, },
        refine tsum_congr (λ i, _),
        split_ifs,
        swap, simp only [ennreal.of_real_zero],
        rw [ennreal.of_real_pow (inv_nonneg.mpr zero_le_two) i,
          ← ennreal.of_real_inv_of_pos zero_lt_two, ennreal.of_real_bit0 zero_le_one,
          ennreal.of_real_one], },
      rw tsum_eq_of_real_tsum,
      refine ennreal.of_real_le_of_real (le_of_eq _),
      sorry, },
    refine le_antisymm _ (zero_le _),
    refine ennreal.le_of_forall_pos_le_add (λ ε hε _, _),
    rw zero_add,
    obtain ⟨k, hk_lt_ε⟩ := h_lt_ε_real ε hε,
    exact ((hμs_le k).trans (ennreal.of_real_le_of_real hk_lt_ε.le)).trans
      (ennreal.of_real_coe_nnreal).le, },
  have h_tendsto : ∀ x ∈ sᶜ, tendsto (λ i, f (ns i) x) at_top (𝓝 (g x)),
  { refine λ x hx, metric.tendsto_at_top.mpr (λ ε hε, _),
    simp_rw [s, set.compl_Inter, set.compl_Union, set.mem_Union, set.mem_Inter] at hx,
    obtain ⟨N, hNx⟩ := hx,
    obtain ⟨k, hk_lt_ε⟩ := h_lt_ε_real ε hε,
    refine ⟨max N (k - 1), λ n hn_ge, lt_of_le_of_lt _ hk_lt_ε⟩,
    specialize hNx n ((le_max_left _ _).trans hn_ge),
    have h_inv_n_le_k : (2 : ℝ)⁻¹ ^ n ≤ 2⁻¹ ^ (k - 1),
    { refine pow_le_pow_of_le_one _ _ ((le_max_right _ _).trans hn_ge); norm_num, },
    refine le_trans _ h_inv_n_le_k,
    rw [set.mem_compl_iff, set.nmem_set_of_eq, not_le] at hNx,
    exact hNx.le, },
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
  replace hfg := ennreal.tendsto.const_mul (tendsto.ennrpow_const p.to_real hfg)
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
