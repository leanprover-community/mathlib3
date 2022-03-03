/-
Copyright (c) 2022 Rémy Degenne, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/

import measure_theory.function.egorov

/-!
# Convergence in measure

We define convergence in measure which is one of the many notions of convergence in probability.
A sequence of functions `f` is said to converge in measure to some function `g`
if for all `ε > 0`, the measure of the set `{x | ε ≤ dist (f i x) (g x)}` tends to 0 as `i`
converges along some given filter `l`.

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
* `measure_theory.tendsto_in_measure.exists_seq_tendsto_ae`: if `f` is a sequence of functions
  which converges in measure to `g`, then `f` has a subsequence which convergence almost
  everywhere to `g`.
* `measure_theory.tendsto_in_measure_of_tendsto_snorm`: convergence in Lp implies convergence
  in measure.
-/

open topological_space filter
open_locale nnreal ennreal measure_theory topological_space

namespace measure_theory

variables {α ι E : Type*} {m : measurable_space α} {μ : measure α}

/-- A sequence of functions `f` is said to converge in measure to some function `g` if for all
`ε > 0`, the measure of the set `{x | ε ≤ dist (f i x) (g x)}` tends to 0 as `i` converges along
some given filter `l`. -/
def tendsto_in_measure [has_dist E] {m : measurable_space α}
  (μ : measure α) (f : ι → α → E) (l : filter ι) (g : α → E) : Prop :=
∀ ε (hε : 0 < ε), tendsto (λ i, μ {x | ε ≤ dist (f i x) (g x)}) l (𝓝 0)

lemma tendsto_in_measure_iff_norm [semi_normed_group E] {l : filter ι}
  {f : ι → α → E} {g : α → E} :
  tendsto_in_measure μ f l g
  ↔ ∀ ε (hε : 0 < ε), tendsto (λ i, μ {x | ε ≤ ∥f i x - g x∥}) l (𝓝 0) :=
by simp_rw [tendsto_in_measure, dist_eq_norm]

namespace tendsto_in_measure

variables [has_dist E] {l : filter ι} {f f' : ι → α → E} {g g' : α → E}

protected lemma congr' (h_left : ∀ᶠ i in l, f i =ᵐ[μ] f' i) (h_right : g =ᵐ[μ] g')
  (h_tendsto : tendsto_in_measure μ f l g) :
  tendsto_in_measure μ f' l g' :=
begin
  intros ε hε,
  suffices : (λ i, μ {x | ε ≤ dist (f' i x) (g' x)})
      =ᶠ[l] (λ i, μ {x | ε ≤ dist (f i x) (g x)}),
  { rw tendsto_congr' this,
    exact h_tendsto ε hε, },
  filter_upwards [h_left] with i h_ae_eq,
  refine measure_congr _,
  filter_upwards [h_ae_eq, h_right] with x hxf hxg,
  rw eq_iff_iff,
  change ε ≤ dist (f' i x) (g' x) ↔ ε ≤ dist (f i x) (g x),
  rw [hxg, hxf],
end

protected lemma congr (h_left : ∀ i, f i =ᵐ[μ] f' i) (h_right : g =ᵐ[μ] g')
  (h_tendsto : tendsto_in_measure μ f l g) :
  tendsto_in_measure μ f' l g' :=
tendsto_in_measure.congr' (eventually_of_forall h_left) h_right h_tendsto

lemma congr_left (h : ∀ i, f i =ᵐ[μ] f' i) (h_tendsto : tendsto_in_measure μ f l g) :
  tendsto_in_measure μ f' l g :=
h_tendsto.congr h (eventually_eq.rfl)

lemma congr_right (h : g =ᵐ[μ] g') (h_tendsto : tendsto_in_measure μ f l g) :
  tendsto_in_measure μ f l g' :=
h_tendsto.congr (λ i, eventually_eq.rfl) h

end tendsto_in_measure

section exists_seq_tendsto_ae

variables [metric_space E]
variables {f : ℕ → α → E} {g : α → E}

/-- Auxiliary lemma for `tendsto_in_measure_of_tendsto_ae`. -/
lemma tendsto_in_measure_of_tendsto_ae_of_measurable
  [measurable_space E] [second_countable_topology E] [borel_space E] [is_finite_measure μ]
  (hf : ∀ n, measurable (f n)) (hg : measurable g)
  (hfg : ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (𝓝 (g x))) :
  tendsto_in_measure μ f at_top g :=
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

/-- Convergence a.e. implies convergence in measure in a finite measure space. -/
lemma tendsto_in_measure_of_tendsto_ae
  [measurable_space E] [second_countable_topology E] [borel_space E] [is_finite_measure μ]
  (hf : ∀ n, ae_measurable (f n) μ) (hfg : ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (𝓝 (g x))) :
  tendsto_in_measure μ f at_top g :=
begin
  have hg : ae_measurable g μ, from ae_measurable_of_tendsto_metric_ae' hf hfg,
  refine tendsto_in_measure.congr (λ i, (hf i).ae_eq_mk.symm) hg.ae_eq_mk.symm _,
  refine tendsto_in_measure_of_tendsto_ae_of_measurable (λ i, (hf i).measurable_mk)
    hg.measurable_mk _,
  have hf_eq_ae : ∀ᵐ x ∂μ, ∀ n, (hf n).mk (f n) x = f n x,
    from ae_all_iff.mpr (λ n, (hf n).ae_eq_mk.symm),
  filter_upwards [hf_eq_ae, hg.ae_eq_mk, hfg] with x hxf hxg hxfg,
  rw [← hxg, funext (λ n, hxf n)],
  exact hxfg,
end

namespace exists_seq_tendsto_ae

lemma exists_nat_measure_lt_two_inv (hfg : tendsto_in_measure μ f at_top g) (n : ℕ) :
  ∃ N, ∀ m ≥ N, μ {x | 2⁻¹ ^ n ≤ dist (f m x) (g x)} ≤ 2⁻¹ ^ n :=
begin
  specialize hfg (2⁻¹ ^ n) (by simp only [zero_lt_bit0, pow_pos, zero_lt_one, inv_pos]),
  rw ennreal.tendsto_at_top_zero at hfg,
  exact hfg (2⁻¹ ^ n) (pos_iff_ne_zero.mpr (λ h_zero, by simpa using pow_eq_zero h_zero))
end

/-- Given a sequence of functions `f` which converges in measure to `g`,
`seq_tendsto_ae_seq_aux` is a sequence such that
`∀ m ≥ seq_tendsto_ae_seq_aux n, μ {x | 2⁻¹ ^ n ≤ dist (f m x) (g x)} ≤ 2⁻¹ ^ n`. -/
noncomputable
def seq_tendsto_ae_seq_aux (hfg : tendsto_in_measure μ f at_top g) (n : ℕ) :=
classical.some (exists_nat_measure_lt_two_inv hfg n)

/-- Transformation of `seq_tendsto_ae_seq_aux` to makes sure it is strictly monotone. -/
noncomputable
def seq_tendsto_ae_seq (hfg : tendsto_in_measure μ f at_top g) : ℕ → ℕ
| 0 := seq_tendsto_ae_seq_aux hfg 0
| (n + 1) := max (seq_tendsto_ae_seq_aux hfg (n + 1))
  (seq_tendsto_ae_seq n + 1)

lemma seq_tendsto_ae_seq_succ (hfg : tendsto_in_measure μ f at_top g) {n : ℕ} :
  seq_tendsto_ae_seq hfg (n + 1) =
  max (seq_tendsto_ae_seq_aux hfg (n + 1)) (seq_tendsto_ae_seq hfg n + 1) :=
by rw seq_tendsto_ae_seq

lemma seq_tendsto_ae_seq_spec (hfg : tendsto_in_measure μ f at_top g)
  (n k : ℕ) (hn : seq_tendsto_ae_seq hfg n ≤ k) :
  μ {x | 2⁻¹ ^ n ≤ dist (f k x) (g x)} ≤ 2⁻¹ ^ n :=
begin
  cases n,
  { exact classical.some_spec (exists_nat_measure_lt_two_inv hfg 0) k hn },
  { exact classical.some_spec (exists_nat_measure_lt_two_inv hfg _) _
      (le_trans (le_max_left _ _) hn) }
end

lemma seq_tendsto_ae_seq_strict_mono (hfg : tendsto_in_measure μ f at_top g) :
  strict_mono (seq_tendsto_ae_seq hfg) :=
begin
  refine strict_mono_nat_of_lt_succ (λ n, _),
  rw seq_tendsto_ae_seq_succ,
  exact lt_of_lt_of_le (lt_add_one $ seq_tendsto_ae_seq hfg n) (le_max_right _ _),
end

end exists_seq_tendsto_ae

/-- If `f` is a sequence of functions which converges in measure to `g`, then there exists a
subsequence of `f` which converges a.e. to `g`. -/
lemma tendsto_in_measure.exists_seq_tendsto_ae
  (hfg : tendsto_in_measure μ f at_top g) :
  ∃ ns : ℕ → ℕ, strict_mono ns ∧ ∀ᵐ x ∂μ, tendsto (λ i, f (ns i) x) at_top (𝓝 (g x)) :=
begin
  /- Since `f` tends to `g` in measure, it has a subsequence `k ↦ f (ns k)` such that
  `μ {|f (ns k) - g| ≥ 2⁻ᵏ} ≤ 2⁻ᵏ` for all `k`. Defining
  `s := ⋂ k, ⋃ i ≥ k, {|f (ns k) - g| ≥ 2⁻ᵏ}`, we see that `μ s = 0` by observing
  `μ s ≤ 2 * 2⁻ᵏ` for all `k`. Indeed, as `s ⊆ ⋃ i ≥ k, {|f (ns k) - g| ≥ 2⁻ᵏ}`,
  `μ s ≤ μ (⋃ i ≥ k, {|f (ns k) - g| ≥ 2⁻ᵏ}) ≤ ∑ i ≥ k, μ {|f (ns k) - g| ≥ 2⁻ᵏ} ≤ ∑ i ≥ k, 2⁻ᵏ`
  which by geometric series equals to `2 * 2⁻ᵏ` as required.

  On the other hand, as `s` is precisely the set for which `f (ns k)`
  doesn't converge to `g`, `f (ns k)` converges almost everywhere to `g` as required. -/
  have h_lt_ε_real : ∀ (ε : ℝ) (hε : 0 < ε), ∃ k : ℕ, 2 * 2⁻¹ ^ k < ε,
  { intros ε hε,
    obtain ⟨k, h_k⟩ : ∃ (k : ℕ), 2⁻¹ ^ k < ε := exists_pow_lt_of_lt_one hε (by norm_num),
    refine ⟨k + 1, (le_of_eq _).trans_lt h_k⟩,
    rw pow_add, ring },
  set ns := exists_seq_tendsto_ae.seq_tendsto_ae_seq hfg,
  use ns,
  let S := λ k, {x | 2⁻¹ ^ k ≤ dist (f (ns k) x) (g x)},
  have hμS_le : ∀ k, μ (S k) ≤ 2⁻¹ ^ k :=
    λ k, exists_seq_tendsto_ae.seq_tendsto_ae_seq_spec hfg k (ns k) (le_rfl),
  let s := ⋂ k, ⋃ i (hik : k ≤ i), S i,
  have hμs : μ s = 0,
  { suffices hμs_le : ∀ k : ℕ, μ s ≤ ennreal.of_real (2 * 2⁻¹ ^ k),
    { refine le_antisymm (ennreal.le_of_forall_pos_le_add (λ ε hε _, _)) (zero_le _),
      rw zero_add,
      obtain ⟨k, hk_lt_ε⟩ := h_lt_ε_real ε hε,
      exact ((hμs_le k).trans (ennreal.of_real_le_of_real hk_lt_ε.le)).trans
        (ennreal.of_real_coe_nnreal).le },
    have : ∀ k, s ⊆ ⋃ i (hik : k ≤ i), S i := λ k, infi_le (λ k, ⋃ i (hik : k ≤ i), S i) k,
    refine λ k, (measure_mono (this k)).trans ((measure_Union_le _).trans _),
    have hμ_if_eq : ∀ i, μ (⋃ (hik : k ≤ i), S i) = if k ≤ i then μ (S i) else 0,
    { intro i, split_ifs; simp only [h, measure_empty, set.Union_true, set.Union_false] },
    rw tsum_congr hμ_if_eq,
    have tsum_le_tsum : ∑' i, ite (k ≤ i) (μ (S i)) 0 ≤ ∑' i, ite (k ≤ i) (2⁻¹ ^ i) 0,
    { refine tsum_le_tsum (λ i, _) ennreal.summable ennreal.summable,
      split_ifs; simp only [hμS_le i, nonpos_iff_eq_zero] },
    refine tsum_le_tsum.trans _,
    suffices tsum_eq_of_real_tsum : ∑' i, ite (k ≤ i) ((2 : ℝ≥0∞)⁻¹ ^ i) 0
      = ennreal.of_real (∑' i, ite (k ≤ i) (2⁻¹ ^ i) 0),
    { rw tsum_eq_of_real_tsum,
      exact ennreal.of_real_le_of_real (tsum_geometric_inv_two_ge k).le },
    rw ennreal.of_real_tsum_of_nonneg,
    { refine tsum_congr (λ i, _),
      split_ifs,
      { rw [ennreal.of_real_pow (inv_nonneg.mpr zero_le_two) i,
        ← ennreal.of_real_inv_of_pos zero_lt_two, ennreal.of_real_bit0 zero_le_one,
        ennreal.of_real_one] },
      { exact ennreal.of_real_zero.symm } },
    { intro n,
      split_ifs,
      { refine pow_nonneg _ _, norm_num },
      { exact le_rfl } },
    { refine summable.summable_of_eq_zero_or_self summable_geometric_two (λ i, _),
      simp only [one_div, inv_eq_zero, not_le, inv_pow₀, zero_eq_inv],
      exact (ite_eq_or_eq _ _ _).symm } },
  have h_tendsto : ∀ x ∈ sᶜ, tendsto (λ i, f (ns i) x) at_top (𝓝 (g x)),
  { refine λ x hx, metric.tendsto_at_top.mpr (λ ε hε, _),
    simp_rw [s, set.compl_Inter, set.compl_Union, set.mem_Union, set.mem_Inter] at hx,
    obtain ⟨N, hNx⟩ := hx,
    obtain ⟨k, hk_lt_ε⟩ := h_lt_ε_real ε hε,
    refine ⟨max N (k - 1), λ n hn_ge, lt_of_le_of_lt _ hk_lt_ε⟩,
    specialize hNx n ((le_max_left _ _).trans hn_ge),
    have h_inv_n_le_k : (2 : ℝ)⁻¹ ^ n ≤ 2 * 2⁻¹ ^ k,
    { rw [mul_comm, ← inv_mul_le_iff' (@two_pos ℝ _ _)],
      conv_lhs { congr, rw ← pow_one (2 : ℝ)⁻¹ },
      rw [← pow_add, add_comm],
      exact pow_le_pow_of_le_one ((one_div (2 : ℝ)) ▸ one_half_pos.le) (inv_le_one one_le_two)
        ((le_tsub_add.trans (add_le_add_right (le_max_right _ _) 1)).trans
        (add_le_add_right hn_ge 1)) },
    refine le_trans _ h_inv_n_le_k,
    rw [set.mem_compl_iff, set.nmem_set_of_eq, not_le] at hNx,
    exact hNx.le },
  rw ae_iff,
  refine ⟨exists_seq_tendsto_ae.seq_tendsto_ae_seq_strict_mono hfg,
    measure_mono_null (λ x, _) hμs⟩,
  rw [set.mem_set_of_eq, ← @not_not (x ∈ s), not_imp_not],
  exact h_tendsto x,
end

lemma tendsto_in_measure.exists_seq_tendsto_in_measure_at_top
  {u : filter ι} [ne_bot u] [is_countably_generated u] {f : ι → α → E} {g : α → E}
  (hfg : tendsto_in_measure μ f u g) :
  ∃ ns : ℕ → ι, tendsto_in_measure μ (λ n, f (ns n)) at_top g :=
begin
  obtain ⟨ns, h_tendsto_ns⟩ : ∃ (ns : ℕ → ι), tendsto ns at_top u := exists_seq_tendsto u,
  exact ⟨ns, λ ε hε, (hfg ε hε).comp h_tendsto_ns⟩,
end

lemma tendsto_in_measure.exists_seq_tendsto_ae'
  {u : filter ι} [ne_bot u] [is_countably_generated u] {f : ι → α → E} {g : α → E}
  (hfg : tendsto_in_measure μ f u g) :
  ∃ ns : ℕ → ι, ∀ᵐ x ∂μ, tendsto (λ i, f (ns i) x) at_top (𝓝 (g x)) :=
begin
  obtain ⟨ms, hms⟩ := hfg.exists_seq_tendsto_in_measure_at_top,
  obtain ⟨ns, -, hns⟩ := hms.exists_seq_tendsto_ae,
  exact ⟨ms ∘ ns, hns⟩,
end

end exists_seq_tendsto_ae

section ae_measurable_of

variables [measurable_space E] [normed_group E] [borel_space E]

lemma tendsto_in_measure.ae_measurable
  {u : filter ι} [ne_bot u] [is_countably_generated u]
  {f : ι → α → E} {g : α → E} (hf : ∀ n, ae_measurable (f n) μ)
  (h_tendsto : tendsto_in_measure μ f u g) :
  ae_measurable g μ :=
begin
  obtain ⟨ns, hns⟩ := h_tendsto.exists_seq_tendsto_ae',
  exact ae_measurable_of_tendsto_metric_ae at_top (λ n, hf (ns n)) hns,
end

end ae_measurable_of

section tendsto_in_measure_of

variables [measurable_space E] [normed_group E] [borel_space E] [has_measurable_sub₂ E] {p : ℝ≥0∞}
variables {f : ι → α → E} {g : α → E}

/-- This lemma is superceded by `measure_theory.tendsto_in_measure_of_tendsto_snorm` where we
allow `p = ∞` and only require `ae_measurable`. -/
lemma tendsto_in_measure_of_tendsto_snorm_of_measurable
  (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
  (hf : ∀ n, measurable (f n)) (hg : measurable g) {l : filter ι}
  (hfg : tendsto (λ n, snorm (f n - g) p μ) l (𝓝 0)) :
  tendsto_in_measure μ f l g :=
begin
  intros ε hε,
  replace hfg := ennreal.tendsto.const_mul (tendsto.ennrpow_const p.to_real hfg)
    (or.inr $ @ennreal.of_real_ne_top (1 / ε ^ (p.to_real))),
  simp only [mul_zero, ennreal.zero_rpow_of_pos (ennreal.to_real_pos hp_ne_zero hp_ne_top)] at hfg,
  rw ennreal.tendsto_nhds_zero at hfg ⊢,
  intros δ hδ,
  refine (hfg δ hδ).mono (λ n hn, _),
  refine le_trans _ hn,
  rw [ennreal.of_real_div_of_pos (real.rpow_pos_of_pos hε _), ennreal.of_real_one, mul_comm,
    mul_one_div, ennreal.le_div_iff_mul_le _ (or.inl (ennreal.of_real_ne_top)), mul_comm],
  { convert mul_meas_ge_le_pow_snorm' μ hp_ne_zero hp_ne_top ((hf n).sub hg) (ennreal.of_real ε),
    { exact (ennreal.of_real_rpow_of_pos hε).symm },
    { ext x,
      rw [dist_eq_norm, ← ennreal.of_real_le_of_real_iff (norm_nonneg _),
          of_real_norm_eq_coe_nnnorm] } },
  { rw [ne, ennreal.of_real_eq_zero, not_le],
    exact or.inl (real.rpow_pos_of_pos hε _) },
end

/-- This lemma is superceded by `measure_theory.tendsto_in_measure_of_tendsto_snorm` where we
allow `p = ∞`. -/
lemma tendsto_in_measure_of_tendsto_snorm_of_ne_top
  (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
  (hf : ∀ n, ae_measurable (f n) μ) (hg : ae_measurable g μ) {l : filter ι}
  (hfg : tendsto (λ n, snorm (f n - g) p μ) l (𝓝 0)) :
  tendsto_in_measure μ f l g :=
begin
  refine tendsto_in_measure.congr (λ i, (hf i).ae_eq_mk.symm) hg.ae_eq_mk.symm _,
  refine tendsto_in_measure_of_tendsto_snorm_of_measurable hp_ne_zero hp_ne_top
    (λ i, (hf i).measurable_mk) hg.measurable_mk _,
  have : (λ n, snorm ((hf n).mk (f n) - ae_measurable.mk g hg) p μ) = (λ n, snorm (f n - g) p μ),
  { ext1 n, refine snorm_congr_ae (eventually_eq.sub (hf n).ae_eq_mk.symm hg.ae_eq_mk.symm), },
  rw this,
  exact hfg,
end

/-- See also `measure_theory.tendsto_in_measure_of_tendsto_snorm` which work for general
Lp-convergence for all `p ≠ 0`. -/
lemma tendsto_in_measure_of_tendsto_snorm_top {E} [normed_group E] {f : ι → α → E} {g : α → E}
  {l : filter ι} (hfg : tendsto (λ n, snorm (f n - g) ∞ μ) l (𝓝 0)) :
  tendsto_in_measure μ f l g :=
begin
  intros δ hδ,
  simp only [snorm_exponent_top, snorm_ess_sup] at hfg,
  rw ennreal.tendsto_nhds_zero at hfg ⊢,
  intros ε hε,
  specialize hfg ((ennreal.of_real δ) / 2) (ennreal.div_pos_iff.2
    ⟨(ennreal.of_real_pos.2 hδ).ne.symm, ennreal.two_ne_top⟩),
  refine hfg.mono (λ n hn, _),
  simp only [true_and, gt_iff_lt, ge_iff_le, zero_tsub, zero_le, zero_add, set.mem_Icc,
    pi.sub_apply] at *,
  have : ess_sup (λ (x : α), (∥f n x - g x∥₊ : ℝ≥0∞)) μ < ennreal.of_real δ :=
    lt_of_le_of_lt hn (ennreal.half_lt_self (ennreal.of_real_pos.2 hδ).ne.symm
      ennreal.of_real_lt_top.ne),
  refine ((le_of_eq _).trans (ae_lt_of_ess_sup_lt this).le).trans hε.le,
  congr' with x,
  simp only [ennreal.of_real_le_iff_le_to_real ennreal.coe_lt_top.ne, ennreal.coe_to_real,
    not_lt, coe_nnnorm, set.mem_set_of_eq, set.mem_compl_eq],
  rw ← dist_eq_norm (f n x) (g x),
  refl
end

/-- Convergence in Lp implies convergence in measure. -/
lemma tendsto_in_measure_of_tendsto_snorm
  (hp_ne_zero : p ≠ 0) (hf : ∀ n, ae_measurable (f n) μ) (hg : ae_measurable g μ) {l : filter ι}
  (hfg : tendsto (λ n, snorm (f n - g) p μ) l (𝓝 0)) :
  tendsto_in_measure μ f l g :=
begin
  by_cases hp_ne_top : p = ∞,
  { subst hp_ne_top,
    exact tendsto_in_measure_of_tendsto_snorm_top hfg },
  { exact tendsto_in_measure_of_tendsto_snorm_of_ne_top hp_ne_zero hp_ne_top hf hg hfg }
end

/-- Convergence in Lp implies convergence in measure. -/
lemma tendsto_in_measure_of_tendsto_Lp [second_countable_topology E] [hp : fact (1 ≤ p)]
  {f : ι → Lp E p μ} {g : Lp E p μ} {l : filter ι} (hfg : tendsto f l (𝓝 g)) :
  tendsto_in_measure μ (λ n, f n) l g :=
tendsto_in_measure_of_tendsto_snorm (ennreal.zero_lt_one.trans_le hp.elim).ne.symm
  (λ n, Lp.ae_measurable _) (Lp.ae_measurable _) ((Lp.tendsto_Lp_iff_tendsto_ℒp' _ _).mp hfg)

end tendsto_in_measure_of

end measure_theory
