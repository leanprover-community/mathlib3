/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import measure_theory.integral.set_integral

/-!
# Uniform integrability

This file will be used in the future to define uniform integrability. Uniform integrability
is an important notion in both measure theory as well as probability theory. So far this file
only contains the Egorov theorem which will be used to prove the Vitali convergence theorem
which is one of the main results about uniform integrability.

## Main results

* `measure_theory.egorov`: Egorov's theorem which shows that a sequence of almost everywhere
  convergent functions converges uniformly except on an arbitrarily small set.

-/

noncomputable theory
open_locale classical measure_theory nnreal ennreal topological_space

namespace measure_theory

open set filter topological_space

variables {α β ι : Type*} {m : measurable_space α} {μ : measure α}

section

variables [metric_space β]

/-! We will in this section prove Egorov's theorem. -/

namespace egorov

/-- Given a sequence of functions `f` and a function `g`, `not_convergent_seq f g i j` is the
set of elements such that `f k x` and `g x` are separated by at least `1 / (i + 1)` for some
`k ≥ j`.

This definition is useful for Egorov's theorem. -/
def not_convergent_seq (f : ℕ → α → β) (g : α → β) (i j : ℕ) : set α :=
⋃ k (hk : j ≤ k), {x | (1 / (i + 1 : ℝ)) < dist (f k x) (g x)}

variables {i j : ℕ} {s : set α} {ε : ℝ} {f : ℕ → α → β} {g : α → β}

lemma mem_not_convergent_seq_iff {x : α} : x ∈ not_convergent_seq f g i j ↔
  ∃ k (hk : j ≤ k), (1 / (i + 1 : ℝ)) < dist (f k x) (g x) :=
by { simp_rw [not_convergent_seq, mem_Union], refl }

lemma not_convergent_seq_antitone :
  antitone (not_convergent_seq f g i) :=
λ j k hjk, Union₂_mono' $ λ l hl, ⟨l, le_trans hjk hl, subset.rfl⟩

lemma measure_inter_not_convergent_seq_eq_zero
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) (i : ℕ) :
  μ (s ∩ ⋂ j, not_convergent_seq f g i j) = 0 :=
begin
  simp_rw [metric.tendsto_at_top, ae_iff] at hfg,
  rw [← nonpos_iff_eq_zero, ← hfg],
  refine measure_mono (λ x, _),
  simp only [mem_inter_eq, mem_Inter, ge_iff_le, mem_not_convergent_seq_iff],
  push_neg,
  rintro ⟨hmem, hx⟩,
  refine ⟨hmem, 1 / (i + 1 : ℝ), nat.one_div_pos_of_nat, λ N, _⟩,
  obtain ⟨n, hn₁, hn₂⟩ := hx N,
  exact ⟨n, hn₁, hn₂.le⟩
end

variables [second_countable_topology β] [measurable_space β] [borel_space β]

lemma not_convergent_seq_measurable_set
  (hf : ∀ n, measurable[m] (f n)) (hg : measurable g) :
  measurable_set (not_convergent_seq f g i j) :=
measurable_set.Union (λ k, measurable_set.Union_Prop $ λ hk,
  measurable_set_lt measurable_const $ (hf k).dist hg)

lemma measure_not_convergent_seq_tendsto_zero
  (hf : ∀ n, measurable (f n)) (hg : measurable g) (hsm : measurable_set s) (hs : μ s ≠ ∞)
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) (i : ℕ) :
  tendsto (λ j, μ (s ∩ not_convergent_seq f g i j)) at_top (𝓝 0) :=
begin
  rw [← measure_inter_not_convergent_seq_eq_zero hfg, inter_Inter],
  exact tendsto_measure_Inter (λ n, hsm.inter $ not_convergent_seq_measurable_set hf hg)
    (λ k l hkl, inter_subset_inter_right _ $ not_convergent_seq_antitone hkl)
    ⟨0, (lt_of_le_of_lt (measure_mono $ inter_subset_left _ _) (lt_top_iff_ne_top.2 hs)).ne⟩
end

lemma exists_not_convergent_seq_lt (hε : 0 < ε)
  (hf : ∀ n, measurable (f n)) (hg : measurable g) (hsm : measurable_set s) (hs : μ s ≠ ∞)
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) (i : ℕ) :
  ∃ j : ℕ, μ (s ∩ not_convergent_seq f g i j) ≤ ennreal.of_real (ε * 2⁻¹ ^ i) :=
begin
  obtain ⟨N, hN⟩ := (ennreal.tendsto_at_top ennreal.zero_ne_top).1
    (measure_not_convergent_seq_tendsto_zero hf hg hsm hs hfg i)
    (ennreal.of_real (ε * 2⁻¹ ^ i)) _,
  { rw zero_add at hN,
    exact ⟨N, (hN N le_rfl).2⟩ },
  { rw [gt_iff_lt, ennreal.of_real_pos],
    exact mul_pos hε (pow_pos (by norm_num) _) }
end

/-- Given some `ε > 0`, `not_convergent_seq_lt_index` provides the index such that
`not_convergent_seq` (intersected with a set of finite measure) has measure less than
`ε * 2⁻¹ ^ i`.

This definition is useful for Egorov's theorem. -/
def not_convergent_seq_lt_index (hε : 0 < ε)
  (hf : ∀ n, measurable (f n)) (hg : measurable g) (hsm : measurable_set s) (hs : μ s ≠ ∞)
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) (i : ℕ) : ℕ :=
classical.some $ exists_not_convergent_seq_lt hε hf hg hsm hs hfg i

lemma not_convergent_seq_lt_index_spec (hε : 0 < ε)
  (hf : ∀ n, measurable (f n)) (hg : measurable g) (hsm : measurable_set s) (hs : μ s ≠ ∞)
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) (i : ℕ) :
  μ (s ∩ not_convergent_seq f g i (not_convergent_seq_lt_index hε hf hg hsm hs hfg i)) ≤
  ennreal.of_real (ε * 2⁻¹ ^ i) :=
classical.some_spec $ exists_not_convergent_seq_lt hε hf hg hsm hs hfg i

/-- Given some `ε > 0`, `Union_not_convergent_seq` is the union of `not_convergent_seq` with
specific indicies such that `Union_not_convergent_seq` has measure less equal than `ε`.

This definition is useful for Egorov's theorem. -/
def Union_not_convergent_seq (hε : 0 < ε)
  (hf : ∀ n, measurable (f n)) (hg : measurable g) (hsm : measurable_set s) (hs : μ s ≠ ∞)
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) : set α :=
⋃ i, s ∩ not_convergent_seq f g i (not_convergent_seq_lt_index (half_pos hε) hf hg hsm hs hfg i)

lemma Union_not_convergent_seq_measurable_set (hε : 0 < ε)
  (hf : ∀ n, measurable (f n)) (hg : measurable g) (hsm : measurable_set s) (hs : μ s ≠ ∞)
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) :
  measurable_set $ Union_not_convergent_seq hε hf hg hsm hs hfg :=
measurable_set.Union (λ n, hsm.inter $ not_convergent_seq_measurable_set hf hg)

lemma measure_Union_not_convergent_seq (hε : 0 < ε)
  (hf : ∀ n, measurable (f n)) (hg : measurable g) (hsm : measurable_set s) (hs : μ s ≠ ∞)
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) :
  μ (Union_not_convergent_seq hε hf hg hsm hs hfg) ≤ ennreal.of_real ε :=
begin
  refine le_trans (measure_Union_le _)
    (le_trans (ennreal.tsum_le_tsum $ not_convergent_seq_lt_index_spec
    (half_pos hε) hf hg hsm hs hfg) _),
  simp_rw [ennreal.of_real_mul (half_pos hε).le],
  rw [ennreal.tsum_mul_left, ← ennreal.of_real_tsum_of_nonneg, inv_eq_one_div,
      tsum_geometric_two, ← ennreal.of_real_mul (half_pos hε).le, div_mul_cancel ε two_ne_zero],
  { exact le_rfl },
  { exact λ n, pow_nonneg (by norm_num) _ },
  { rw [inv_eq_one_div],
    exact summable_geometric_two },
end

lemma Union_not_convergent_seq_subset (hε : 0 < ε)
  (hf : ∀ n, measurable (f n)) (hg : measurable g) (hsm : measurable_set s) (hs : μ s ≠ ∞)
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) :
  Union_not_convergent_seq hε hf hg hsm hs hfg ⊆ s :=
begin
  rw [Union_not_convergent_seq, ← inter_Union],
  exact inter_subset_left _ _,
end

lemma tendsto_uniformly_on_diff_Union_not_convergent_seq (hε : 0 < ε)
  (hf : ∀ n, measurable (f n)) (hg : measurable g) (hsm : measurable_set s) (hs : μ s ≠ ∞)
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) :
  tendsto_uniformly_on f g at_top (s \ egorov.Union_not_convergent_seq hε hf hg hsm hs hfg) :=
begin
  rw metric.tendsto_uniformly_on_iff,
  intros δ hδ,
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ,
  rw eventually_at_top,
  refine ⟨egorov.not_convergent_seq_lt_index (half_pos hε) hf hg hsm hs hfg N, λ n hn x hx, _⟩,
  simp only [mem_diff, egorov.Union_not_convergent_seq, not_exists, mem_Union, mem_inter_eq,
    not_and, exists_and_distrib_left] at hx,
  obtain ⟨hxs, hx⟩ := hx,
  specialize hx hxs N,
  rw egorov.mem_not_convergent_seq_iff at hx,
  push_neg at hx,
  rw dist_comm,
  exact lt_of_le_of_lt (hx n hn) hN,
end

end egorov

variables [second_countable_topology β] [measurable_space β] [borel_space β]
  {f : ℕ → α → β} {g : α → β} {s : set α}


/-- **Egorov's theorem**: If `f : ℕ → α → β` is a sequence of measurable functions that converges
to `g : α → β` almost everywhere on a measurable set `s` of finite measure, then for all `ε > 0`,
there exists a subset `t ⊆ s` such that `μ t ≤ ε` and `f` converges to `g` uniformly on `s \ t`.

In other words, a sequence of almost everywhere convergent functions converges uniformly except on
an arbitrarily small set. -/
theorem tendsto_uniformly_on_of_ae_tendsto
  (hf : ∀ n, measurable (f n)) (hg : measurable g) (hsm : measurable_set s) (hs : μ s ≠ ∞)
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) {ε : ℝ} (hε : 0 < ε) :
  ∃ t ⊆ s, measurable_set t ∧ μ t ≤ ennreal.of_real ε ∧ tendsto_uniformly_on f g at_top (s \ t) :=
⟨egorov.Union_not_convergent_seq hε hf hg hsm hs hfg,
 egorov.Union_not_convergent_seq_subset hε hf hg hsm hs hfg,
 egorov.Union_not_convergent_seq_measurable_set hε hf hg hsm hs hfg,
 egorov.measure_Union_not_convergent_seq hε hf hg hsm hs hfg,
 egorov.tendsto_uniformly_on_diff_Union_not_convergent_seq hε hf hg hsm hs hfg⟩

/-- Egorov's theorem for finite measure spaces. -/
lemma tendsto_uniformly_on_of_ae_tendsto' [is_finite_measure μ]
  (hf : ∀ n, measurable (f n)) (hg : measurable g)
  (hfg : ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (𝓝 (g x))) {ε : ℝ} (hε : 0 < ε) :
  ∃ t, measurable_set t ∧ μ t ≤ ennreal.of_real ε ∧ tendsto_uniformly_on f g at_top tᶜ :=
begin
  obtain ⟨t, _, ht, htendsto⟩ :=
    tendsto_uniformly_on_of_ae_tendsto hf hg measurable_set.univ (measure_ne_top μ univ) _ hε,
  { refine ⟨_, ht, _⟩,
    rwa compl_eq_univ_diff },
  { filter_upwards [hfg] with _ htendsto _ using htendsto, },
end

end

variables [measurable_space β] [normed_group β]

/-- Also known as uniformly absolutely continuous integrals. -/
def unif_integrable {m : measurable_space α} (f : ι → α → β) (p : ℝ≥0∞) (μ : measure α) : Prop :=
∀ ⦃ε : ℝ⦄ (hε : 0 < ε), ∃ (δ : ℝ) (hδ : 0 < δ), ∀ i s, measurable_set s → μ s ≤ ennreal.of_real δ →
snorm (s.indicator (f i)) p μ < ennreal.of_real ε

section unif_integrable

variables [borel_space β] [second_countable_topology β] [is_finite_measure μ] {p : ℝ≥0∞}
-- useful lemmas:
-- #check snorm_ess_sup_lt_top_of_ae_bound
-- #check snorm_le_of_ae_bound

lemma mem_ℒp.snorm_lt_measure {f : α → β} (hf : mem_ℒp f p μ) {ε : ℝ} (hε : 0 < ε) :
  ∃ (δ : ℝ) (hδ : 0 < δ), ∀ s, measurable_set s → μ s ≤ ennreal.of_real δ →
  snorm (s.indicator f) p μ < ennreal.of_real ε :=
begin
  sorry
end

lemma unif_integrable_subsingleton [subsingleton ι] {f : ι → α → β} (hf : ∀ i, mem_ℒp (f i) p μ) :
  unif_integrable f p μ :=
begin
  sorry
end

lemma unif_integrable_finite [fintype ι] {f : ι → α → β} (hf : ∀ i, mem_ℒp (f i) p μ) :
  unif_integrable f p μ :=
begin
  sorry
end

lemma snorm_sub_le_of_dist_bdd (μ : measure α) [is_finite_measure μ]
  {p : ℝ≥0∞} (hp : p ≠ 0) (hp' : p ≠ ∞) {s : set α} (hs : measurable_set[m] s)
  {f g : α → β} {c : ℝ} (hc : 0 ≤ c) (hf : ∀ x ∈ s, dist (f x) (g x) ≤ c) :
  snorm (s.indicator (f - g)) p μ ≤ ennreal.of_real c * μ s ^ (1 / p.to_real) :=
begin
  have : ∀ x, ∥s.indicator (f - g) x∥ ≤ ∥s.indicator (λ x, c) x∥,
  { intro x,
    by_cases hx : x ∈ s,
    { rw [indicator_of_mem hx, indicator_of_mem hx, pi.sub_apply, ← dist_eq_norm,
          real.norm_eq_abs, abs_of_nonneg hc],
      exact hf x hx },
    { simp [indicator_of_not_mem hx] } },
  refine le_trans (snorm_mono this) _,
  rw snorm_indicator_const hs hp hp',
  by_cases hμs : μ s = 0,
  { rw [hμs, ennreal.zero_rpow_of_pos, mul_zero, mul_zero],
    { exact le_rfl },
    { rw one_div_pos,
      exact ennreal.to_real_pos hp hp' } },
  { rw [ennreal.mul_le_mul_right, real.nnnorm_of_nonneg hc, ennreal.coe_nnreal_eq],
    { exact le_rfl },
    { intro h,
      obtain (h' | h') := ennreal.rpow_eq_zero_iff.1 h,
      { exact hμs h'.1 },
      { exact (measure_lt_top μ s).ne h'.1 } },
    { intro h,
      obtain (h' | h') := ennreal.rpow_eq_top_iff.1 h,
      { exact hμs h'.1 },
      { exact (measure_lt_top μ s).ne h'.1 } } }
end

-- We can remove the measurability assumption so this lemma should be private once we have
-- generalized it

-- To generalize the below to convergence in measure we need that convergence in measure implies
-- existence of convergent a.e. subsequence

/-- A sequence of uniformly integrable functions which converges μ-a.e. converges in Lp. -/
lemma tendsto_Lp_of_unif_integrable (hp : 1 ≤ p) (hp' : p ≠ ∞) {f : ℕ → α → β} {g : α → β}
  (hf : ∀ n, measurable[m] (f n)) (hg : measurable g)
  (hg' : mem_ℒp g p μ) (hui : unif_integrable f p μ)
  (hfg : ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (𝓝 (g x))) :
  tendsto (λ n, snorm (f n - g) p μ) at_top (𝓝 0) :=
begin
  rw ennreal.tendsto_at_top ennreal.zero_ne_top,
  swap, apply_instance,
  intros ε hε,
  by_cases ε < ∞,
  { by_cases hμ : μ = 0,
    { exact ⟨0, λ n hn, by simp [hμ]⟩ },
    have hε' : 0 < ε.to_real / 3 :=
      div_pos (ennreal.to_real_pos (gt_iff_lt.1 hε).ne.symm h.ne) (by norm_num),
    have hdivp : 0 ≤ 1 / p.to_real,
    { refine one_div_nonneg.2 _,
      rw [← ennreal.zero_to_real, ennreal.to_real_le_to_real ennreal.zero_ne_top hp'],
      exact le_trans ennreal.zero_lt_one.le hp },
    have hpow : 0 < (measure_univ_nnreal μ) ^ (1 / p.to_real) :=
      real.rpow_pos_of_pos (measure_univ_nnreal_pos hμ) _,
    obtain ⟨δ₁, hδ₁, hsnorm₁⟩ := hui hε',
    obtain ⟨δ₂, hδ₂, hsnorm₂⟩ := hg'.snorm_lt_measure hε',
    obtain ⟨t, htm, ht₁, ht₂⟩ := tendsto_uniformly_on_of_ae_tendsto' hf hg hfg (lt_min hδ₁ hδ₂),
    rw metric.tendsto_uniformly_on_iff at ht₂,
    specialize ht₂ (ε.to_real / (3 * measure_univ_nnreal μ ^ (1 / p.to_real)))
      (div_pos (ennreal.to_real_pos (gt_iff_lt.1 hε).ne.symm h.ne) (mul_pos (by norm_num) hpow)),
    obtain ⟨N, hN⟩ := eventually_at_top.1 ht₂, clear ht₂,
    refine ⟨N, λ n hn, _⟩,
    simp only [mem_Icc, true_and, zero_tsub, zero_le, zero_add],
    rw [← t.indicator_self_add_compl (f n - g)],
    refine le_trans (snorm_add_le ((((hf n).sub hg).indicator htm).ae_measurable)
      (((hf n).sub hg).indicator htm.compl).ae_measurable hp) _,
    rw [sub_eq_add_neg, indicator_add' t, indicator_neg'],
    refine le_trans (add_le_add_right (snorm_add_le ((hf n).indicator htm).ae_measurable
      (hg.indicator htm).neg.ae_measurable hp) _) _,
    have hnf : snorm (t.indicator (f n)) p μ < ennreal.of_real (ε.to_real / 3),
    { refine hsnorm₁ n t htm (le_trans ht₁ _),
      rw ennreal.of_real_le_of_real_iff hδ₁.le,
      exact min_le_left _ _ },
    have hng : snorm (t.indicator g) p μ < ennreal.of_real (ε.to_real / 3),
    { refine hsnorm₂ t htm (le_trans ht₁ _),
      rw ennreal.of_real_le_of_real_iff hδ₂.le,
      exact min_le_right _ _ },
    have hlt : snorm (tᶜ.indicator (f n - g)) p μ ≤ ennreal.of_real (ε.to_real / 3),
    { specialize hN n hn,
      have := snorm_sub_le_of_dist_bdd μ ((lt_of_lt_of_le ennreal.zero_lt_one hp).ne.symm)
        hp' htm.compl _ (λ x hx, (dist_comm (g x) (f n x) ▸ (hN x hx).le :
        dist (f n x) (g x) ≤ ε.to_real / (3 * measure_univ_nnreal μ ^ (1 / p.to_real)))),
      refine le_trans this _,
      rw [div_mul_eq_div_mul_one_div, ← ennreal.of_real_to_real (measure_lt_top μ tᶜ).ne,
          ennreal.of_real_rpow_of_nonneg ennreal.to_real_nonneg hdivp, ← ennreal.of_real_mul,
          mul_assoc],
      { refine ennreal.of_real_le_of_real (mul_le_of_le_one_right hε'.le _),
        rw [mul_comm, mul_one_div, div_le_one],
        { refine real.rpow_le_rpow ennreal.to_real_nonneg
            (ennreal.to_real_le_of_le_of_real (measure_univ_nnreal_pos hμ).le _) hdivp,
          rw [ennreal.of_real_coe_nnreal, coe_measure_univ_nnreal],
          exact measure_mono (subset_univ _) },
        { exact real.rpow_pos_of_pos (measure_univ_nnreal_pos hμ) _ } },
      { refine mul_nonneg (hε').le (one_div_nonneg.2 hpow.le) },
      { rw div_mul_eq_div_mul_one_div,
        exact mul_nonneg hε'.le (one_div_nonneg.2 hpow.le) } },
    have : ennreal.of_real (ε.to_real / 3) = ε / 3,
    { rw [ennreal.of_real_div_of_pos (show (0 : ℝ) < 3, by norm_num), ennreal.of_real_to_real h.ne],
      simp },
    rw this at hnf hng hlt,
    rw [snorm_neg, ← ennreal.add_thirds ε, ← sub_eq_add_neg],
    exact add_le_add_three hnf.le hng.le hlt },
  { rw [not_lt, top_le_iff] at h,
    exact ⟨0, λ n hn, by simp [h]⟩ }
end

lemma unif_integrable_of_tendsto_Lp {f : ℕ → α → β} {g : α → β}
  (hf : ∀ n, mem_ℒp (f n) p μ) (hg : mem_ℒp g p μ)
  (hfg : tendsto (λ n, snorm (f n - g) p μ) at_top (𝓝 0)) :
  unif_integrable f p μ :=
begin
  sorry
end

-- should be convergence in measure instead over convergence a.e.
-- statement in current form is **false**
lemma ae_tendsto_of_tendsto_Lp {f : ℕ → α → β} {g : α → β}
  (hf : ∀ n, mem_ℒp (f n) p μ) (hg : mem_ℒp g p μ)
  (hfg : tendsto (λ n, snorm (f n - g) p μ) at_top (𝓝 0)) :
  ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (𝓝 (g x)) :=
sorry

end unif_integrable

/-- In probability theory, a family of functions is uniformly integrable if it is uniformly
integrable in the measure theory sense and is uniformly bounded. -/
def uniform_integrable {m : measurable_space α}
  (μ : measure α) (f : ι → α → β) (p : ℝ≥0∞) : Prop :=
(∀ i, measurable (f i)) ∧ unif_integrable f p μ ∧ ∃ C : ℝ≥0, ∀ i, snorm (f i) p μ < C

variables {f : ι → α → β} {p : ℝ≥0∞}

lemma uniform_integrable.mem_ℒp (hf : uniform_integrable μ f p) (i : ι) :
  mem_ℒp (f i) p μ :=
⟨(hf.1 i).ae_measurable, let ⟨_, _, hC⟩ := hf.2 in lt_trans (hC i) ennreal.coe_lt_top⟩

end measure_theory
