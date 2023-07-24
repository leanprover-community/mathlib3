/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import probability.martingale.convergence
import probability.martingale.optional_stopping
import probability.martingale.centering

/-!

# Generalized Borel-Cantelli lemma

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves Lévy's generalized Borel-Cantelli lemma which is a generalization of the
Borel-Cantelli lemmas. With this generalization, one can easily deduce the Borel-Cantelli lemmas
by choosing appropriate filtrations. This file also contains the one sided martingale bound which
is required to prove the generalized Borel-Cantelli.

## Main results

- `measure_theory.submartingale.bdd_above_iff_exists_tendsto`: the one sided martingale bound: given
  a submartingale `f` with uniformly bounded differences, the set for which `f` converges is almost
  everywhere equal to the set for which it is bounded.
- `measure_theory.ae_mem_limsup_at_top_iff`: Lévy's generalized Borel-Cantelli:
  given a filtration `ℱ` and a sequence of sets `s` such that `s n ∈ ℱ n` for all `n`,
  `limsup at_top s` is almost everywhere equal to the set for which `∑ ℙ[s (n + 1)∣ℱ n] = ∞`.

-/

open filter
open_locale nnreal ennreal measure_theory probability_theory big_operators topology

namespace measure_theory

variables {Ω : Type*} {m0 : measurable_space Ω} {μ : measure Ω}
  {ℱ : filtration ℕ m0} {f : ℕ → Ω → ℝ} {ω : Ω}

/-!
### One sided martingale bound
-/

-- TODO: `least_ge` should be defined taking values in `with_top ℕ` once the `stopped_process`
-- refactor is complete
/-- `least_ge f r n` is the stopping time corresponding to the first time `f ≥ r`. -/
noncomputable
def least_ge (f : ℕ → Ω → ℝ) (r : ℝ) (n : ℕ) := hitting f (set.Ici r) 0 n

lemma adapted.is_stopping_time_least_ge (r : ℝ) (n : ℕ) (hf : adapted ℱ f) :
  is_stopping_time ℱ (least_ge f r n) :=
hitting_is_stopping_time hf measurable_set_Ici

lemma least_ge_le {i : ℕ} {r : ℝ} (ω : Ω) : least_ge f r i ω ≤ i :=
hitting_le ω

-- The following four lemmas shows `least_ge` behaves like a stopped process. Ideally we should
-- define `least_ge` as a stopping time and take its stopped process. However, we can't do that
-- with our current definition since a stopping time takes only finite indicies. An upcomming
-- refactor should hopefully make it possible to have stopping times taking infinity as a value
lemma least_ge_mono {n m : ℕ} (hnm : n ≤ m) (r : ℝ) (ω : Ω) :
  least_ge f r n ω ≤ least_ge f r m ω :=
hitting_mono hnm

lemma least_ge_eq_min (π : Ω → ℕ) (r : ℝ) (ω : Ω)
  {n : ℕ} (hπn : ∀ ω, π ω ≤ n) :
  least_ge f r (π ω) ω = min (π ω) (least_ge f r n ω) :=
begin
  classical,
  refine le_antisymm (le_min (least_ge_le _) (least_ge_mono (hπn ω) r ω)) _,
  by_cases hle : π ω ≤ least_ge f r n ω,
  { rw [min_eq_left hle, least_ge],
    by_cases h : ∃ j ∈ set.Icc 0 (π ω), f j ω ∈ set.Ici r,
    { refine hle.trans (eq.le _),
      rw [least_ge, ← hitting_eq_hitting_of_exists (hπn ω) h] },
    { simp only [hitting, if_neg h] } },
  { rw [min_eq_right (not_le.1 hle).le, least_ge, least_ge,
      ← hitting_eq_hitting_of_exists (hπn ω) _],
    rw [not_le, least_ge, hitting_lt_iff _ (hπn ω)] at hle,
    exact let ⟨j, hj₁, hj₂⟩ := hle in ⟨j, ⟨hj₁.1, hj₁.2.le⟩, hj₂⟩ }
end

lemma stopped_value_stopped_value_least_ge (f : ℕ → Ω → ℝ) (π : Ω → ℕ) (r : ℝ)
  {n : ℕ} (hπn : ∀ ω, π ω ≤ n) :
  stopped_value (λ i, stopped_value f (least_ge f r i)) π
    = stopped_value (stopped_process f (least_ge f r n)) π :=
by { ext1 ω, simp_rw [stopped_process, stopped_value], rw least_ge_eq_min _ _ _ hπn, }

lemma submartingale.stopped_value_least_ge [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (r : ℝ) :
  submartingale (λ i, stopped_value f (least_ge f r i)) ℱ μ :=
begin
  rw submartingale_iff_expected_stopped_value_mono,
  { intros σ π hσ hπ hσ_le_π hπ_bdd,
    obtain ⟨n, hπ_le_n⟩ := hπ_bdd,
    simp_rw stopped_value_stopped_value_least_ge f σ r (λ i, (hσ_le_π i).trans (hπ_le_n i)),
    simp_rw stopped_value_stopped_value_least_ge f π r hπ_le_n,
    refine hf.expected_stopped_value_mono _ _ _ (λ ω, (min_le_left _ _).trans (hπ_le_n ω)),
    { exact hσ.min (hf.adapted.is_stopping_time_least_ge _ _), },
    { exact hπ.min (hf.adapted.is_stopping_time_least_ge _ _), },
    { exact λ ω, min_le_min (hσ_le_π ω) le_rfl, }, },
  { exact λ i, strongly_measurable_stopped_value_of_le hf.adapted.prog_measurable_of_discrete
      (hf.adapted.is_stopping_time_least_ge _ _) least_ge_le, },
  { exact λ i, integrable_stopped_value _ ((hf.adapted.is_stopping_time_least_ge _ _))
      (hf.integrable) least_ge_le, },
end

variables {r : ℝ} {R : ℝ≥0}

lemma norm_stopped_value_least_ge_le (hr : 0 ≤ r) (hf0 : f 0 = 0)
  (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) (i : ℕ) :
  ∀ᵐ ω ∂μ, stopped_value f (least_ge f r i) ω ≤ r + R :=
begin
  filter_upwards [hbdd] with ω hbddω,
  change f (least_ge f r i ω) ω ≤ r + R,
  by_cases heq : least_ge f r i ω = 0,
  { rw [heq, hf0, pi.zero_apply],
    exact add_nonneg hr R.coe_nonneg },
  { obtain ⟨k, hk⟩ := nat.exists_eq_succ_of_ne_zero heq,
    rw [hk, add_comm, ← sub_le_iff_le_add],
    have := not_mem_of_lt_hitting (hk.symm ▸ k.lt_succ_self : k < least_ge f r i ω) (zero_le _),
    simp only [set.mem_union, set.mem_Iic, set.mem_Ici, not_or_distrib, not_le] at this,
    exact (sub_lt_sub_left this _).le.trans ((le_abs_self _).trans (hbddω _)) }
end

lemma submartingale.stopped_value_least_ge_snorm_le [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (hr : 0 ≤ r) (hf0 : f 0 = 0)
  (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) (i : ℕ) :
  snorm (stopped_value f (least_ge f r i)) 1 μ ≤ 2 * μ set.univ * ennreal.of_real (r + R) :=
begin
  refine snorm_one_le_of_le' ((hf.stopped_value_least_ge r).integrable _) _
    (norm_stopped_value_least_ge_le hr hf0 hbdd i),
  rw ← integral_univ,
  refine le_trans _ ((hf.stopped_value_least_ge r).set_integral_le (zero_le _)
    measurable_set.univ),
  simp_rw [stopped_value, least_ge, hitting_of_le le_rfl, hf0, integral_zero']
end

lemma submartingale.stopped_value_least_ge_snorm_le' [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (hr : 0 ≤ r) (hf0 : f 0 = 0)
  (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) (i : ℕ) :
  snorm (stopped_value f (least_ge f r i)) 1 μ ≤
    ennreal.to_nnreal (2 * μ set.univ * ennreal.of_real (r + R)) :=
begin
  refine (hf.stopped_value_least_ge_snorm_le hr hf0 hbdd i).trans _,
  simp [ennreal.coe_to_nnreal (measure_ne_top μ _), ennreal.coe_to_nnreal],
end

/-- This lemma is superceded by `submartingale.bdd_above_iff_exists_tendsto`. -/
lemma submartingale.exists_tendsto_of_abs_bdd_above_aux [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (hf0 : f 0 = 0)
  (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
  ∀ᵐ ω ∂μ, bdd_above (set.range $ λ n, f n ω) → ∃ c, tendsto (λ n, f n ω) at_top (𝓝 c) :=
begin
  have ht : ∀ᵐ ω ∂μ, ∀ i : ℕ, ∃ c, tendsto (λ n, stopped_value f (least_ge f i n) ω) at_top (𝓝 c),
  { rw ae_all_iff,
    exact λ i, submartingale.exists_ae_tendsto_of_bdd (hf.stopped_value_least_ge i)
      (hf.stopped_value_least_ge_snorm_le' i.cast_nonneg hf0 hbdd) },
  filter_upwards [ht] with ω hω hωb,
  rw bdd_above at hωb,
  obtain ⟨i, hi⟩ := exists_nat_gt hωb.some,
  have hib : ∀ n, f n ω < i,
  { intro n,
    exact lt_of_le_of_lt ((mem_upper_bounds.1 hωb.some_mem) _ ⟨n, rfl⟩) hi },
  have heq : ∀ n, stopped_value f (least_ge f i n) ω = f n ω,
  { intro n,
    rw [least_ge, hitting, stopped_value],
    simp only,
    rw if_neg,
    simp only [set.mem_Icc, set.mem_union, set.mem_Ici],
    push_neg,
    exact λ j _, hib j },
  simp only [← heq, hω i],
end

lemma submartingale.bdd_above_iff_exists_tendsto_aux [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (hf0 : f 0 = 0)
  (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
  ∀ᵐ ω ∂μ, bdd_above (set.range $ λ n, f n ω) ↔ ∃ c, tendsto (λ n, f n ω) at_top (𝓝 c) :=
by filter_upwards [hf.exists_tendsto_of_abs_bdd_above_aux hf0 hbdd] with ω hω using
  ⟨hω, λ ⟨c, hc⟩, hc.bdd_above_range⟩

/-- One sided martingale bound: If `f` is a submartingale which has uniformly bounded differences,
then for almost every `ω`, `f n ω` is bounded above (in `n`) if and only if it converges. -/
lemma submartingale.bdd_above_iff_exists_tendsto [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
  ∀ᵐ ω ∂μ, bdd_above (set.range $ λ n, f n ω) ↔ ∃ c, tendsto (λ n, f n ω) at_top (𝓝 c) :=
begin
  set g : ℕ → Ω → ℝ := λ n ω, f n ω - f 0 ω with hgdef,
  have hg : submartingale g ℱ μ :=
    hf.sub_martingale (martingale_const_fun _ _ (hf.adapted 0) (hf.integrable 0)),
  have hg0 : g 0 = 0,
  { ext ω,
    simp only [hgdef, sub_self, pi.zero_apply] },
  have hgbdd : ∀ᵐ ω ∂μ, ∀ (i : ℕ), |g (i + 1) ω - g i ω| ≤ ↑R,
  { simpa only [sub_sub_sub_cancel_right] },
  filter_upwards [hg.bdd_above_iff_exists_tendsto_aux hg0 hgbdd] with ω hω,
  convert hω using 1; rw eq_iff_iff,
  { simp only [hgdef],
    refine ⟨λ h, _, λ h, _⟩;
    obtain ⟨b, hb⟩ := h;
    refine ⟨b + |f 0 ω|, λ y hy, _⟩;
    obtain ⟨n, rfl⟩ := hy,
    { simp_rw [sub_eq_add_neg],
      exact add_le_add (hb ⟨n, rfl⟩) (neg_le_abs_self _) },
    { exact sub_le_iff_le_add.1 (le_trans (sub_le_sub_left (le_abs_self _) _) (hb ⟨n, rfl⟩)) } },
  { simp only [hgdef],
    refine ⟨λ h, _, λ h, _⟩;
    obtain ⟨c, hc⟩ := h,
    { exact ⟨c - f 0 ω, hc.sub_const _⟩ },
    { refine ⟨c + f 0 ω, _⟩,
      have := hc.add_const (f 0 ω),
      simpa only [sub_add_cancel] } }
end

/-!
### Lévy's generalization of the Borel-Cantelli lemma

Lévy's generalization of the Borel-Cantelli lemma states that: given a natural number indexed
filtration $(\mathcal{F}_n)$, and a sequence of sets $(s_n)$ such that for all
$n$, $s_n \in \mathcal{F}_n$, $limsup_n s_n$ is almost everywhere equal to the set for which
$\sum_n \mathbb{P}[s_n \mid \mathcal{F}_n] = \infty$.

The proof strategy follows by constructing a martingale satisfying the one sided martingale bound.
In particular, we define
$$
  f_n := \sum_{k < n} \mathbf{1}_{s_{n + 1}} - \mathbb{P}[s_{n + 1} \mid \mathcal{F}_n].
$$
Then, as a martingale is both a sub and a super-martingale, the set for which it is unbounded from
above must agree with the set for which it is unbounded from below almost everywhere. Thus, it
can only converge to $\pm \infty$ with probability 0. Thus, by considering
$$
  \limsup_n s_n = \{\sum_n \mathbf{1}_{s_n} = \infty\}
$$
almost everywhere, the result follows.
-/

lemma martingale.bdd_above_range_iff_bdd_below_range [is_finite_measure μ]
  (hf : martingale f ℱ μ) (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
  ∀ᵐ ω ∂μ, bdd_above (set.range (λ n, f n ω)) ↔ bdd_below (set.range (λ n, f n ω)) :=
begin
  have hbdd' : ∀ᵐ ω ∂μ, ∀ i, |(-f) (i + 1) ω - (-f) i ω| ≤ R,
  { filter_upwards [hbdd] with ω hω i,
    erw [← abs_neg, neg_sub, sub_neg_eq_add, neg_add_eq_sub],
    exact hω i },
  have hup := hf.submartingale.bdd_above_iff_exists_tendsto hbdd,
  have hdown := hf.neg.submartingale.bdd_above_iff_exists_tendsto hbdd',
  filter_upwards [hup, hdown] with ω hω₁ hω₂,
  have : (∃ c, tendsto (λ n, f n ω) at_top (𝓝 c)) ↔ ∃ c, tendsto (λ n, (-f) n ω) at_top (𝓝 c),
  { split; rintro ⟨c, hc⟩,
    { exact ⟨-c, hc.neg⟩ },
    { refine ⟨-c, _⟩,
      convert hc.neg,
      simp only [neg_neg, pi.neg_apply] } },
  rw [hω₁, this, ← hω₂],
  split; rintro ⟨c, hc⟩; refine ⟨-c, λ ω hω, _⟩,
  { rw mem_upper_bounds at hc,
    refine neg_le.2 (hc _ _),
    simpa only [pi.neg_apply, set.mem_range, neg_inj] },
  { rw mem_lower_bounds at hc,
    simp_rw [set.mem_range, pi.neg_apply, neg_eq_iff_eq_neg] at hω,
    refine le_neg.1 (hc _ _),
    simpa only [set.mem_range] }
end

lemma martingale.ae_not_tendsto_at_top_at_top [is_finite_measure μ]
  (hf : martingale f ℱ μ) (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
  ∀ᵐ ω ∂μ, ¬ tendsto (λ n, f n ω) at_top at_top :=
by filter_upwards [hf.bdd_above_range_iff_bdd_below_range hbdd] with ω hω htop using
    unbounded_of_tendsto_at_top htop (hω.2 $ bdd_below_range_of_tendsto_at_top_at_top htop)

lemma martingale.ae_not_tendsto_at_top_at_bot [is_finite_measure μ]
  (hf : martingale f ℱ μ) (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
  ∀ᵐ ω ∂μ, ¬ tendsto (λ n, f n ω) at_top at_bot :=
by filter_upwards [hf.bdd_above_range_iff_bdd_below_range hbdd] with ω hω htop using
    unbounded_of_tendsto_at_bot htop (hω.1 $ bdd_above_range_of_tendsto_at_top_at_bot htop)

namespace borel_cantelli

/-- Auxiliary definition required to prove Lévy's generalization of the Borel-Cantelli lemmas for
which we will take the martingale part. -/
noncomputable
def process (s : ℕ → set Ω) (n : ℕ) : Ω → ℝ :=
∑ k in finset.range n, (s (k + 1)).indicator 1

variables {s : ℕ → set Ω}

lemma process_zero : process s 0 = 0 :=
by rw [process, finset.range_zero, finset.sum_empty]

lemma adapted_process (hs : ∀ n, measurable_set[ℱ n] (s n)) :
  adapted ℱ (process s) :=
λ n, finset.strongly_measurable_sum' _ $ λ k hk, strongly_measurable_one.indicator $
  ℱ.mono (finset.mem_range.1 hk) _ $ hs _

lemma martingale_part_process_ae_eq (ℱ : filtration ℕ m0) (μ : measure Ω) (s : ℕ → set Ω) (n : ℕ) :
  martingale_part (process s) ℱ μ n =
  ∑ k in finset.range n, ((s (k + 1)).indicator 1 - μ[(s (k + 1)).indicator 1 | ℱ k]) :=
begin
  simp only [martingale_part_eq_sum, process_zero, zero_add],
  refine finset.sum_congr rfl (λ k hk, _),
  simp only [process, finset.sum_range_succ_sub_sum],
end

lemma predictable_part_process_ae_eq (ℱ : filtration ℕ m0) (μ : measure Ω) (s : ℕ → set Ω) (n : ℕ) :
  predictable_part (process s) ℱ μ n =
  ∑ k in finset.range n, μ[(s (k + 1)).indicator (1 : Ω → ℝ) | ℱ k] :=
begin
  have := martingale_part_process_ae_eq ℱ μ s n,
  simp_rw [martingale_part, process, finset.sum_sub_distrib] at this,
  exact sub_right_injective this,
end

lemma process_difference_le (s : ℕ → set Ω) (ω : Ω) (n : ℕ) :
  |process s (n + 1) ω - process s n ω| ≤ (1 : ℝ≥0) :=
begin
  rw [nonneg.coe_one, process, process, finset.sum_apply, finset.sum_apply,
    finset.sum_range_succ_sub_sum, ← real.norm_eq_abs, norm_indicator_eq_indicator_norm],
  refine set.indicator_le' (λ _ _, _) (λ _ _, zero_le_one) _,
  rw [pi.one_apply, norm_one]
end

lemma integrable_process (μ : measure Ω) [is_finite_measure μ]
  (hs : ∀ n, measurable_set[ℱ n] (s n)) (n : ℕ) :
  integrable (process s n) μ :=
integrable_finset_sum' _ $ λ k hk,
  integrable_on.integrable_indicator (integrable_const 1) $ ℱ.le _ _ $ hs _

end borel_cantelli

open borel_cantelli

/-- An a.e. monotone adapted process `f` with uniformly bounded differences converges to `+∞` if
and only if its predictable part also converges to `+∞`. -/
lemma tendsto_sum_indicator_at_top_iff [is_finite_measure μ]
  (hfmono : ∀ᵐ ω ∂μ, ∀ n, f n ω ≤ f (n + 1) ω)
  (hf : adapted ℱ f) (hint : ∀ n, integrable (f n) μ)
  (hbdd : ∀ᵐ ω ∂μ, ∀ n, |f (n + 1) ω - f n ω| ≤ R) :
  ∀ᵐ ω ∂μ, tendsto (λ n, f n ω) at_top at_top ↔
    tendsto (λ n, predictable_part f ℱ μ n ω) at_top at_top :=
begin
  have h₁ := (martingale_martingale_part hf hint).ae_not_tendsto_at_top_at_top
    (martingale_part_bdd_difference ℱ hbdd),
  have h₂ := (martingale_martingale_part hf hint).ae_not_tendsto_at_top_at_bot
    (martingale_part_bdd_difference ℱ hbdd),
  have h₃ : ∀ᵐ ω ∂μ, ∀ n, 0 ≤ μ[f (n + 1) - f n | ℱ n] ω,
  { refine ae_all_iff.2 (λ n, condexp_nonneg _),
    filter_upwards [ae_all_iff.1 hfmono n] with ω hω using sub_nonneg.2 hω },
  filter_upwards [h₁, h₂, h₃, hfmono] with ω hω₁ hω₂ hω₃ hω₄,
  split; intro ht,
  { refine tendsto_at_top_at_top_of_monotone' _ _,
    { intros n m hnm,
      simp only [predictable_part, finset.sum_apply],
      refine finset.sum_mono_set_of_nonneg hω₃ (finset.range_mono hnm) },
    rintro ⟨b, hbdd⟩,
    rw ← tendsto_neg_at_bot_iff at ht,
    simp only [martingale_part, sub_eq_add_neg] at hω₁,
    exact hω₁ (tendsto_at_top_add_right_of_le _ (-b)
      (tendsto_neg_at_bot_iff.1 ht) $ λ n, neg_le_neg (hbdd ⟨n, rfl⟩)) },
  { refine tendsto_at_top_at_top_of_monotone' (monotone_nat_of_le_succ hω₄) _,
    rintro ⟨b, hbdd⟩,
    exact hω₂ (tendsto_at_bot_add_left_of_ge _ b (λ n, hbdd ⟨n, rfl⟩) $
      tendsto_neg_at_bot_iff.2 ht) },
end

open borel_cantelli

lemma tendsto_sum_indicator_at_top_iff' [is_finite_measure μ]
  {s : ℕ → set Ω} (hs : ∀ n, measurable_set[ℱ n] (s n)) :
  ∀ᵐ ω ∂μ,
    tendsto (λ n, ∑ k in finset.range n, (s (k + 1)).indicator (1 : Ω → ℝ) ω) at_top at_top ↔
    tendsto (λ n, ∑ k in finset.range n, μ[(s (k + 1)).indicator (1 : Ω → ℝ) | ℱ k] ω)
      at_top at_top :=
begin
  have := tendsto_sum_indicator_at_top_iff (eventually_of_forall $ λ ω n, _) (adapted_process hs)
    (integrable_process μ hs) (eventually_of_forall $ process_difference_le s),
  swap,
  { rw [process, process, ← sub_nonneg, finset.sum_apply, finset.sum_apply,
      finset.sum_range_succ_sub_sum],
    exact set.indicator_nonneg (λ _ _, zero_le_one) _ },
  simp_rw [process, predictable_part_process_ae_eq] at this,
  simpa using this,
end

/-- **Lévy's generalization of the Borel-Cantelli lemma**: given a sequence of sets `s` and a
filtration `ℱ` such that for all `n`, `s n` is `ℱ n`-measurable, `at_top.limsup s` is almost
everywhere equal to the set for which `∑ k, ℙ(s (k + 1) | ℱ k) = ∞`. -/
theorem ae_mem_limsup_at_top_iff (μ : measure Ω) [is_finite_measure μ]
  {s : ℕ → set Ω} (hs : ∀ n, measurable_set[ℱ n] (s n)) :
  ∀ᵐ ω ∂μ, ω ∈ limsup s at_top ↔
    tendsto (λ n, ∑ k in finset.range n, μ[(s (k + 1)).indicator (1 : Ω → ℝ) | ℱ k] ω)
      at_top at_top :=
(limsup_eq_tendsto_sum_indicator_at_top ℝ s).symm ▸ tendsto_sum_indicator_at_top_iff' hs

end measure_theory
