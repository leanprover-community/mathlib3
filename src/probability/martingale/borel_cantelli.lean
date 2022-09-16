/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import probability.martingale.convergence
import probability.martingale.optional_stopping
import probability.martingale.centering
import probability.conditional_expectation

/-!

# Generalized Borel-Cantelli lemma

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

## TODO

Prove the missing second Borel-Cantelli lemma using this generalized version.

-/

open filter
open_locale nnreal ennreal measure_theory probability_theory big_operators topological_space

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
  { exact λ i, strongly_measurable_stopped_value_of_le hf.adapted.prog_measurable_of_nat
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
    simp only [set.mem_union_eq, set.mem_Iic, set.mem_Ici, not_or_distrib, not_le] at this,
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
    simp_rw [set.mem_range, pi.neg_apply, neg_eq_iff_neg_eq, eq_comm] at hω,
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

lemma martingale_part_process_ae_eq (ℱ : filtration ℕ m0) (s : ℕ → set Ω) (n : ℕ) :
  martingale_part ℱ μ (process s) n =ᵐ[μ]
  ∑ k in finset.range n, ((s (k + 1)).indicator 1 - μ[(s (k + 1)).indicator 1 | ℱ k]) :=
begin
  simp only [martingale_part_eq_sum, process_zero, zero_add],
  refine eventually_eq_sum (λ k hk, _),
  simp only [process, finset.sum_range_succ_sub_sum],
end

lemma martingale_part_process_ae_eq' (ℱ : filtration ℕ m0) (s : ℕ → set Ω) :
  ∀ᵐ ω ∂μ, ∀ n, martingale_part ℱ μ (process s) n ω =
  ∑ k in finset.range n, ((s (k + 1)).indicator 1 - μ[(s (k + 1)).indicator 1 | ℱ k]) ω :=
begin
  rw ae_all_iff,
  intro n,
  convert martingale_part_process_ae_eq ℱ s n,
  ext ω,
  rw finset.sum_apply,
end

variables [is_finite_measure μ]

lemma integrable_process (hs : ∀ n, measurable_set[ℱ n] (s n)) (n : ℕ) :
  integrable (process s n) μ :=
integrable_finset_sum' _ $ λ k hk, integrable_on.indicator (integrable_const 1) $ ℱ.le _ _ $ hs _

lemma martingale_part_process_diff_le (hs : ∀ n, measurable_set[ℱ n] (s n)) (n : ℕ) :
  ∀ᵐ ω ∂μ, |martingale_part ℱ μ (process s) (n + 1) ω - martingale_part ℱ μ (process s) n ω| ≤ 1 :=
begin
  have h₁ : μ[(s (n + 1)).indicator 1|ℱ n] ≤ᵐ[μ] 1,
  { change _ ≤ᵐ[μ] (λ ω, 1 : Ω → ℝ),
    rw ← @condexp_const _ _ _ _ _ _ _ μ (ℱ.le n) (1 : ℝ),
    refine condexp_mono ((integrable_indicator_iff (ℱ.le _ _ (hs $ _))).2
      (integrable_const 1).integrable_on) (integrable_const 1)
      (eventually_of_forall $ λ ω, set.indicator_le_self' (λ _ _, zero_le_one) ω) },
  have h₂ : (0 : Ω → ℝ) ≤ᵐ[μ] μ[(s (n + 1)).indicator 1|ℱ n],
    from condexp_nonneg (eventually_of_forall $ λ ω, set.indicator_nonneg (λ _ _, zero_le_one) _),
  filter_upwards [h₁, h₂, martingale_part_process_ae_eq ℱ s (n + 1),
    martingale_part_process_ae_eq ℱ s n] with ω hω₁ hω₂ hω₃ hω₄,
  simp_rw [hω₃, hω₄, finset.sum_apply, finset.sum_range_succ_sub_sum],
  rw [abs_le, neg_le, pi.sub_apply, neg_sub, tsub_le_iff_right, tsub_le_iff_right,
    add_comm (1 : ℝ), add_comm (1 : ℝ)],
  exact ⟨le_add_of_nonneg_of_le (set.indicator_nonneg (λ _ _, zero_le_one) _) hω₁,
    le_add_of_nonneg_of_le hω₂ (set.indicator_le' (λ _ _, le_rfl) (λ _ _, zero_le_one) ω)⟩,
end

lemma martingale_part_process_diff_le' (hs : ∀ n, measurable_set[ℱ n] (s n)) :
  ∀ᵐ ω ∂μ, ∀ n,
    |martingale_part ℱ μ (process s) (n + 1) ω - martingale_part ℱ μ (process s) n ω| ≤ (1 : ℝ≥0) :=
begin
  rw [ae_all_iff, nonneg.coe_one],
  exact martingale_part_process_diff_le hs ,
end

end borel_cantelli

open borel_cantelli

lemma tendsto_sum_indicator_at_top_iff
  [is_finite_measure μ] {s : ℕ → set Ω} (hs : ∀ n, measurable_set[ℱ n] (s n)) :
  ∀ᵐ ω ∂μ,
    tendsto (λ n, ∑ k in finset.range n, (s (k + 1)).indicator (1 : Ω → ℝ) ω) at_top at_top ↔
    tendsto (λ n, ∑ k in finset.range n, μ[(s (k + 1)).indicator (1 : Ω → ℝ) | ℱ k] ω)
      at_top at_top :=
begin
  have h₁ := (martingale_martingale_part (adapted_process hs)
    (integrable_process hs)).ae_not_tendsto_at_top_at_top (martingale_part_process_diff_le' hs),
  have h₂ := (martingale_martingale_part (adapted_process hs)
    (integrable_process hs)).ae_not_tendsto_at_top_at_bot (martingale_part_process_diff_le' hs),
  have h₃ : ∀ᵐ ω ∂μ, ∀ k, (0 : ℝ) ≤ μ[(s (k + 1)).indicator 1|ℱ k] ω,
  { rw ae_all_iff,
    exact λ n, condexp_nonneg (eventually_of_forall $ set.indicator_nonneg $ λ _ _, zero_le_one) },
  filter_upwards [h₁, h₂, h₃, martingale_part_process_ae_eq' ℱ s] with ω hω₁ hω₂ hω₃ hω₄,
  split; intro ht,
  { refine tendsto_at_top_at_top_of_monotone'
      (λ n m hnm, finset.sum_mono_set_of_nonneg hω₃ $ finset.range_mono hnm) _,
    rintro ⟨b, hbdd⟩,
    rw ← tendsto_neg_at_bot_iff at ht,
    simp only [hω₄, pi.sub_apply, finset.sum_sub_distrib] at hω₁,
    exact hω₁ (tendsto_at_top_add_right_of_le _ (-b)
      (tendsto_neg_at_bot_iff.1 ht) $ λ n, neg_le_neg (hbdd ⟨n, rfl⟩)) },
  { refine tendsto_at_top_at_top_of_monotone'
      (λ n m hnm, finset.sum_mono_set_of_nonneg (λ i, set.indicator_nonneg (λ _ _, zero_le_one) _) $
      finset.range_mono hnm) _,
    rintro ⟨b, hbdd⟩,
    simp only [hω₄, pi.sub_apply, finset.sum_sub_distrib] at hω₂,
    exact hω₂ (tendsto_at_bot_add_left_of_ge _ b (λ n, hbdd ⟨n, rfl⟩) $
      tendsto_neg_at_bot_iff.2 ht) },
  all_goals { apply_instance }
end

section centering

section move

variables {α : Type*} {n m : measurable_space α} {ν : @measure α m}

lemma set_integral_gt_gt {R : ℝ} (hR : 0 ≤ R) {f : α → ℝ}
  (hfm : measurable f) (hfint : integrable_on f {x | ↑R < f x} ν) (hν : ν {x | ↑R < f x} ≠ 0):
  (ν {x | ↑R < f x}).to_real * R < ∫ x in {x | ↑R < f x}, f x ∂ν :=
begin
  have : integrable_on (λ x, R) {x | ↑R < f x} ν,
  { refine ⟨ae_strongly_measurable_const, lt_of_le_of_lt _ hfint.2⟩,
    refine set_lintegral_mono (measurable.nnnorm _).coe_nnreal_ennreal
      hfm.nnnorm.coe_nnreal_ennreal (λ x hx, _),
    { exact measurable_const },
    { simp only [ennreal.coe_le_coe, real.nnnorm_of_nonneg hR,
        real.nnnorm_of_nonneg (hR.trans $ le_of_lt hx), subtype.mk_le_mk],
      exact le_of_lt hx } },
  rw [← sub_pos, ← smul_eq_mul, ← set_integral_const, ← integral_sub hfint this,
    set_integral_pos_iff_support_of_nonneg_ae],
  { rw ← zero_lt_iff at hν,
    rwa set.inter_eq_self_of_subset_right,
    exact λ x hx, ne.symm (ne_of_lt $ sub_pos.2 hx) },
  { change ∀ᵐ x ∂(ν.restrict _), _,
    rw ae_restrict_iff,
    { exact eventually_of_forall (λ x hx, sub_nonneg.2 $ le_of_lt hx) },
    { exact measurable_set_le measurable_zero (hfm.sub measurable_const) } },
  { exact integrable.sub hfint this },
end

lemma ennreal.coe_nnnorm {E : Type*} [seminormed_add_comm_group E] {a : E} :
  ↑∥a∥₊ = ennreal.of_real (∥a∥) :=
begin
  rw ennreal.of_real_eq_coe_nnreal,
  refl,
end

lemma integral_abs_condexp_le (f : α → ℝ) :
  ∫ x, |ν[f | n] x| ∂ν ≤ ∫ x, |f x| ∂ν :=
begin
  by_cases hnm : n ≤ m,
  swap,
  { simp_rw [condexp_of_not_le hnm, pi.zero_apply, abs_zero, integral_zero],
    exact integral_nonneg (λ x, abs_nonneg _) },
  by_cases hfint : integrable f ν,
  swap,
  { simp only [condexp_undef hfint, pi.zero_apply, abs_zero, integral_const,
      algebra.id.smul_eq_mul, mul_zero],
    exact integral_nonneg (λ x, abs_nonneg _) },
  rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae],
  { rw ennreal.to_real_le_to_real; simp_rw [← real.norm_eq_abs, ← ennreal.coe_nnnorm],
    { rw [← snorm_one_eq_lintegral_nnnorm, ← snorm_one_eq_lintegral_nnnorm],
      exact snorm_one_condexp_le_snorm _ },
    { exact ne_of_lt integrable_condexp.2 },
    { exact ne_of_lt hfint.2 } },
  { exact eventually_of_forall (λ x, abs_nonneg _) },
  { simp_rw ← real.norm_eq_abs,
    exact hfint.1.norm },
  { exact eventually_of_forall (λ x, abs_nonneg _) },
  { simp_rw ← real.norm_eq_abs,
    exact (strongly_measurable_condexp.mono hnm).ae_strongly_measurable.norm }
end

lemma set_integral_abs_condexp_le {s : set α} (hs : measurable_set[n] s) (f : α → ℝ) :
  ∫ x in s, |ν[f | n] x| ∂ν ≤ ∫ x in s, |f x| ∂ν :=
begin
  by_cases hnm : n ≤ m,
  swap,
  { simp_rw [condexp_of_not_le hnm, pi.zero_apply, abs_zero, integral_zero],
    exact integral_nonneg (λ x, abs_nonneg _) },
  by_cases hfint : integrable f ν,
  swap,
  { simp only [condexp_undef hfint, pi.zero_apply, abs_zero, integral_const,
      algebra.id.smul_eq_mul, mul_zero],
    exact integral_nonneg (λ x, abs_nonneg _) },
  have : ∫ x in s, |ν[f | n] x| ∂ν = ∫ x, |ν[s.indicator f | n] x| ∂ν,
  { rw ← integral_indicator,
    swap, { exact hnm _ hs },
    refine integral_congr_ae _,
    have : (λ x, |ν[s.indicator f | n] x|) =ᵐ[ν] λ x, |s.indicator (ν[f | n]) x| :=
      eventually_eq.fun_comp (condexp_indicator hfint hs) _,
    refine eventually_eq.trans (eventually_of_forall $ λ x, _) this.symm,
    rw [← real.norm_eq_abs, norm_indicator_eq_indicator_norm],
    refl },
  rw [this, ← integral_indicator],
  swap, { exact hnm _ hs },
  refine (integral_abs_condexp_le _).trans (le_of_eq $ integral_congr_ae $
    eventually_of_forall $ λ x, _),
  rw [← real.norm_eq_abs, norm_indicator_eq_indicator_norm],
  refl,
end

lemma ae_bdd_condexp_of_ae_bdd {f : α → ℝ} (hbdd : ∀ᵐ x ∂ν, |f x| ≤ R) :
  ∀ᵐ x ∂ν, |ν[f|n] x| ≤ R :=
begin
  by_cases hnm : n ≤ m,
  swap,
  { simp_rw [condexp_of_not_le hnm, pi.zero_apply, abs_zero],
    refine eventually_of_forall (λ x, R.coe_nonneg) },
  by_cases hfint : integrable f ν,
  swap,
  { simp_rw [condexp_undef hfint],
    filter_upwards [hbdd] with x hx,
    rw [pi.zero_apply, abs_zero],
    exact (abs_nonneg _).trans hx },
  by_contra h,
  change ν _ ≠ 0 at h,
  simp only [← zero_lt_iff, set.compl_def, set.mem_set_of_eq, not_le] at h,
  suffices : (ν {x | ↑R < |ν[f|n] x|}).to_real * ↑R < (ν {x | ↑R < |ν[f|n] x|}).to_real * ↑R,
  { exact this.ne rfl },
  refine lt_of_lt_of_le (set_integral_gt_gt R.coe_nonneg _ _ h.ne.symm) _,
  { simp_rw [← real.norm_eq_abs],
    exact (strongly_measurable_condexp.mono hnm).measurable.norm },
  { exact integrable_condexp.abs.integrable_on },
  refine (set_integral_abs_condexp_le _ _).trans _,
  { simp_rw [← real.norm_eq_abs],
    exact @measurable_set_lt _ _ _ _ _ n _ _ _ _ _ measurable_const
      strongly_measurable_condexp.norm.measurable },
  simp only [← smul_eq_mul, ← set_integral_const, nnreal.val_eq_coe,
    is_R_or_C.coe_real_eq_id, id.def],
  refine set_integral_mono_ae hfint.abs.integrable_on _ _,
  { refine ⟨ae_strongly_measurable_const, lt_of_le_of_lt _
      (integrable_condexp.integrable_on : integrable_on (ν[f|n]) {x | ↑R < |ν[f|n] x|} ν).2⟩,
    refine set_lintegral_mono (measurable.nnnorm _).coe_nnreal_ennreal
      (strongly_measurable_condexp.mono hnm).measurable.nnnorm.coe_nnreal_ennreal (λ x hx, _),
    { exact measurable_const },
    { rw [ennreal.coe_le_coe, real.nnnorm_of_nonneg R.coe_nonneg],
      exact subtype.mk_le_mk.2 (le_of_lt hx) } },
  { exact hbdd },
end

end move

lemma predictable_part_bdd_difference
  (ℱ : filtration ℕ m0) (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
  ∀ᵐ ω ∂μ, ∀ i, |predictable_part ℱ μ f (i + 1) ω - predictable_part ℱ μ f i ω| ≤ R :=
begin
  simp_rw [predictable_part, finset.sum_apply, finset.sum_range_succ_sub_sum],
  exact ae_all_iff.2 (λ i, ae_bdd_condexp_of_ae_bdd $ ae_all_iff.1 hbdd i),
end

lemma martingale_part_bdd_difference
  (ℱ : filtration ℕ m0) (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
  ∀ᵐ ω ∂μ, ∀ i, |martingale_part ℱ μ f (i + 1) ω - martingale_part ℱ μ f i ω| ≤ ↑(2 * R) :=
begin
  filter_upwards [hbdd, predictable_part_bdd_difference ℱ hbdd] with ω hω₁ hω₂ i,
  simp only [two_mul, martingale_part, pi.sub_apply],
  have : |f (i + 1) ω - predictable_part ℱ μ f (i + 1) ω - (f i ω - predictable_part ℱ μ f i ω)| =
    |(f (i + 1) ω - f i ω) - (predictable_part ℱ μ f (i + 1) ω - predictable_part ℱ μ f i ω)|,
  { ring_nf }, -- `ring` suggests `ring_nf` despite proving the goal
  rw this,
  exact (abs_sub _ _).trans (add_le_add (hω₁ i) (hω₂ i)),
end

lemma tendsto_sum_indicator_at_top_iff'
  [is_finite_measure μ] (hf : adapted ℱ f) (hint : ∀ n, integrable (f n) μ)
  (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
  ∀ᵐ ω ∂μ, tendsto (λ n, f n ω) at_top at_top ↔
    tendsto (λ n, predictable_part ℱ μ f n ω) at_top at_top :=
begin
  have h₁ := (martingale_martingale_part hf hint).ae_not_tendsto_at_top_at_top
    (martingale_part_bdd_difference ℱ hbdd),
  have h₂ := (martingale_martingale_part hf hint).ae_not_tendsto_at_top_at_bot
    (martingale_part_bdd_difference ℱ hbdd),
  sorry
end

end centering

/-- **Lévy's generalization of the Borel-Cantelli lemma**: given a sequence of sets `s` and a
filtration `ℱ` such that for all `n`, `s n` is `ℱ n`-measurable, `at_top.limsup s` is almost
everywhere equal to the set for which `∑ k, ℙ(s (k + 1) | ℱ k) = ∞`. -/
theorem ae_mem_limsup_at_top_iff [is_finite_measure μ]
  {s : ℕ → set Ω} (hs : ∀ n, measurable_set[ℱ n] (s n)) :
  ∀ᵐ ω ∂μ, ω ∈ limsup at_top s ↔
    tendsto (λ n, ∑ k in finset.range n, μ[(s (k + 1)).indicator (1 : Ω → ℝ) | ℱ k] ω)
      at_top at_top :=
(limsup_eq_tendsto_sum_indicator_at_top ℝ s).symm ▸ tendsto_sum_indicator_at_top_iff hs

end measure_theory
