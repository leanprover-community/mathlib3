/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import probability.martingale.convergence
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

lemma least_ge_eq_lt_iff {n : ℕ} {r : ℝ} {k : ℕ} (hk : k < n) :
  least_ge f r n ω = k ↔ least_ge f r (n + 1) ω = k :=
begin
  split; intro h,
  { rw [← h, eq_comm],
    rw [← h, least_ge, hitting_lt_iff n le_rfl] at hk,
    obtain ⟨j, hj₁, hj₂⟩ := hk,
    exact hitting_eq_hitting_of_exists n.le_succ ⟨j, ⟨zero_le _, hj₁.2.le⟩, hj₂⟩ },
  { rw ← h,
    rw [← h, least_ge, hitting_lt_iff _ n.le_succ] at hk,
    obtain ⟨j, hj₁, hj₂⟩ := hk,
    exact hitting_eq_hitting_of_exists n.le_succ ⟨j, ⟨zero_le _, hj₁.2.le⟩, hj₂⟩ }
end

lemma least_ge_succ_eq_iff (n : ℕ) {r : ℝ} :
  least_ge f r (n + 1) ω = n ↔ least_ge f r n ω = n ∧ r ≤ f n ω :=
begin
  split,
  { intro h,
    have : least_ge f r (n + 1) ω < n + 1 := h.symm ▸ n.lt_succ_self,
    refine ⟨_, (h ▸ hitting_mem_set _ : f n ω ∈ set.Ici r)⟩,
    { rw ← h,
      refine hitting_eq_hitting_of_exists (hitting_le _) _,
      rw [least_ge, hitting_lt_iff (n + 1) le_rfl] at this,
      obtain ⟨j, hj₁, hj₂⟩ := this,
      exact ⟨j, ⟨zero_le _, h.symm ▸ nat.le_of_lt_succ hj₁.2⟩, hj₂⟩ },
    { rw [least_ge, hitting_lt_iff (n + 1) le_rfl] at this,
      obtain ⟨j, hj₁, hj₂⟩ := this,
      exact ⟨j, ⟨zero_le _, hj₁.2.le⟩, hj₂⟩ } },
  { rintro ⟨h₁, h₂⟩,
    rw [← h₁, eq_comm],
    exact hitting_eq_hitting_of_exists (h₁.symm ▸ n.le_succ)
      ⟨n, ⟨zero_le _, le_rfl⟩, h₂⟩ }
end

lemma least_ge_succ_eq_iff' (n : ℕ) {r : ℝ} :
  least_ge f r (n + 1) ω = n + 1 ↔ least_ge f r n ω = n ∧ f n ω < r :=
begin
  split,
  { intro h,
    have : least_ge f r n ω = n,
    { refine le_antisymm (hitting_le _) _,
      by_contra hlt,
      rw [not_le, least_ge] at hlt,
      refine ne_of_lt _ h,
      rw [least_ge, hitting_lt_iff (n + 1) le_rfl],
      exact ⟨least_ge f r n ω, ⟨zero_le _, nat.lt_succ_of_le (hitting_le _)⟩,
        hitting_mem_set_of_hitting_lt hlt⟩ },
    refine ⟨this, _⟩,
    by_contra h',
    rw not_lt at h',
    rw ((least_ge_succ_eq_iff n).2 ⟨this, h'⟩) at h,
    norm_num at h },
  { rintro ⟨h₁, h₂⟩,
    refine le_antisymm (hitting_le _) (nat.succ_le_of_lt _),
    by_contra h,
    have : least_ge f r (n + 1) ω = least_ge f r n ω :=
      le_antisymm (h₁.symm ▸ not_lt.1 h) (hitting_mono n.le_succ),
    rw h₁ at this,
    refine not_lt.2 _ h₂,
    refine this ▸ hitting_mem_set_of_hitting_lt _,
    rw [← least_ge, this],
    exact n.lt_succ_self },
end

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

lemma least_ge_apply_eq_stopped_value (f : ℕ → Ω → ℝ) (π : Ω → ℕ) (r : ℝ) (ω : Ω)
  {n : ℕ} (hπn : ∀ ω, π ω ≤ n) :
  f (least_ge f r (π ω) ω) ω = stopped_value f (λ ω, min (π ω) (least_ge f r n ω)) ω :=
by { rw least_ge_eq_min _ _ _ hπn, simp_rw [stopped_value], }

lemma stopped_value_stopped_value_least_ge (f : ℕ → Ω → ℝ) (π : Ω → ℕ) (r : ℝ)
  {n : ℕ} (hπn : ∀ ω, π ω ≤ n) :
  stopped_value (λ i, stopped_value f (least_ge f r i)) π
    = (λ ω, stopped_value f (λ ω, min (π ω) (least_ge f r n ω)) ω) :=
begin
  ext1 ω,
  exact least_ge_apply_eq_stopped_value f π r ω hπn,
end

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
  { exact λ i, integrable_stopped_value ((hf.adapted.is_stopping_time_least_ge _ _))
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

lemma snorm_one_le_of_le {r : ℝ≥0} {f : Ω → ℝ}
  (hfint : integrable f μ) (hfint' : 0 ≤ μ[f]) (hf : ∀ᵐ ω ∂μ, f ω ≤ r) :
  snorm f 1 μ ≤ 2 * μ set.univ * r :=
begin
  by_cases hr : r = 0,
  { suffices : f =ᵐ[μ] 0,
    { rw [snorm_congr_ae this, snorm_zero, hr, ennreal.coe_zero, mul_zero],
      exact le_rfl },
    rw [hr, nonneg.coe_zero] at hf,
    have hnegf : μ[-f] = 0,
    { rw [integral_neg', neg_eq_zero],
      exact le_antisymm (integral_nonpos_of_ae hf) hfint' },
    have := (integral_eq_zero_iff_of_nonneg_ae _ hfint.neg).1 hnegf,
    { filter_upwards [this] with ω hω,
      rwa [pi.neg_apply, pi.zero_apply, neg_eq_zero] at hω },
    { filter_upwards [hf] with ω hω,
      rwa [pi.zero_apply, pi.neg_apply, right.nonneg_neg_iff] } },
  by_cases hμ : is_finite_measure μ,
  swap,
  { have : μ set.univ = ∞,
    { by_contra hμ',
      exact hμ (is_finite_measure.mk $ lt_top_iff_ne_top.2 hμ') },
    rw [this, ennreal.mul_top, if_neg, ennreal.top_mul, if_neg],
    { exact le_top },
    { simp [hr] },
    { norm_num } },
  haveI := hμ,
  rw [integral_eq_integral_pos_part_sub_integral_neg_part hfint, sub_nonneg] at hfint',
  have hposbdd : ∫ ω, max (f ω) 0 ∂μ ≤ (μ set.univ).to_real • r,
  { rw ← integral_const,
    refine integral_mono_ae hfint.real_to_nnreal (integrable_const r) _,
    filter_upwards [hf] with ω hω using real.to_nnreal_le_iff_le_coe.2 hω },
  rw [mem_ℒp.snorm_eq_integral_rpow_norm one_ne_zero ennreal.one_ne_top
      (mem_ℒp_one_iff_integrable.2 hfint),
    ennreal.of_real_le_iff_le_to_real (ennreal.mul_ne_top
      (ennreal.mul_ne_top ennreal.two_ne_top $ @measure_ne_top _ _ _ hμ _) ennreal.coe_ne_top)],
  simp_rw [ennreal.one_to_real, inv_one, real.rpow_one, real.norm_eq_abs,
    ← max_zero_add_max_neg_zero_eq_abs_self, ← real.coe_to_nnreal'],
  rw integral_add hfint.real_to_nnreal,
  { simp only [real.coe_to_nnreal', ennreal.to_real_mul, ennreal.to_real_bit0,
    ennreal.one_to_real, ennreal.coe_to_real] at hfint' ⊢,
    refine (add_le_add_left hfint' _).trans _,
    rwa [← two_mul, mul_assoc, mul_le_mul_left (two_pos : (0 : ℝ) < 2)] },
  { exact hfint.neg.sup (integrable_zero _ _ μ) }
end

lemma snorm_one_le_of_le' {r : ℝ} {f : Ω → ℝ}
  (hfint : integrable f μ) (hfint' : 0 ≤ μ[f]) (hf : ∀ᵐ ω ∂μ, f ω ≤ r) :
  snorm f 1 μ ≤ 2 * μ set.univ * ennreal.of_real r :=
begin
  refine snorm_one_le_of_le hfint hfint' _,
  simp only [real.coe_to_nnreal', le_max_iff],
  filter_upwards [hf] with ω hω using or.inl hω,
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
    rw set.mem_range at hω,
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
begin
  filter_upwards [hf.bdd_above_range_iff_bdd_below_range hbdd] with ω hω htop using
    unbounded_of_tendsto_at_top htop (hω.2 $ bdd_below_range_of_tendsto_at_top_at_top htop),
end

lemma martingale.ae_not_tendsto_at_top_at_bot [is_finite_measure μ]
  (hf : martingale f ℱ μ) (hbdd : ∀ᵐ ω ∂μ, ∀ i, |f (i + 1) ω - f i ω| ≤ R) :
  ∀ᵐ ω ∂μ, ¬ tendsto (λ n, f n ω) at_top at_bot :=
begin
  filter_upwards [hf.bdd_above_range_iff_bdd_below_range hbdd] with ω hω htop using
    unbounded_of_tendsto_at_bot htop (hω.1 $ bdd_above_range_of_tendsto_at_top_at_bot htop),
end

namespace borel_cantelli

/-- Auxiliary definition required to prove Lévy's generalization of the Borel-Cantelli lemmas.
The sum of the differences of the indicator functions with their conditional expectation forms a
martingale satisfying the conditions of the one sided martingale bound. -/
noncomputable
def mgale (ℱ : filtration ℕ m0) (μ : measure Ω) (s : ℕ → set Ω) (n : ℕ) : Ω → ℝ :=
∑ k in finset.range n, ((s (k + 1)).indicator 1 - μ[(s (k + 1)).indicator 1 | ℱ k])

variables {s : ℕ → set Ω}

lemma mgale_succ (n : ℕ) :
  mgale ℱ μ s (n + 1) =
    mgale ℱ μ s n + ((s (n + 1)).indicator 1 - μ[(s (n + 1)).indicator 1 | ℱ n]) :=
begin
  rw [mgale, finset.sum_range_succ],
  refl,
end

lemma adapted_mgale (hs : ∀ n, measurable_set[ℱ n] (s n)) :
  adapted ℱ (mgale ℱ μ s) :=
λ n, finset.strongly_measurable_sum' _ (λ k hk, (strongly_measurable_one.indicator
  (ℱ.mono (nat.succ_le_of_lt (finset.mem_range.1 hk)) _ (hs _))).sub
  (strongly_measurable_condexp.mono (ℱ.mono (finset.mem_range.1 hk).le)))

variables [is_finite_measure μ]

lemma integrable_mgale (hs : ∀ n, measurable_set[ℱ n] (s n)) (n : ℕ) :
  integrable (mgale ℱ μ s n) μ :=
integrable_finset_sum' _ (λ k hk,
  ((integrable_indicator_iff (ℱ.le (k + 1) _ (hs $ k + 1))).2
  (integrable_const 1).integrable_on).sub integrable_condexp)

lemma martingale_mgale
  (μ : measure Ω) [is_finite_measure μ] (hs : ∀ n, measurable_set[ℱ n] (s n)) :
  martingale (mgale ℱ μ s) ℱ μ :=
begin
  refine martingale_nat (adapted_mgale hs) (integrable_mgale hs)
    (λ n, eventually_eq.symm $ (condexp_finset_sum _).trans $
    (@eventually_eq_sum _ _ _ _ _ _ _
    (λ k, (μ[(s (k + 1)).indicator 1|ℱ n] - μ[(s (k + 1)).indicator 1|ℱ k])) _).trans _),
  { intros k hk,
    exact ((integrable_indicator_iff (ℱ.le (k + 1) _ (hs $ k + 1))).2
      (integrable_const 1).integrable_on).sub integrable_condexp },
  { intros k hk,
    rw finset.mem_range_succ_iff at hk,
    refine (condexp_sub ((integrable_indicator_iff (ℱ.le (k + 1) _ (hs $ k + 1))).2
      (integrable_const 1).integrable_on) integrable_condexp).trans
      ((ae_eq_refl _).sub _),
    rw (condexp_of_strongly_measurable (ℱ.le _)
      (strongly_measurable.mono strongly_measurable_condexp (ℱ.mono hk)) integrable_condexp),
    apply_instance },
  simp_rw [finset.sum_range_succ, sub_self, add_zero, mgale],
  refine eventually_eq_sum (λ i hi, eventually_eq.sub _ $ ae_eq_refl _),
  rw [finset.mem_range, ← nat.succ_le_iff] at hi,
  rw condexp_of_strongly_measurable (ℱ.le _)
    (strongly_measurable_one.indicator (ℱ.mono hi _ $ hs _)),
  { exact (integrable_indicator_iff (ℱ.le _ _ (hs $ _))).2 (integrable_const 1).integrable_on },
  { apply_instance },
end

lemma mgale_diff_le (hs : ∀ n, measurable_set[ℱ n] (s n)) (n : ℕ) :
  ∀ᵐ ω ∂μ, |mgale ℱ μ s (n + 1) ω - mgale ℱ μ s n ω| ≤ 1 :=
begin
  simp_rw [mgale, finset.sum_apply, finset.sum_range_succ_sub_sum],
  have h₁ : μ[(s (n + 1)).indicator 1|ℱ n] ≤ᵐ[μ] 1,
  { change _ ≤ᵐ[μ] (λ ω, 1 : Ω → ℝ),
    rw ← @condexp_const _ _ _ _ _ _ _ μ (ℱ.le n) (1 : ℝ),
    refine condexp_mono ((integrable_indicator_iff (ℱ.le _ _ (hs $ _))).2
      (integrable_const 1).integrable_on) (integrable_const 1)
      (eventually_of_forall $ λ ω, set.indicator_le_self' (λ _ _, zero_le_one) ω) },
  have h₂ : (0 : Ω → ℝ) ≤ᵐ[μ] μ[(s (n + 1)).indicator 1|ℱ n],
  { rw ← @condexp_zero Ω ℝ _ _ _ (ℱ n) _ μ,
    exact condexp_mono (integrable_zero _ _ _)
      ((integrable_indicator_iff (ℱ.le _ _ (hs $ _))).2 (integrable_const 1).integrable_on)
      (eventually_of_forall $ λ ω, set.indicator_nonneg (λ _ _, zero_le_one) _) },
  filter_upwards [h₁, h₂] with ω hω₁ hω₂,
  rw [abs_le, neg_le, pi.sub_apply, neg_sub, tsub_le_iff_right, tsub_le_iff_right,
    add_comm (1 : ℝ), add_comm (1 : ℝ)],
  exact ⟨le_add_of_nonneg_of_le (set.indicator_nonneg (λ _ _, zero_le_one) _) hω₁,
    le_add_of_nonneg_of_le hω₂ (set.indicator_le' (λ _ _, le_rfl) (λ _ _, zero_le_one) ω)⟩,
end

lemma mgale_diff_le' (hs : ∀ n, measurable_set[ℱ n] (s n)) :
  ∀ᵐ ω ∂μ, ∀ n, |mgale ℱ μ s (n + 1) ω - mgale ℱ μ s n ω| ≤ (1 : ℝ≥0) :=
begin
  rw [ae_all_iff, nonneg.coe_one],
  exact mgale_diff_le hs ,
end

lemma limsup_eq_tendsto_sum_indicator_at_top (s : ℕ → set Ω) :
  limsup at_top s =
    {ω | tendsto (λ n, ∑ k in finset.range n, (s (k + 1)).indicator (1 : Ω → ℕ) ω) at_top at_top} :=
begin
  ext ω,
  simp only [limsup_eq_infi_supr_of_nat, ge_iff_le, set.supr_eq_Union,
      set.infi_eq_Inter, set.mem_Inter, set.mem_Union, exists_prop],
  split,
  { intro hω,
    refine tendsto_at_top_at_top_of_monotone' (λ n m hnm, finset.sum_mono_set_of_nonneg
      (λ i, set.indicator_nonneg (λ _ _, zero_le_one) _) (finset.range_mono hnm)) _,
    rintro ⟨i, h⟩,
    simp only [mem_upper_bounds, set.mem_range, forall_exists_index, forall_apply_eq_imp_iff'] at h,
    induction i with k hk,
    { obtain ⟨j, hj₁, hj₂⟩ := hω 1,
      refine not_lt.2 (h $ j + 1) (lt_of_le_of_lt
        (finset.sum_const_zero.symm : 0 = ∑ k in finset.range (j + 1), 0).le _),
      refine finset.sum_lt_sum (λ m _, set.indicator_nonneg (λ _ _, zero_le_one) _)
        ⟨j - 1, finset.mem_range.2 (lt_of_le_of_lt (nat.sub_le _ _) j.lt_succ_self), _⟩,
      rw [nat.sub_add_cancel hj₁, set.indicator_of_mem hj₂],
      exact zero_lt_one },
    { rw imp_false at hk,
      push_neg at hk,
      obtain ⟨i, hi⟩ := hk,
      obtain ⟨j, hj₁, hj₂⟩ := hω (i + 1),
      replace hi : ∑ k in finset.range i, (s (k + 1)).indicator 1 ω = k + 1 := le_antisymm (h i) hi,
      refine not_lt.2 (h $ j + 1) _,
      rw [← finset.sum_range_add_sum_Ico _ (i.le_succ.trans (hj₁.trans j.le_succ)), hi],
      refine lt_add_of_pos_right _ _,
      rw (finset.sum_const_zero.symm : 0 = ∑ k in finset.Ico i (j + 1), 0),
      refine finset.sum_lt_sum (λ m _, set.indicator_nonneg (λ _ _, zero_le_one) _)
        ⟨j - 1, finset.mem_Ico.2
        ⟨(nat.le_sub_iff_right (le_trans ((le_add_iff_nonneg_left _).2 zero_le') hj₁)).2 hj₁,
          lt_of_le_of_lt (nat.sub_le _ _) j.lt_succ_self⟩, _⟩,
      rw [nat.sub_add_cancel (le_trans ((le_add_iff_nonneg_left _).2 zero_le') hj₁),
        set.indicator_of_mem hj₂],
      exact zero_lt_one } },
  { rintro hω i,
    rw [set.mem_set_of_eq, tendsto_at_top_at_top] at hω,
    by_contra hcon,
    push_neg at hcon,
    obtain ⟨j, h⟩ := hω (i + 1),
    have : ∑ k in finset.range j, (s (k + 1)).indicator 1 ω ≤ i,
    { have hle : ∀ j ≤ i, ∑ k in finset.range j, (s (k + 1)).indicator 1 ω ≤ i,
      { refine λ j hij, (finset.sum_le_card_nsmul _ _ _ _ : _ ≤ (finset.range j).card • 1).trans _,
        { exact λ m hm, set.indicator_apply_le' (λ _, le_rfl) (λ _, zero_le_one) },
        { simpa only [finset.card_range, algebra.id.smul_eq_mul, mul_one] } },
      by_cases hij : j < i,
      { exact hle _ hij.le },
      { rw ← finset.sum_range_add_sum_Ico _ (not_lt.1 hij),
        suffices : ∑ k in finset.Ico i j, (s (k + 1)).indicator 1 ω = 0,
        { rw [this, add_zero],
          exact hle _ le_rfl },
        rw finset.sum_eq_zero (λ m hm, _),
        exact set.indicator_of_not_mem (hcon _ $ (finset.mem_Ico.1 hm).1.trans m.le_succ) _ } },
    exact not_le.2 (lt_of_lt_of_le i.lt_succ_self $ h _ le_rfl) this }
end

lemma limsup_eq_tendsto_sum_indicator_at_top' (s : ℕ → set Ω) :
  limsup at_top s =
    {ω | tendsto (λ n, ∑ k in finset.range n, (s (k + 1)).indicator (1 : Ω → ℝ) ω) at_top at_top} :=
begin
  rw limsup_eq_tendsto_sum_indicator_at_top s,
  ext ω,
  simp only [set.mem_set_of_eq],
  rw (_ : (λ n, ∑ k in finset.range n, (s (k + 1)).indicator (1 : Ω → ℝ) ω) =
    (λ n, ↑(∑ k in finset.range n, (s (k + 1)).indicator (1 : Ω → ℕ) ω))),
  { exact tendsto_coe_nat_at_top_iff.symm },
  { ext n,
    simp only [set.indicator, pi.one_apply, finset.sum_boole, nat.cast_id] }
end

end borel_cantelli

open borel_cantelli

lemma tendsto_sum_indicator_at_top_iff
  (μ : measure Ω) [is_finite_measure μ] {s : ℕ → set Ω} (hs : ∀ n, measurable_set[ℱ n] (s n)) :
  ∀ᵐ ω ∂μ,
    tendsto (λ n, ∑ k in finset.range n, (s (k + 1)).indicator (1 : Ω → ℝ) ω) at_top at_top ↔
    tendsto (λ n, ∑ k in finset.range n, μ[(s (k + 1)).indicator (1 : Ω → ℝ) | ℱ k] ω)
      at_top at_top :=
begin
  have h₁ := (martingale_mgale μ hs).ae_not_tendsto_at_top_at_top (mgale_diff_le' hs),
  have h₂ := (martingale_mgale μ hs).ae_not_tendsto_at_top_at_bot (mgale_diff_le' hs),
  have h₃ : ∀ᵐ ω ∂μ, ∀ k, (0 : ℝ) ≤ μ[(s (k + 1)).indicator 1|ℱ k] ω,
  { rw ae_all_iff,
    exact λ n, condexp_nonneg (eventually_of_forall $ set.indicator_nonneg $ λ _ _, zero_le_one) },
  filter_upwards [h₁, h₂, h₃] with ω hω₁ hω₂ hω₃,
  split; intro ht,
  { refine tendsto_at_top_at_top_of_monotone'
      (λ n m hnm, finset.sum_mono_set_of_nonneg hω₃ $ finset.range_mono hnm) _,
    rintro ⟨b, hbdd⟩,
    rw ← tendsto_neg_at_bot_iff at ht,
    simp_rw [mgale, finset.sum_apply, pi.sub_apply, finset.sum_sub_distrib, sub_eq_add_neg] at hω₁,
    exact hω₁ (tendsto_at_top_add_right_of_le _ (-b)
      ((tendsto_neg_at_bot_iff at_top).1 ht) $ λ n, neg_le_neg (hbdd ⟨n, rfl⟩)) },
  { refine tendsto_at_top_at_top_of_monotone'
      (λ n m hnm, finset.sum_mono_set_of_nonneg (λ i, set.indicator_nonneg (λ _ _, zero_le_one) _) $
      finset.range_mono hnm) _,
    rintro ⟨b, hbdd⟩,
    simp_rw [mgale, finset.sum_apply, pi.sub_apply, finset.sum_sub_distrib, sub_eq_add_neg] at hω₂,
    exact hω₂ (tendsto_at_bot_add_left_of_ge _ b (λ n, hbdd ⟨n, rfl⟩) $
      (tendsto_neg_at_bot_iff at_top).2 ht) },
end

/-- **Lévy's generalization of the Borel-Cantelli lemma**: given a sequence of sets `s` and a
filtration `ℱ` such that for all `n`, `s n` is `ℱ n`-measurable, `at_top.limsup s` is almost
everywhere equal to the set for which `∑ k, ℙ(s (k + 1) | ℱ k) = ∞`. -/
theorem ae_mem_limsup_at_top_iff [is_finite_measure μ]
  {s : ℕ → set Ω} (hs : ∀ n, measurable_set[ℱ n] (s n)) :
  ∀ᵐ ω ∂μ, ω ∈ limsup at_top s ↔
    tendsto (λ n, ∑ k in finset.range n, μ[(s (k + 1)).indicator (1 : Ω → ℝ) | ℱ k] ω)
      at_top at_top :=
(borel_cantelli.limsup_eq_tendsto_sum_indicator_at_top' s).symm ▸
  tendsto_sum_indicator_at_top_iff μ hs

end measure_theory
