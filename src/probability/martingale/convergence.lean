/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import probability.martingale.upcrossing
import measure_theory.function.uniform_integrable

/-!

# Martingale convergence theorems

The martingale convergence theorems are a collection of theorems characterizing the convergence
of a martingale provided it satisfy some boundedness conditions. In particular, we have proved the
almost everywhere martingale convergence theorem which states that, given a L¹-bounded
submartingale adapted to the filtration `ℱ`, it converges almost everywhere to an integrable
function which is measurable with respect to the σ-algebra `⨆ n, ℱ n`.

## Main results

* `measure_theory.submartingale.exists_mem_ℒ1_ae_tendsto_of_bdd`: a L¹-bounded submartingale
  adapted to the filtration `ℱ` converges almost everywhere to an integrable function which is
  measurable with respect to the σ-algebra `⨆ n, ℱ n`.

-/

open topological_space filter
open_locale nnreal ennreal measure_theory probability_theory big_operators topological_space

namespace measure_theory

variables {α ι : Type*} {m0 : measurable_space α} {μ : measure α} {ℱ : filtration ℕ m0}
variables {a b : ℝ} {f : ℕ → α → ℝ} {x : α} {R : ℝ≥0}

/-!

### Almost everywhere martingale convergence theorem

We will now prove almost everywhere the martingale convergence theorem.

The a.e. martingale convergence theorem states: if `f` is a L¹-bounded `ℱ`-submartingale, then
it converges almost everywhere to a integrable function which is measurable with respect to
the σ-algebra `ℱ∞ := ⨆ n, ℱ n`.

Mathematically, we proceed by first noting that a real sequence $(x_n)$ converges if
(a) $\limsup_{n \to \infty} |x_n| < \infty$, (b) for all $a < b \in \mathbb{Q}$ we have the
number of upcrossings of $(x_n)$ from below $a$ to above $b$ is finite.
Thus, for all $x$ satisfying $\limsup_{n \to \infty} |f_n(x)| < \infty$ and the number of
upcrossings of $(f_n(x))$ from below $a$ to above $b$ is finite for all $a < b \in \mathbb{Q}$,
we have $(f_n(x))$ is convergent.

Hence, assuming $(f_n)$ is L¹-bounded, using Fatou's lemma, we have
$$
  \mathbb{E] \limsup_{n \to \infty} |f_n| \le \limsup_{n \to \infty} \mathbb{E}|f_n| < \infty
$$
implying $\limsup_{n \to \infty} |f_n| < \infty$ a.e. Furthermore, by the upcrossing estimate,
the number of upcrossings is finite almost everywhere implying $f$ converges pointwise almost
everywhere.

Thus, denoting $g$ the a.e. limit of $(f_n)$, $g$ is $\mathcal{F}_\infty$-measurable as for all
$n$, $f_n$ is $\mathcal{F}_n$-measurable and $\mathcal{F}_n \le \mathcal{F}_\infty$. Finally, $g$
is integrable as $|g| \le \liminf_{n \to \infty} |f_n|$ so
$$
  \mathbb{E}|g| \le \mathbb{E} \limsup_{n \to \infty} |f_n| \le
    \limsup_{n \to \infty} \mathbb{E}|f_n| < \infty
$$
as required.

Implementation wise, a previous PR has given us `tendsto_of_no_upcrossings` which showed that
a bounded sequence converges if it does not visit below $a$ and above $b$ infinitely often
for all $a, b ∈ s$ for some dense set $s$. So, we may skip the first step provided we can prove
that the realizations are bounded almost everywhere. Indeed, suppose $(|f_n(x)|)$ is not bounded,
then either $f_n(x) \to \pm \infty$ or one of $\limsup f_n(x)$ or $\liminf f_n(x)$ equals
$\pm \infty$ while the other is finite. But the first case contradicts $\liminf |f_n(x)| < \infty$
while the second case contradicts finite upcrossings.

-/

/-- If a stochastic process has bounded upcrossing from below `a` to above `b`,
then it does not frequently visit both below `a` and above `b`. -/
lemma not_frequently_of_upcrossing_lt_top (hab : a < b) (hx : upcrossing a b f x ≠ ∞) :
  ¬((∃ᶠ n in at_top, f n x < a) ∧ (∃ᶠ n in at_top, b < f n x)) :=
begin
  rw [← lt_top_iff_ne_top, upcrossing_lt_top_iff] at hx,
  replace hx : ∃ k, ∀ N, upcrossing_before a b f N x < k,
  { obtain ⟨k, hk⟩ := hx,
    exact ⟨k + 1, λ N, lt_of_le_of_lt (hk N) k.lt_succ_self⟩ },
  rintro ⟨h₁, h₂⟩,
  rw frequently_at_top at h₁ h₂,
  refine not_not.2 hx _,
  push_neg,
  intro k,
  induction k with k ih,
  { simp only [zero_le', exists_const] },
  { obtain ⟨N, hN⟩ := ih,
    obtain ⟨N₁, hN₁, hN₁'⟩ := h₁ N,
    obtain ⟨N₂, hN₂, hN₂'⟩ := h₂ N₁,
    exact ⟨(N₂ + 1), nat.succ_le_of_lt $ lt_of_le_of_lt hN
      (upcrossing_lt_upcrossing_of_exists_upcrossing hab hN₁ hN₁' hN₂ hN₂')⟩ }
end

/-- A stochastic process that frequently visits below `a` and above `b` have infinite
upcrossings. -/
lemma upcrossing_eq_top_of_frequently_lt (hab : a < b)
  (h₁ : ∃ᶠ n in at_top, f n x < a) (h₂ : ∃ᶠ n in at_top, b < f n x) :
  upcrossing a b f x = ∞ :=
classical.by_contradiction (λ h, not_frequently_of_upcrossing_lt_top hab h ⟨h₁, h₂⟩)

lemma exists_frequently_lt_of_liminf_ne_top
  {x : ℕ → ℝ} (hx : at_top.liminf (λ n, (∥x n∥₊ : ℝ≥0∞)) ≠ ∞) :
  ∃ R, ∃ᶠ n in at_top, x n < R :=
begin
  by_contra h,
  simp_rw [not_exists, not_frequently, not_lt, eventually_at_top] at h,
  refine hx (ennreal.eq_top_of_forall_nnreal_le $ λ r, _),
  obtain ⟨N, hN⟩ := h r,
  exact le_Liminf_of_le (by is_bounded_default) (eventually_at_top.2
    ⟨N, λ n hn, ennreal.coe_le_coe.2 $ nnreal.coe_le_coe.1 $ (hN n hn).trans (le_abs_self _)⟩),
end

lemma exists_frequently_lt_of_liminf_ne_top'
  {x : ℕ → ℝ} (hx : at_top.liminf (λ n, (∥x n∥₊ : ℝ≥0∞)) ≠ ∞) :
  ∃ R, ∃ᶠ n in at_top, R < x n :=
begin
  by_contra h,
  simp_rw [not_exists, not_frequently, not_lt, eventually_at_top] at h,
  refine hx (ennreal.eq_top_of_forall_nnreal_le $ λ r, _),
  obtain ⟨N, hN⟩ := h (-r),
  refine le_Liminf_of_le (by is_bounded_default) (eventually_at_top.2
    ⟨N, λ n hn, ennreal.coe_le_coe.2 $ nnreal.coe_le_coe.1 $ (le_neg.1 $ hN n hn).trans _⟩),
  rw [coe_nnnorm, real.norm_eq_abs, ← abs_neg],
  exact le_abs_self _,
end

lemma exists_upcrossings_of_not_bounded_under
  (hf : at_top.liminf (λ n, (∥f n x∥₊ : ℝ≥0∞)) ≠ ∞)
  (hbdd : ¬ is_bounded_under (≤) at_top (λ n, |f n x|)) :
  ∃ a b : ℚ, a < b ∧ (∃ᶠ n in at_top, f n x < a) ∧ (∃ᶠ n in at_top, ↑b < f n x) :=
begin
  rw [is_bounded_under_le_abs, not_and_distrib] at hbdd,
  obtain hbdd | hbdd := hbdd,
  { obtain ⟨R, hR⟩ := exists_frequently_lt_of_liminf_ne_top hf,
    obtain ⟨q, hq⟩ := exists_rat_gt R,
    refine ⟨q, q + 1, (lt_add_iff_pos_right _).2 zero_lt_one, _, _⟩,
    { rw frequently_at_top at hR ⊢,
      intro a,
      obtain ⟨b, hb₁, hb₂⟩ := hR a,
      exact ⟨b, hb₁, hb₂.trans hq⟩ },
    { simp only [is_bounded_under, is_bounded, eventually_map, eventually_at_top,
        ge_iff_le, not_exists, not_forall, not_le, exists_prop] at hbdd,
      rw frequently_at_top,
      exact λ a, let ⟨b, hb₁, hb₂⟩ := hbdd ↑(q + 1) a in ⟨b, hb₁, hb₂⟩ } },
  { obtain ⟨R, hR⟩ := exists_frequently_lt_of_liminf_ne_top' hf,
    obtain ⟨q, hq⟩ := exists_rat_lt R,
    refine ⟨q - 1, q, (sub_lt_self_iff _).2 zero_lt_one, _, _⟩,
    { simp only [is_bounded_under, is_bounded, eventually_map, eventually_at_top,
        ge_iff_le, not_exists, not_forall, not_le, exists_prop] at hbdd,
      rw frequently_at_top,
      exact λ a, let ⟨b, hb₁, hb₂⟩ := hbdd ↑(q - 1) a in ⟨b, hb₁, hb₂⟩ },
    { rw frequently_at_top at hR ⊢,
      intro a,
      obtain ⟨b, hb₁, hb₂⟩ := hR a,
      exact ⟨b, hb₁, hq.trans hb₂⟩ } }
end

/-- A realization of a stochastic process with bounded upcrossings and bounded limit infimums is
convergent.

We use the spelling `< ∞` instead of the standard `≠ ∞` in the assumptions since it is difficult
to manipulate under binders. -/
lemma tendsto_of_uncrossing_lt_top {x : α}
  (hf₁ : at_top.liminf (λ n, (∥f n x∥₊ : ℝ≥0∞)) < ∞)
  (hf₂ : ∀ a b : ℚ, a < b → upcrossing a b f x < ∞) :
  ∃ c, tendsto (λ n, f n x) at_top (𝓝 c) :=
begin
  by_cases h : is_bounded_under (≤) at_top (λ n, |f n x|),
  { rw is_bounded_under_le_abs at h,
    refine tendsto_of_no_upcrossings rat.dense_range_cast _ h.1 h.2,
    { intros a ha b hb hab,
      obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := ⟨ha, hb⟩,
      exact not_frequently_of_upcrossing_lt_top hab (hf₂ a b (rat.cast_lt.1 hab)).ne } },
  { obtain ⟨a, b, hab, h₁, h₂⟩ := exists_upcrossings_of_not_bounded_under hf₁.ne h,
    exact false.elim ((hf₂ a b hab).ne
      (upcrossing_eq_top_of_frequently_lt (rat.cast_lt.2 hab) h₁ h₂)) }
end

lemma liminf_at_top_ae_bdd_of_snorm_bdd
  (hfmeas : ∀ n, measurable (f n)) (hbdd : ∀ n, snorm (f n) 1 μ ≤ R) :
  ∀ᵐ x ∂μ, at_top.liminf (λ n, (∥f n x∥₊ : ℝ≥0∞)) < ∞ :=
begin
  refine ae_lt_top (measurable_liminf (λ n, (hfmeas n).nnnorm.coe_nnreal_ennreal))
    (lt_of_le_of_lt (lintegral_liminf_le (λ n, (hfmeas n).nnnorm.coe_nnreal_ennreal))
    (lt_of_le_of_lt _ (ennreal.coe_lt_top : ↑R < ∞))).ne,
  simp_rw [← snorm_one_eq_lintegral_nnnorm, liminf_eq, eventually_at_top],
  exact Sup_le (λ b ⟨a, ha⟩, (ha a le_rfl).trans (hbdd _)),
end

variables [is_finite_measure μ]

/-- An L¹-bounded submartingale has bounded upcrossings almost everywhere. -/
lemma submartingale.upcrossing_ae_lt_top'
  (hf : submartingale f ℱ μ) (hbdd : ∀ n, snorm (f n) 1 μ ≤ R) (hab : a < b) :
  ∀ᵐ x ∂μ, upcrossing a b f x < ∞ :=
begin
  refine ae_lt_top (hf.adapted.measurable_upcrossing hab) _,
  have := hf.mul_lintegral_upcrossing_le_lintegral_pos_part a b,
  rw [mul_comm, ← ennreal.le_div_iff_mul_le] at this,
  { refine (lt_of_le_of_lt this (ennreal.div_lt_top _ _)).ne,
    { have hR' : ∀ n, ∫⁻ (x : α), ∥f n x - a∥₊ ∂μ ≤ R + ∥a∥₊ * μ set.univ,
      { simp_rw snorm_one_eq_lintegral_nnnorm at hbdd,
        intro n,
        refine (lintegral_mono _ : ∫⁻ x, ∥f n x - a∥₊ ∂μ ≤ ∫⁻ x, ∥f n x∥₊ + ∥a∥₊ ∂μ).trans _,
        { intro x,
          simp_rw [sub_eq_add_neg, ← nnnorm_neg a, ← ennreal.coe_add, ennreal.coe_le_coe],
          exact nnnorm_add_le _ _ },
        { simp_rw [ lintegral_add_right _ measurable_const, lintegral_const],
          exact add_le_add (hbdd _) le_rfl } },
      refine ne_of_lt (supr_lt_iff.2 ⟨R + ∥a∥₊ * μ set.univ, ennreal.add_lt_top.2
          ⟨ennreal.coe_lt_top, ennreal.mul_lt_top ennreal.coe_lt_top.ne (measure_ne_top _ _)⟩,
          λ n, le_trans _ (hR' n)⟩),
      refine lintegral_mono (λ x, _),
      rw [ennreal.of_real_le_iff_le_to_real, ennreal.coe_to_real, coe_nnnorm],
      by_cases hnonneg : 0 ≤ f n x - a,
      { rw [lattice_ordered_comm_group.pos_of_nonneg _ hnonneg,
          real.norm_eq_abs, abs_of_nonneg hnonneg] },
      { rw lattice_ordered_comm_group.pos_of_nonpos _ (not_le.1 hnonneg).le,
        exact norm_nonneg _ },
      { simp only [ne.def, ennreal.coe_ne_top, not_false_iff] } },
    { simp only [hab, ne.def, ennreal.of_real_eq_zero, sub_nonpos, not_le] } },
  { simp only [hab, ne.def, ennreal.of_real_eq_zero, sub_nonpos, not_le, true_or]},
  { simp only [ne.def, ennreal.of_real_ne_top, not_false_iff, true_or] }
end

lemma submartingale.upcrossing_ae_lt_top
  (hf : submartingale f ℱ μ) (hbdd : ∀ n, snorm (f n) 1 μ ≤ R) :
  ∀ᵐ x ∂μ, ∀ a b : ℚ, a < b → upcrossing a b f x < ∞ :=
begin
  suffices : ∀ a b : ℚ, a < b → ∀ᵐ x ∂μ, upcrossing a b f x < ∞,
  { simp_rw ae_iff at this ⊢,
    push_neg at this ⊢,
    rw set.set_of_exists,
    refine nonpos_iff_eq_zero.1 ((measure_Union_le _).trans
      (((tsum_eq_zero_iff ennreal.summable).2 (λ a, _)).le)),
    rw set.set_of_exists,
    refine nonpos_iff_eq_zero.1 ((measure_Union_le _).trans
      (((tsum_eq_zero_iff ennreal.summable).2 (λ b, _)).le)),
    rw set.set_of_and,
    by_cases hab : a < b,
    { simp only [hab, set.set_of_true, set.univ_inter, this a b] },
    { simp only [hab, set.set_of_false, set.empty_inter, measure_empty] } },
  rintro a b hab,
  exact hf.upcrossing_ae_lt_top' hbdd (rat.cast_lt.2 hab),
end

/-- An L¹-bounded submartingale converges almost everywhere. -/
lemma submartingale.exists_ae_tendsto_of_bdd
  (hf : submartingale f ℱ μ) (hbdd : ∀ n, snorm (f n) 1 μ ≤ R) :
  ∀ᵐ x ∂μ, ∃ c, tendsto (λ n, f n x) at_top (𝓝 c) :=
begin
  filter_upwards [hf.upcrossing_ae_lt_top hbdd, liminf_at_top_ae_bdd_of_snorm_bdd
    (λ n, (hf.strongly_measurable n).measurable.mono (ℱ.le n) le_rfl) hbdd] with x h₁ h₂,
  exact tendsto_of_uncrossing_lt_top h₂ h₁,
end

section PRed

lemma metric.cauchy_seq_iff'' {α β : Type*}
  [pseudo_metric_space α] [nonempty β] [semilattice_sup β] {u : β → α} :
  cauchy_seq u ↔ ∀ K : ℕ, ∃ N, ∀ n ≥ N, dist (u n) (u N) < (K + 1)⁻¹ :=
begin
  rw metric.cauchy_seq_iff',
  refine ⟨λ h K, h (K + 1)⁻¹ (inv_pos.2 K.cast_add_one_pos), λ h ε hε, _⟩,
  obtain ⟨K, hK⟩ := exists_nat_gt ε⁻¹,
  obtain ⟨N, hN⟩ := h K,
  refine ⟨N, λ n hn, lt_of_lt_of_le (hN n hn) _⟩,
  rw [inv_le (K.cast_add_one_pos : (0 : ℝ) < K + 1) hε, ← nat.cast_one, ← nat.cast_add],
  exact hK.le.trans (nat.cast_le.2 K.le_succ),
end

lemma measurable_set_exists_tendsto_at_top {α β ι : Type*} {m0 : measurable_space α}
  [measurable_space β] [pseudo_metric_space β] [opens_measurable_space β]
  [second_countable_topology β] [complete_space β] [nonempty ι] [semilattice_sup ι] [encodable ι]
  {f : ι → α → β} (hf : ∀ i, measurable (f i)) :
  measurable_set {x | ∃ c, tendsto (λ n, f n x) at_top (𝓝 c)} :=
begin
  simp_rw ← cauchy_map_iff_exists_tendsto,
  change measurable_set {x | cauchy_seq (λ n, f n x)},
  simp_rw metric.cauchy_seq_iff'',
  rw set.set_of_forall,
  refine measurable_set.Inter (λ K, _),
  rw set.set_of_exists,
  refine measurable_set.Union (λ N, _),
  rw set.set_of_forall,
  refine measurable_set.Inter (λ n, _),
  by_cases hNn : N ≤ n,
  { simp only [hNn, ge_iff_le, forall_true_left],
    exact measurable_set_lt (measurable.dist (hf n) (hf N)) measurable_const },
  { simp only [hNn, ge_iff_le, forall_false_left, set.set_of_true, measurable_set.univ] }
end

end PRed

lemma submartingale.exists_ae_trim_tendsto_of_bdd
  (hf : submartingale f ℱ μ) (hbdd : ∀ n, snorm (f n) 1 μ ≤ R) :
  ∀ᵐ x ∂(μ.trim (Sup_le (λ m ⟨n, hn⟩, hn ▸ ℱ.le _) : (⨆ n, ℱ n) ≤ m0)),
    ∃ c, tendsto (λ n, f n x) at_top (𝓝 c) :=
begin
  rw [ae_iff, trim_measurable_set_eq],
  { exact hf.exists_ae_tendsto_of_bdd hbdd },
  { exact measurable_set.compl (measurable_set_exists_tendsto_at_top (λ n,
      ((hf.strongly_measurable n).measurable.mono (le_Sup ⟨n, rfl⟩) le_rfl))) }
end

/-- **Almost everywhere martingale convergence theorem**: An L¹-bounded submartingale converges
almost everywhere to a L¹-function which is measurable with respect to `⨆ n, ℱ n`. -/
lemma submartingale.exists_mem_ℒ1_ae_tendsto_of_bdd
  (hf : submartingale f ℱ μ) (hbdd : ∀ n, snorm (f n) 1 μ ≤ R) :
  ∃ g : α → ℝ, mem_ℒp g 1 μ ∧ strongly_measurable[⨆ n, ℱ n] g ∧
  ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (𝓝 (g x)) :=
begin
  classical,
  set g' : α → ℝ := λ x, if h : ∃ c, tendsto (λ n, f n x) at_top (𝓝 c) then h.some else 0,
  have hle : (⨆ n, ℱ n) ≤ m0 := Sup_le (λ m ⟨n, hn⟩, hn ▸ ℱ.le _),
  have hg' : ∀ᵐ x ∂(μ.trim hle), tendsto (λ n, f n x) at_top (𝓝 (g' x)),
  { filter_upwards [hf.exists_ae_trim_tendsto_of_bdd hbdd] with x hx,
    simp_rw [g', dif_pos hx],
    exact hx.some_spec },
  have hg'm : @ae_strongly_measurable _ _ _ (⨆ n, ℱ n) g' (μ.trim hle) :=
    (@ae_measurable_of_tendsto_metrizable_ae' _ _ (⨆ n, ℱ n) _ _ _ _ _ _ _
      (λ n, ((hf.strongly_measurable n).measurable.mono
      (le_Sup ⟨n, rfl⟩ : ℱ n ≤ ⨆ n, ℱ n) le_rfl).ae_measurable) hg').ae_strongly_measurable,
  obtain ⟨g, hgm, hae⟩ := hg'm,
  have hg : ∀ᵐ x ∂μ.trim hle, tendsto (λ n, f n x) at_top (𝓝 (g x)),
  { filter_upwards [hae, hg'] with x hx hg'x,
    exact hx ▸ hg'x },
  refine ⟨g, ⟨(hgm.mono hle).ae_strongly_measurable, lt_of_le_of_lt (Lp.snorm_lim_le_liminf_snorm
      (λ n, ((hf.strongly_measurable n).measurable.mono (ℱ.le n) le_rfl).ae_strongly_measurable)
      g (measure_eq_zero_of_trim_eq_zero hle hg))
      (lt_of_le_of_lt _ (ennreal.coe_lt_top : ↑R < ∞))⟩,
    hgm, measure_eq_zero_of_trim_eq_zero hle hg⟩,
  simp_rw [liminf_eq, eventually_at_top],
  exact Sup_le (λ b ⟨a, ha⟩, (ha a le_rfl).trans (hbdd _)),
end

/-!

### L¹ martingale convergence theorem

We will now prove the L¹ martingale convergence theorems.

The L¹ martingale convergence theorem states that:
(a) if `f` is a uniformly integrable (in the probability sense) submartingale adapted to the
  filtration `ℱ`, it converges in L¹ to an integrable function `g` which is measurable with
  respect to `ℱ∞ := ⨆ n, ℱ n` and
(b) if `f` is actually a martingale, `f n = 𝔼[g | ℱ n]` almost everywhere.
(c) Finally, if `h` is integrable and measurable with respect to `ℱ∞`, `(𝔼[h | ℱ n])ₙ` is a
  uniformly integrable martingale which converges to `h` almost everywhere and in L¹.

The proof is quite simple. (a) follows directly from the a.e. martingale convergence theorem
and the Vitali convergence theorem. Mathematically, one first have to observe that uniform
integrability implies uniform boundedness in L¹. Indeed, if
$$
  \lim_{\lambda \to \infty} \sup_{n \ge 0} \mathbb{E}(|f_n|\mathbf{1}_{\{|f_n| > \lambda\}}) = 0,
$$
then there exists some $\lambda$ such that
$\sup_{n \ge 0} \mathbb{E}(|f_n|\mathbf{1}_{\{|f_n| > \lambda\}}) \le 1$. So,
$$
  \sup_{n \ge 0} \mathbb{E}|f_n| \le
    \sup_{n \ge 0} \mathbb{E}|f_n|\mathbf{1}_{\{|f_n| \le \lambda\}} +
    \sup_{n \ge 0} \mathbb{E}|f_n|\mathbf{1}_{\{|f_n| > \lambda\}} \le
    \lambda \mu(\Omega) + 1 < \infty.
$$
However, by the very definition we used for uniform integrability in the probability sense,
uniform integrability in Lean directly requires L¹ boundedness and so the above is unnecessary.

(b) follows since given $n$, we have for all $m \ge n$,
$$
  \|f_n - \mathbb{E}[g \mid \mathcal{F}_n]\|_1 =
    \|\mathbb{E}[f_m \mid \mathcal{F}_n] - \mathbb{E}[g \mid \mathcal{F}_n]\|_1 =
    \|\mathbb{E}[f_m - g \mid \mathcal{F}_n]\|_1 \le \|f_m - g\|_1
$$
where the inequality is due to the conditional Jensen's inequality. Thus, taking $m \to \infty$
provides the almost everywhere equality.

At the time of writting, we don't have the conditional Jensen's inequality yet. To avoid this,
we observe that as a function, the conditional expectation of a continuous linear functional and
thus, have bounded norm. Hence, if $f_n \to g$ in L¹, we have
$$
  \|\mathbb{E}[f_n - g \mid \mathcal{F}_n]\|_1 \le
    \|\mathbb{E}[\cdot \mid \mathcal{F}_n]\| \|f_n - g\|_1 \to 0
$$
as $n \to \infty$.

Finally, to prove (c), we define $f_n := \mathbb{E}[h \mid \mathcal{F}_n]$. It is clear that
$(f_n)_n$ is a martingale by the tower property for conditional expectations and so it suffices to
show $(f_n)_n$ is uniformly integrable in the probability sense. Indeed, as a single function is
uniformly integrable in the measure theory sense, for all $\epsilon > 0$, there exists some
$\delta > 0$ such that for all measurable set $A$ with $\mu(A) < δ$, we have
$\mathbb{E}|h|\mathbf{1}_A < \epsilon$. So, since for sufficently large $\lambda$, by the Markov
inequality, we have for all $n$,
$$
  \mu(|f_n| \ge \lambda) \le \lambda^{-1}\mathbb{E}|f_n| \le \lambda^{-1}\mathbb|g| < \delta,
$$
we have for sufficently large $\lambda$, for all $n$,
$$
  \mathbb{E}|f_n|\mathbf{1}_{|f_n| \ge \lambda} \le
    \mathbb|g|\mathbf{1}_{|f_n| \ge \lambda} < \epsilon
$$
where the first inequality follows as $|f_n| \le \mathbb{E}[|g| \mid \mathcal{F}_n]$ by the
conditional Jensen's inequality.

-/

/-- Part 1 of the **L¹ martingale convergence theorem**: a uniformly integrable submartingale
adapted to the filtration `ℱ` converges in L¹ to an integrable function which is measurable
with respect to the σ-algebra `⨆ n, ℱ n`. -/
lemma submartingale.exists_mem_ℒ1_tendsto_snorm
  (hf : submartingale f ℱ μ) (hbdd : uniform_integrable f 1 μ) :
  ∃ g : α → ℝ, mem_ℒp g 1 μ ∧ strongly_measurable[⨆ n, ℱ n] g ∧
  tendsto (λ n, snorm (f n - g) 1 μ) at_top (𝓝 0) :=
begin
  obtain ⟨R, hR⟩ := hbdd.2.2,
  obtain ⟨g, hg₁, hg₂, htends⟩ := hf.exists_mem_ℒ1_ae_tendsto_of_bdd hR,
  have hmeas : ∀ n, ae_strongly_measurable (f n) μ :=
    λ n, ((hf.strongly_measurable n).mono (ℱ.le _)).ae_strongly_measurable,
  exact ⟨g, hg₁, hg₂, tendsto_Lp_of_tendsto_in_measure _ le_rfl ennreal.one_ne_top
    hmeas hg₁ hbdd.2.1 (tendsto_in_measure_of_tendsto_ae hmeas htends)⟩,
end

lemma integrable.snorm_condexp_le_mul_norm
  {m : measurable_space α} {f : α → ℝ} (hf : integrable f μ) (hm : m ≤ m0) :
  snorm (μ[f | m]) 1 μ ≤
    ennreal.of_real (∥@condexp_L1_clm _ ℝ _ _ _ _ _ hm μ _∥ * ∥hf.to_L1 _∥) :=
begin
  refine le_trans _ (ennreal.of_real_le_of_real (continuous_linear_map.le_op_norm _ _)),
  rw [ennreal.le_of_real_iff_to_real_le
    (mem_ℒp_one_iff_integrable.2 integrable_condexp).snorm_lt_top.ne (norm_nonneg _),
    snorm_congr_ae (condexp_ae_eq_condexp_L1_clm hm hf), ← Lp.norm_def]
end

/-- If a martingale `f` adapted to `ℱ` converges in L¹ to `g`, then for all `n`, `f n` is almost
everywhere equal to `𝔼[g | ℱ n]`. -/
lemma martingale.eq_condexp_lim_of_tendsto_snorm
  (hf : martingale f ℱ μ) {g : α → ℝ} (hgℒ1 : mem_ℒp g 1 μ)
  (hgtends : tendsto (λ n, snorm (f n - g) 1 μ) at_top (𝓝 0)) (n : ℕ) :
  f n =ᵐ[μ] μ[g | ℱ n] :=
begin
  rw [← sub_ae_eq_zero, ← snorm_eq_zero_iff ((((hf.strongly_measurable n).mono (ℱ.le _)).sub
    (strongly_measurable_condexp.mono (ℱ.le _))).ae_strongly_measurable) one_ne_zero],
  have ht : tendsto (λ m, snorm (μ[f m - g | ℱ n]) 1 μ) at_top (𝓝 0),
  { have hint : ∀ m, integrable (f m - g) μ := λ m, (hf.integrable m).sub (hgℒ1.integrable le_rfl),
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _ (λ m, zero_le _)
      (λ m, (hint m).snorm_condexp_le_mul_norm (ℱ.le _)),
    rw [← ennreal.of_real_zero,
      ((mul_zero _).symm : 0 = ∥@condexp_L1_clm _ ℝ _ _ _ _ _ (ℱ.le n) μ _∥ * (0 : ℝ))],
    refine ennreal.tendsto_of_real (tendsto_const_nhds.mul _),
    rw [← ennreal.tendsto_to_real_iff
      (λ m, (mem_ℒp.snorm_lt_top $ mem_ℒp_one_iff_integrable.2 $ hint m).ne)
      ennreal.zero_ne_top, ennreal.zero_to_real] at hgtends,
    convert hgtends,
    ext m,
    rw ← Lp.norm_to_Lp,
    refl },
  have hev : ∀ m ≥ n, snorm (μ[f m - g | ℱ n]) 1 μ = snorm (f n - μ[g | ℱ n]) 1 μ,
  { refine λ m hm, snorm_congr_ae
      ((condexp_sub (hf.integrable m) (hgℒ1.integrable le_rfl)).trans _),
    filter_upwards [hf.2 n m hm] with x hx,
    simp only [hx, pi.sub_apply] },
  exact tendsto_nhds_unique (tendsto_at_top_of_eventually_const hev) ht,
end

/-- Part 2 of the **L¹ martingale convergence theorem**: a uniformly integrable martingale `f`
adapted to the filtration `ℱ` converges in L¹ to some integrable function `g` which is measurable
with respect to the σ-algebra `⨆ n, ℱ n`. Furthermore, for all `n`, `f n` is almost everywhere
equal to `𝔼[g | ℱ n]`. -/
lemma martingale.exists_mem_ℒ1_tendsto_snorm
  (hf : martingale f ℱ μ) (hbdd : uniform_integrable f 1 μ) :
  ∃ g : α → ℝ, mem_ℒp g 1 μ ∧ strongly_measurable[⨆ n, ℱ n] g ∧ (∀ n, f n =ᵐ[μ] μ[g | ℱ n]) ∧
  tendsto (λ n, snorm (f n - g) 1 μ) at_top (𝓝 0) :=
let ⟨g, hg₁, hg₂, hg₃⟩ := hf.submartingale.exists_mem_ℒ1_tendsto_snorm hbdd in
  ⟨g, hg₁, hg₂, λ n, hf.eq_condexp_lim_of_tendsto_snorm hg₁ hg₃ n, hg₃⟩

#check martingale_condexp
#check unif_integrable

/-- Part 3 of the **L¹ martingale convergnce theorem**: TODO. -/
lemma martingale_condexp_uniform_integrable
  {g : α → ℝ} (hg : mem_ℒp g 1 μ) :
  uniform_integrable (λ n, μ[g | ℱ n]) 1 μ :=
begin
  refine uniform_integrable_of le_rfl ennreal.one_ne_top
    (λ n, strongly_measurable_condexp.mono (ℱ.le n)) (λ ε hε, _),
  obtain ⟨δ, hδ, h⟩ := hg.snorm_indicator_le μ le_rfl ennreal.one_ne_top hε,
  set C := (⟨δ, hδ.le⟩ : ℝ≥0)⁻¹ * (μ set.univ).to_nnreal,
  sorry,
end

/-
Uniform boundedness in Lᵖ → uniform integrability.
https://math.stackexchange.com/questions/729217/uniform-lp-bound-on-finite-measure-implies-uniform-integrability
-/

end measure_theory
