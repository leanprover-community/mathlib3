/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import probability.martingale.upcrossing
import measure_theory.function.uniform_integrable
import measure_theory.constructions.polish

/-!

# Martingale convergence theorems

The martingale convergence theorems are a collection of theorems characterizing the convergence
of a martingale provided it satisfy some boundedness conditions. This file contains the
almost everywhere martingale convergence theorem which provides an almost everywhere limit to
an L¹ bounded submartingale. It also contains the L¹ martingale convergence theorem which provides
an L¹ limit to a uniformly integrable submartingale.

## Main results

* `measure_theory.submartingale.exists_mem_ℒ1_ae_tendsto_of_bdd`: the almost everywhere martingale
  convergence theorem: a L¹-bounded submartingale adapted to the filtration `ℱ` converges almost
  everywhere to an integrable function which is measurable with respect to the σ-algebra `⨆ n, ℱ n`.
* `measure_theory.submartingale.exists_mem_ℒ1_tendsto_snorm`: part a of the L¹ martingale
  convergence theorem: a uniformly integrable submartingale adapted to the filtration `ℱ` converges
  almost everywhere and in L¹ to an integrable function which is measurable with respect to
  the σ-algebra `⨆ n, ℱ n`.
* `measure_theory.martingale.exists_mem_ℒ1_tendsto_snorm`: part b the L¹ martingale convergence
  theorem: a uniformly integrable martingale `f` adapted to the filtration `ℱ` converges almost
  everywhere and in L¹ to an integrable function `g` which is measurable with respect to the
  σ-algebra `⨆ n, ℱ n`. Furthermore, for all `n`, `f n` is almost everywhere equal to `𝔼[g | ℱ n]`.
* `measure_theory.mem_ℒp.tendsto_ae_condexp`: part c the L¹ martingale convergence theorem:
  given a `⨆ n, ℱ n`-measurable function `g` where `ℱ` is a filtration, `𝔼[g | ℱ n]` converges
  almost everywhere to `g`.
* `measure_theory.mem_ℒp.tendsto_snorm_condexp`: part c the L¹ martingale convergence theorem:
  given a `⨆ n, ℱ n`-measurable function `g` where `ℱ` is a filtration, `𝔼[g | ℱ n]` converges in
  L¹ to `g`.

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
  simp only [ae_all_iff, eventually_imp_distrib_left],
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

lemma submartingale.exists_ae_trim_tendsto_of_bdd
  (hf : submartingale f ℱ μ) (hbdd : ∀ n, snorm (f n) 1 μ ≤ R) :
  ∀ᵐ x ∂(μ.trim (Sup_le (λ m ⟨n, hn⟩, hn ▸ ℱ.le _) : (⨆ n, ℱ n) ≤ m0)),
    ∃ c, tendsto (λ n, f n x) at_top (𝓝 c) :=
begin
  rw [ae_iff, trim_measurable_set_eq],
  { exact hf.exists_ae_tendsto_of_bdd hbdd },
  { exact measurable_set.compl (@measurable_set_exists_tendsto _ _ _ _ _ _ (⨆ n, ℱ n) _ _ _ _ _
    (λ n, ((hf.strongly_measurable n).measurable.mono (le_Sup ⟨n, rfl⟩) le_rfl))) }
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
    \|\mathbb{E}[f_m - g \mid \mathcal{F}_n]\|_1 \le \|\|f_m - g\|_1.
$$
Thus, taking $m \to \infty$ provides the almost everywhere equality.

Finally, to prove (c), we define $f_n := \mathbb{E}[h \mid \mathcal{F}_n]$. It is clear that
$(f_n)_n$ is a martingale by the tower property for conditional expectations. Furthermore,
$(f_n)_n$ is uniformly integrable in the probability sense. Indeed, as a single function is
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
    \mathbb|g|\mathbf{1}_{|f_n| \ge \lambda} < \epsilon,
$$
implying $(f_n)_n$ is uniformly integrable. Now, to prove $f_n \to h$ almost everywhere and in
L¹, it suffices to show that $h = g$ almost everywhere where $g$ is the almost everywhere and L¹
limit of $(f_n)_n$ from part (b) of the theorem. By noting that, for all $s \in \mathcal{F}_n$,
we have
$$
  \mathbb{E}g\mathbf{1}_s = \mathbb{E}[\mathbb{E}[g \mid \mathcal{F}_n]\mathbf{1}_s] =
    \mathbb{E}[\mathbb{E}[h \mid \mathcal{F}_n]\mathbf{1}_s] = \mathbb{E}h\mathbf{1}_s
$$
where $\mathbb{E}[g \mid \mathcal{F}_n = \mathbb{E}[h \mid \mathcal{F}_n]$ almost everywhere
by part (b); the equality also holds for all $s \in \mathcal{F}_\infty$ by Dynkin's theorem.
Thus, as both $h$ and $g$ are $\mathcal{F}_\infty$-measurable, $h = g$ almost everywhere as
required.

-/

/-- Part a of the **L¹ martingale convergence theorem**: a uniformly integrable submartingale
adapted to the filtration `ℱ` converges a.e. and in L¹ to an integrable function which is
measurable with respect to the σ-algebra `⨆ n, ℱ n`. -/
lemma submartingale.exists_mem_ℒ1_tendsto_snorm
  (hf : submartingale f ℱ μ) (hunif : uniform_integrable f 1 μ) :
  ∃ g : α → ℝ, mem_ℒp g 1 μ ∧ strongly_measurable[⨆ n, ℱ n] g ∧
  tendsto (λ n, snorm (f n - g) 1 μ) at_top (𝓝 0) ∧
  ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (𝓝 (g x)) :=
begin
  obtain ⟨R, hR⟩ := hunif.2.2,
  obtain ⟨g, hg₁, hg₂, htends⟩ := hf.exists_mem_ℒ1_ae_tendsto_of_bdd hR,
  have hmeas : ∀ n, ae_strongly_measurable (f n) μ :=
    λ n, ((hf.strongly_measurable n).mono (ℱ.le _)).ae_strongly_measurable,
  exact ⟨g, hg₁, hg₂, tendsto_Lp_of_tendsto_in_measure _ le_rfl ennreal.one_ne_top
    hmeas hg₁ hunif.2.1 (tendsto_in_measure_of_tendsto_ae hmeas htends), htends⟩,
end

section PRed

lemma integrable.snorm_one_condexp_le_snorm {m : measurable_space α}
  {f : α → ℝ} (hf : integrable f μ) (hm : m ≤ m0) :
  snorm (μ[f | m]) 1 μ ≤ snorm f 1 μ :=
calc snorm (μ[f | m]) 1 μ ≤ snorm (μ[|f| | m]) 1 μ :
begin
  refine snorm_mono_ae _,
  filter_upwards [@condexp_mono _ m m0 _ _ _ _ _ _ _ _ hf hf.abs
      (@ae_of_all _ m0 _ μ (λ x, le_abs_self (f x) : ∀ x, f x ≤ |f x|)),
    eventually_le.trans (condexp_neg f).symm.le
      (@condexp_mono _ m m0 _ _ _ _ _ _ _ _ hf.neg hf.abs
      (@ae_of_all _ m0 _ μ (λ x, neg_le_abs_self (f x) : ∀ x, -f x ≤ |f x|)))] with x hx₁ hx₂,
  exact abs_le_abs hx₁ hx₂,
end
  ... = snorm f 1 μ :
begin
  rw [snorm_one_eq_lintegral_nnnorm, snorm_one_eq_lintegral_nnnorm,
    ← ennreal.to_real_eq_to_real (ne_of_lt integrable_condexp.2) (ne_of_lt hf.2),
    ← integral_norm_eq_lintegral_nnnorm
      (strongly_measurable_condexp.mono hm).ae_strongly_measurable,
    ← integral_norm_eq_lintegral_nnnorm hf.1],
  simp_rw [real.norm_eq_abs],
  rw ← @integral_condexp _ _ _ _ _ m m0 μ _ hm _ hf.abs,
  refine integral_congr_ae _,
  have : (λ x, (0 : ℝ)) ≤ᵐ[μ] μ[|f| | m],
  { rw ← @condexp_const _ _ _ _ _ _ _ μ hm (0 : ℝ),
    exact condexp_mono (integrable_zero _ _ _) hf.abs
      (@ae_of_all _ m0 _ μ (λ x, abs_nonneg (f x) : ∀ x, 0 ≤ |f x|)) },
  filter_upwards [this] with x hx,
  exact abs_eq_self.2 hx,
end

-- PR contain a more general version
lemma mem_ℒp.uniform_integrable_condexp_filtration
  {g : α → ℝ} (hg : mem_ℒp g 1 μ) :
  uniform_integrable (λ n, μ[g | ℱ n]) 1 μ :=
begin
  have hmeas : ∀ n, ∀ C, measurable_set {x | C ≤ ∥μ[g | ℱ n] x∥₊} :=
    λ n C, measurable_set_le measurable_const
      (strongly_measurable_condexp.mono (ℱ.le _)).measurable.nnnorm,
  have hint : integrable g μ := mem_ℒp_one_iff_integrable.1 hg,
  refine uniform_integrable_of le_rfl ennreal.one_ne_top
    (λ n, (strongly_measurable_condexp.mono (ℱ.le n)).ae_strongly_measurable) (λ ε hε, _),
  by_cases hne : snorm g 1 μ = 0,
  { rw snorm_eq_zero_iff hg.1 one_ne_zero at hne,
    refine ⟨0, λ n, (le_of_eq $ (snorm_eq_zero_iff
      ((strongly_measurable_condexp.mono (ℱ.le _)).ae_strongly_measurable.indicator (hmeas n 0))
      one_ne_zero).2 _).trans (zero_le _)⟩,
    filter_upwards [@condexp_congr_ae _ _ _ _ _ (ℱ n) m0 μ _ _ hne] with x hx,
    simp only [zero_le', set.set_of_true, set.indicator_univ, pi.zero_apply, hx, condexp_zero] },
  obtain ⟨δ, hδ, h⟩ := hg.snorm_indicator_le μ le_rfl ennreal.one_ne_top hε,
  set C : ℝ≥0 := ⟨δ, hδ.le⟩⁻¹ * (snorm g 1 μ).to_nnreal with hC,
  have hCpos : 0 < C :=
    mul_pos (nnreal.inv_pos.2 hδ) (ennreal.to_nnreal_pos hne hg.snorm_lt_top.ne),
  have : ∀ n, μ {x : α | C ≤ ∥μ[g | ℱ n] x∥₊} ≤ ennreal.of_real δ,
  { intro n,
    have := mul_meas_ge_le_pow_snorm' μ one_ne_zero ennreal.one_ne_top
      ((@strongly_measurable_condexp _ _ _ _ _ (ℱ n) _ μ g).mono
        (ℱ.le n)).ae_strongly_measurable C,
    rw [ennreal.one_to_real, ennreal.rpow_one, ennreal.rpow_one, mul_comm,
      ← ennreal.le_div_iff_mul_le (or.inl (ennreal.coe_ne_zero.2 hCpos.ne.symm))
        (or.inl ennreal.coe_lt_top.ne)] at this,
    simp_rw [ennreal.coe_le_coe] at this,
    refine this.trans _,
    rw [ennreal.div_le_iff_le_mul (or.inl (ennreal.coe_ne_zero.2 hCpos.ne.symm))
        (or.inl ennreal.coe_lt_top.ne), hC, nonneg.inv_mk, ennreal.coe_mul,
      ennreal.coe_to_nnreal hg.snorm_lt_top.ne, ← mul_assoc, ← ennreal.of_real_eq_coe_nnreal,
      ← ennreal.of_real_mul hδ.le, mul_inv_cancel hδ.ne.symm, ennreal.of_real_one, one_mul],
    exact hint.snorm_one_condexp_le_snorm (ℱ.le n) },
  refine ⟨C, λ n, le_trans _ (h {x : α | C ≤ ∥μ[g | ℱ n] x∥₊} (hmeas n C) (this n))⟩,
  have hmeasℱ : measurable_set[ℱ n] {x : α | C ≤ ∥μ[g | ℱ n] x∥₊} :=
    @measurable_set_le _ _ _ _ _ (ℱ n) _ _ _ _ _ measurable_const
      (@measurable.nnnorm _ _ _ _ _ (ℱ n) _ strongly_measurable_condexp.measurable),
  rw ← snorm_congr_ae (condexp_indicator hint hmeasℱ),
  exact (integrable.snorm_one_condexp_le_snorm (hint.indicator (hmeas n C)) (ℱ.le _)),
end

end PRed

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
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgtends (λ m, zero_le _)
      (λ m, (hint m).snorm_one_condexp_le_snorm (ℱ.le _)) },
  have hev : ∀ m ≥ n, snorm (μ[f m - g | ℱ n]) 1 μ = snorm (f n - μ[g | ℱ n]) 1 μ,
  { refine λ m hm, snorm_congr_ae
      ((condexp_sub (hf.integrable m) (hgℒ1.integrable le_rfl)).trans _),
    filter_upwards [hf.2 n m hm] with x hx,
    simp only [hx, pi.sub_apply] },
  exact tendsto_nhds_unique (tendsto_at_top_of_eventually_const hev) ht,
end

/-- Part b of the **L¹ martingale convergence theorem**: a uniformly integrable martingale `f`
adapted to the filtration `ℱ` converges a.e. and in L¹ to some integrable function `g` which is
measurable with respect to the σ-algebra `⨆ n, ℱ n`. Furthermore, for all `n`, `f n` is almost
everywhere equal to `𝔼[g | ℱ n]`. -/
lemma martingale.exists_mem_ℒ1_tendsto_snorm
  (hf : martingale f ℱ μ) (hbdd : uniform_integrable f 1 μ) :
  ∃ g : α → ℝ, mem_ℒp g 1 μ ∧ strongly_measurable[⨆ n, ℱ n] g ∧ (∀ n, f n =ᵐ[μ] μ[g | ℱ n]) ∧
  tendsto (λ n, snorm (f n - g) 1 μ) at_top (𝓝 0) ∧
  ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (𝓝 (g x)) :=
let ⟨g, hg₁, hg₂, hg₃, hg₄⟩ := hf.submartingale.exists_mem_ℒ1_tendsto_snorm hbdd in
  ⟨g, hg₁, hg₂, λ n, hf.eq_condexp_lim_of_tendsto_snorm hg₁ hg₃ n, hg₃, hg₄⟩

/-- Part c of the **L¹ martingale convergnce theorem**: Given a integrable function `g` which
is measurable with respect to `⨆ n, ℱ n` where `ℱ` is a filtration, the martingale defined by
`𝔼[g | ℱ n]` converges almost everywhere to `g`.

This martingale also converges to `g` in L¹ and this result is provided by
`measure_theory.mem_ℒp.tendsto_snorm_condexp` -/
lemma mem_ℒp.tendsto_ae_condexp
  {g : α → ℝ} (hg : mem_ℒp g 1 μ) (hgmeas : strongly_measurable[⨆ n, ℱ n] g) :
  ∀ᵐ x ∂μ, tendsto (λ n, μ[g | ℱ n] x) at_top (𝓝 (g x)) :=
begin
  have hle : (⨆ n, ℱ n) ≤ m0 := Sup_le (λ m ⟨n, hn⟩, hn ▸ ℱ.le _),
  obtain ⟨h, hh₁, hhmeas, hh₂, hh₃, hh₄⟩ := (martingale_condexp g ℱ μ).exists_mem_ℒ1_tendsto_snorm
    hg.uniform_integrable_condexp_filtration,
  have hintg : integrable g μ := mem_ℒp_one_iff_integrable.1 hg,
  have hinth : integrable h μ := mem_ℒp_one_iff_integrable.1 hh₁,
  suffices : g =ᵐ[μ] h,
  { filter_upwards [this, hh₄] with x heq ht,
    rwa heq },
  have : ∀ n, ∀ s, measurable_set[ℱ n] s → ∫ x in s, g x ∂μ = ∫ x in s, h x ∂μ,
  { intros n s hs,
    rw [← set_integral_condexp (ℱ.le n) hintg hs, ← set_integral_condexp (ℱ.le n) hinth hs],
    refine set_integral_congr_ae (ℱ.le _ _ hs) _,
    filter_upwards [hh₂ n] with x hx _,
    rwa hx },
  refine ae_eq_of_forall_set_integral_eq_of_sigma_finite' hle
    (λ s _ _, hintg.integrable_on) (λ s _ _, hinth.integrable_on) (λ s hs, _)
    hgmeas.ae_strongly_measurable' hhmeas.ae_strongly_measurable',
  have hgen : (⨆ n, ℱ n) = measurable_space.generate_from {s : set α | ∃ n, measurable_set[ℱ n] s},
  { ext s,
    rw measurable_space.measurable_set_Sup,
    simp_rw set.mem_range,
    change _ ↔ measurable_space.generate_measurable {s : set α | ∃ n, measurable_set[ℱ n] s} s,
    simp only [exists_prop, exists_exists_eq_and] },
  refine @measurable_space.induction_on_inter _ _ _ (⨆ n, ℱ n) hgen _ _ _ _ _ _ hs,
  { rintro s ⟨n, hs⟩ t ⟨m, ht⟩ -,
    by_cases hnm : n ≤ m,
    { exact ⟨m, (ℱ.mono hnm _ hs).inter ht⟩ },
    { exact ⟨n, hs.inter (ℱ.mono (not_le.1 hnm).le _ ht)⟩ } },
  { simp only [measure_empty, with_top.zero_lt_top, measure.restrict_empty,
      integral_zero_measure, forall_true_left] },
  { rintro t ⟨n, ht⟩ -,
    exact this n _ ht },
  { rintro t htmeas ht -,
    have hgeq := @integral_add_compl _ _ (⨆ n, ℱ n) _ _ _ _ _ _ htmeas (hintg.trim hle hgmeas),
    have hheq := @integral_add_compl _ _ (⨆ n, ℱ n) _ _ _ _ _ _ htmeas (hinth.trim hle hhmeas),
    rw [add_comm, ← eq_sub_iff_add_eq] at hgeq hheq,
    rw [set_integral_trim hle hgmeas htmeas.compl, set_integral_trim hle hhmeas htmeas.compl,
      hgeq, hheq, ← set_integral_trim hle hgmeas htmeas, ← set_integral_trim hle hhmeas htmeas,
      ← integral_trim hle hgmeas, ← integral_trim hle hhmeas, ← integral_univ,
      this 0 _ measurable_set.univ, integral_univ, ht (measure_lt_top _ _)] },
  { rintro f hf hfmeas heq -,
    rw [integral_Union (λ n, hle _ (hfmeas n)) hf hintg.integrable_on,
      integral_Union (λ n, hle _ (hfmeas n)) hf hinth.integrable_on],
    exact tsum_congr (λ n, heq _ (measure_lt_top _ _)) }
end

/-- Part c of the **L¹ martingale convergnce theorem**: Given a integrable function `g` which
is measurable with respect to `⨆ n, ℱ n` where `ℱ` is a filtration, the martingale defined by
`𝔼[g | ℱ n]` converges in L¹ to `g`.

This martingale also converges to `g` almost everywhere and this result is provided by
`measure_theory.mem_ℒp.tendsto_ae_condexp` -/
lemma mem_ℒp.tendsto_snorm_condexp
  {g : α → ℝ} (hg : mem_ℒp g 1 μ) (hgmeas : strongly_measurable[⨆ n, ℱ n] g) :
  tendsto (λ n, snorm (μ[g | ℱ n] - g) 1 μ) at_top (𝓝 0) :=
tendsto_Lp_of_tendsto_in_measure _ le_rfl ennreal.one_ne_top
  (λ n, (strongly_measurable_condexp.mono (ℱ.le n)).ae_strongly_measurable) hg
  hg.uniform_integrable_condexp_filtration.2.1 (tendsto_in_measure_of_tendsto_ae
    (λ n,(strongly_measurable_condexp.mono (ℱ.le n)).ae_strongly_measurable)
      (hg.tendsto_ae_condexp hgmeas))

/-- **Lévy's upward theorem**, almost everywhere version: given a function `g` and a filtration
`ℱ`, the sequence defined by `𝔼[g | ℱ n]` converges almost everywhere to `𝔼[g | ⨆ n, ℱ n]`. -/
lemma mem_ℒp.tendsto_ae_condexp' {g : α → ℝ} :
  ∀ᵐ x ∂μ, tendsto (λ n, μ[g | ℱ n] x) at_top (𝓝 (μ[g | ⨆ n, ℱ n] x)) :=
begin
  have ht : ∀ᵐ x ∂μ, tendsto (λ n, μ[μ[g | ⨆ n, ℱ n] | ℱ n] x) at_top (𝓝 (μ[g | ⨆ n, ℱ n] x)) :=
    mem_ℒp.tendsto_ae_condexp (mem_ℒp_one_iff_integrable.2 integrable_condexp)
      strongly_measurable_condexp,
  have heq : ∀ n, ∀ᵐ x ∂μ, μ[μ[g | ⨆ n, ℱ n] | ℱ n] x = μ[g | ℱ n] x :=
    λ n, condexp_condexp_of_le (le_supr _ n) (supr_le (λ n, ℱ.le n)),
  rw ← ae_all_iff at heq,
  filter_upwards [heq, ht] with x hxeq hxt,
  exact hxt.congr hxeq,
end

/-- **Lévy's upward theorem**, L¹ version: given a function `g` and a filtration `ℱ`, the
sequence defined by `𝔼[g | ℱ n]` converges in L¹ to `𝔼[g | ⨆ n, ℱ n]`. -/
lemma mem_ℒp.tendsto_snorm_condexp' {g : α → ℝ} :
  tendsto (λ n, snorm (μ[g | ℱ n] - μ[g | ⨆ n, ℱ n]) 1 μ) at_top (𝓝 0) :=
begin
  have ht : tendsto (λ n, snorm (μ[μ[g | ⨆ n, ℱ n] | ℱ n] - μ[g | ⨆ n, ℱ n]) 1 μ) at_top (𝓝 0) :=
    mem_ℒp.tendsto_snorm_condexp (mem_ℒp_one_iff_integrable.2 integrable_condexp)
      strongly_measurable_condexp,
  have heq : ∀ n, ∀ᵐ x ∂μ, μ[μ[g | ⨆ n, ℱ n] | ℱ n] x = μ[g | ℱ n] x :=
    λ n, condexp_condexp_of_le (le_supr _ n) (supr_le (λ n, ℱ.le n)),
  refine ht.congr (λ n, snorm_congr_ae _),
  filter_upwards [heq n] with x hxeq,
  simp only [hxeq, pi.sub_apply],
end

end measure_theory
