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

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The martingale convergence theorems are a collection of theorems characterizing the convergence
of a martingale provided it satisfies some boundedness conditions. This file contains the
almost everywhere martingale convergence theorem which provides an almost everywhere limit to
an L¹ bounded submartingale. It also contains the L¹ martingale convergence theorem which provides
an L¹ limit to a uniformly integrable submartingale. Finally, it also contains the Lévy upwards
theorems.

## Main results

* `measure_theory.submartingale.ae_tendsto_limit_process`: the almost everywhere martingale
  convergence theorem: an L¹-bounded submartingale adapted to the filtration `ℱ` converges almost
  everywhere to its limit process.
* `measure_theory.submartingale.mem_ℒp_limit_process`: the limit process of an Lᵖ-bounded
  submartingale is Lᵖ.
* `measure_theory.submartingale.tendsto_snorm_one_limit_process`: part a of the L¹ martingale
  convergence theorem: a uniformly integrable submartingale adapted to the filtration `ℱ` converges
  almost everywhere and in L¹ to an integrable function which is measurable with respect to
  the σ-algebra `⨆ n, ℱ n`.
* `measure_theory.martingale.ae_eq_condexp_limit_process`: part b the L¹ martingale convergence
  theorem: if `f` is a uniformly integrable martingale adapted to the filtration `ℱ`, then
  `f n` equals `𝔼[g | ℱ n]` almost everywhere where `g` is the limiting process of `f`.
* `measure_theory.integrable.tendsto_ae_condexp`: part c the L¹ martingale convergence theorem:
  given a `⨆ n, ℱ n`-measurable function `g` where `ℱ` is a filtration, `𝔼[g | ℱ n]` converges
  almost everywhere to `g`.
* `measure_theory.integrable.tendsto_snorm_condexp`: part c the L¹ martingale convergence theorem:
  given a `⨆ n, ℱ n`-measurable function `g` where `ℱ` is a filtration, `𝔼[g | ℱ n]` converges in
  L¹ to `g`.

-/

open topological_space filter measure_theory.filtration
open_locale nnreal ennreal measure_theory probability_theory big_operators topology

namespace measure_theory

variables {Ω ι : Type*} {m0 : measurable_space Ω} {μ : measure Ω} {ℱ : filtration ℕ m0}
variables {a b : ℝ} {f : ℕ → Ω → ℝ} {ω : Ω} {R : ℝ≥0}

section ae_convergence

/-!

### Almost everywhere martingale convergence theorem

We will now prove the almost everywhere martingale convergence theorem.

The a.e. martingale convergence theorem states: if `f` is an L¹-bounded `ℱ`-submartingale, then
it converges almost everywhere to an integrable function which is measurable with respect to
the σ-algebra `ℱ∞ := ⨆ n, ℱ n`.

Mathematically, we proceed by first noting that a real sequence $(x_n)$ converges if
(a) $\limsup_{n \to \infty} |x_n| < \infty$, (b) for all $a < b \in \mathbb{Q}$ we have the
number of upcrossings of $(x_n)$ from below $a$ to above $b$ is finite.
Thus, for all $\omega$ satisfying $\limsup_{n \to \infty} |f_n(\omega)| < \infty$ and the number of
upcrossings of $(f_n(\omega))$ from below $a$ to above $b$ is finite for all $a < b \in \mathbb{Q}$,
we have $(f_n(\omega))$ is convergent.

Hence, assuming $(f_n)$ is L¹-bounded, using Fatou's lemma, we have
$$
  \mathbb{E} \limsup_{n \to \infty} |f_n| \le \limsup_{n \to \infty} \mathbb{E}|f_n| < \infty
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

Implementation wise, we have `tendsto_of_no_upcrossings` which showed that
a bounded sequence converges if it does not visit below $a$ and above $b$ infinitely often
for all $a, b ∈ s$ for some dense set $s$. So, we may skip the first step provided we can prove
that the realizations are bounded almost everywhere. Indeed, suppose $(|f_n(\omega)|)$ is not
bounded, then either $f_n(\omega) \to \pm \infty$ or one of $\limsup f_n(\omega)$ or
$\liminf f_n(\omega)$ equals $\pm \infty$ while the other is finite. But the first case
contradicts $\liminf |f_n(\omega)| < \infty$ while the second case contradicts finite upcrossings.

Furthermore, we introduced `filtration.limit_process` which chooses the limiting random variable
of a stochastic process if it exists, otherwise it returns 0. Hence, instead of showing an
existence statement, we phrased the a.e. martingale convergence theorem by showed that a
submartingale converges to its `limit_process` almost everywhere.

-/

/-- If a stochastic process has bounded upcrossing from below `a` to above `b`,
then it does not frequently visit both below `a` and above `b`. -/
lemma not_frequently_of_upcrossings_lt_top (hab : a < b) (hω : upcrossings a b f ω ≠ ∞) :
  ¬((∃ᶠ n in at_top, f n ω < a) ∧ (∃ᶠ n in at_top, b < f n ω)) :=
begin
  rw [← lt_top_iff_ne_top, upcrossings_lt_top_iff] at hω,
  replace hω : ∃ k, ∀ N, upcrossings_before a b f N ω < k,
  { obtain ⟨k, hk⟩ := hω,
    exact ⟨k + 1, λ N, lt_of_le_of_lt (hk N) k.lt_succ_self⟩ },
  rintro ⟨h₁, h₂⟩,
  rw frequently_at_top at h₁ h₂,
  refine not_not.2 hω _,
  push_neg,
  intro k,
  induction k with k ih,
  { simp only [zero_le', exists_const] },
  { obtain ⟨N, hN⟩ := ih,
    obtain ⟨N₁, hN₁, hN₁'⟩ := h₁ N,
    obtain ⟨N₂, hN₂, hN₂'⟩ := h₂ N₁,
    exact ⟨(N₂ + 1), nat.succ_le_of_lt $ lt_of_le_of_lt hN
      (upcrossings_before_lt_of_exists_upcrossing hab hN₁ hN₁' hN₂ hN₂')⟩ }
end

/-- A stochastic process that frequently visits below `a` and above `b` have infinite
upcrossings. -/
lemma upcrossings_eq_top_of_frequently_lt (hab : a < b)
  (h₁ : ∃ᶠ n in at_top, f n ω < a) (h₂ : ∃ᶠ n in at_top, b < f n ω) :
  upcrossings a b f ω = ∞ :=
classical.by_contradiction (λ h, not_frequently_of_upcrossings_lt_top hab h ⟨h₁, h₂⟩)

/-- A realization of a stochastic process with bounded upcrossings and bounded liminfs is
convergent.

We use the spelling `< ∞` instead of the standard `≠ ∞` in the assumptions since it is not as easy
to change `<` to `≠` under binders. -/
lemma tendsto_of_uncrossing_lt_top
  (hf₁ : liminf (λ n, (‖f n ω‖₊ : ℝ≥0∞)) at_top < ∞)
  (hf₂ : ∀ a b : ℚ, a < b → upcrossings a b f ω < ∞) :
  ∃ c, tendsto (λ n, f n ω) at_top (𝓝 c) :=
begin
  by_cases h : is_bounded_under (≤) at_top (λ n, |f n ω|),
  { rw is_bounded_under_le_abs at h,
    refine tendsto_of_no_upcrossings rat.dense_range_cast _ h.1 h.2,
    { intros a ha b hb hab,
      obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := ⟨ha, hb⟩,
      exact not_frequently_of_upcrossings_lt_top hab (hf₂ a b (rat.cast_lt.1 hab)).ne } },
  { obtain ⟨a, b, hab, h₁, h₂⟩ := ennreal.exists_upcrossings_of_not_bounded_under hf₁.ne h,
    exact false.elim ((hf₂ a b hab).ne
      (upcrossings_eq_top_of_frequently_lt (rat.cast_lt.2 hab) h₁ h₂)) }
end

/-- An L¹-bounded submartingale has bounded upcrossings almost everywhere. -/
lemma submartingale.upcrossings_ae_lt_top' [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (hbdd : ∀ n, snorm (f n) 1 μ ≤ R) (hab : a < b) :
  ∀ᵐ ω ∂μ, upcrossings a b f ω < ∞ :=
begin
  refine ae_lt_top (hf.adapted.measurable_upcrossings hab) _,
  have := hf.mul_lintegral_upcrossings_le_lintegral_pos_part a b,
  rw [mul_comm, ← ennreal.le_div_iff_mul_le] at this,
  { refine (lt_of_le_of_lt this (ennreal.div_lt_top _ _)).ne,
    { have hR' : ∀ n, ∫⁻ ω, ‖f n ω - a‖₊ ∂μ ≤ R + ‖a‖₊ * μ set.univ,
      { simp_rw snorm_one_eq_lintegral_nnnorm at hbdd,
        intro n,
        refine (lintegral_mono _ : ∫⁻ ω, ‖f n ω - a‖₊ ∂μ ≤ ∫⁻ ω, ‖f n ω‖₊ + ‖a‖₊ ∂μ).trans _,
        { intro ω,
          simp_rw [sub_eq_add_neg, ← nnnorm_neg a, ← ennreal.coe_add, ennreal.coe_le_coe],
          exact nnnorm_add_le _ _ },
        { simp_rw [ lintegral_add_right _ measurable_const, lintegral_const],
          exact add_le_add (hbdd _) le_rfl } },
      refine ne_of_lt (supr_lt_iff.2 ⟨R + ‖a‖₊ * μ set.univ, ennreal.add_lt_top.2
          ⟨ennreal.coe_lt_top, ennreal.mul_lt_top ennreal.coe_lt_top.ne (measure_ne_top _ _)⟩,
          λ n, le_trans _ (hR' n)⟩),
      refine lintegral_mono (λ ω, _),
      rw [ennreal.of_real_le_iff_le_to_real, ennreal.coe_to_real, coe_nnnorm],
      by_cases hnonneg : 0 ≤ f n ω - a,
      { rw [lattice_ordered_comm_group.pos_of_nonneg _ hnonneg,
          real.norm_eq_abs, abs_of_nonneg hnonneg] },
      { rw lattice_ordered_comm_group.pos_of_nonpos _ (not_le.1 hnonneg).le,
        exact norm_nonneg _ },
      { simp only [ne.def, ennreal.coe_ne_top, not_false_iff] } },
    { simp only [hab, ne.def, ennreal.of_real_eq_zero, sub_nonpos, not_le] } },
  { simp only [hab, ne.def, ennreal.of_real_eq_zero, sub_nonpos, not_le, true_or]},
  { simp only [ne.def, ennreal.of_real_ne_top, not_false_iff, true_or] }
end

lemma submartingale.upcrossings_ae_lt_top [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (hbdd : ∀ n, snorm (f n) 1 μ ≤ R) :
  ∀ᵐ ω ∂μ, ∀ a b : ℚ, a < b → upcrossings a b f ω < ∞ :=
begin
  simp only [ae_all_iff, eventually_imp_distrib_left],
  rintro a b hab,
  exact hf.upcrossings_ae_lt_top' hbdd (rat.cast_lt.2 hab),
end

/-- An L¹-bounded submartingale converges almost everywhere. -/
lemma submartingale.exists_ae_tendsto_of_bdd [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (hbdd : ∀ n, snorm (f n) 1 μ ≤ R) :
  ∀ᵐ ω ∂μ, ∃ c, tendsto (λ n, f n ω) at_top (𝓝 c) :=
begin
  filter_upwards [hf.upcrossings_ae_lt_top hbdd, ae_bdd_liminf_at_top_of_snorm_bdd one_ne_zero
    (λ n, (hf.strongly_measurable n).measurable.mono (ℱ.le n) le_rfl) hbdd] with ω h₁ h₂,
  exact tendsto_of_uncrossing_lt_top h₂ h₁,
end

lemma submartingale.exists_ae_trim_tendsto_of_bdd [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (hbdd : ∀ n, snorm (f n) 1 μ ≤ R) :
  ∀ᵐ ω ∂(μ.trim (Sup_le (λ m ⟨n, hn⟩, hn ▸ ℱ.le _) : (⨆ n, ℱ n) ≤ m0)),
    ∃ c, tendsto (λ n, f n ω) at_top (𝓝 c) :=
begin
  rw [ae_iff, trim_measurable_set_eq],
  { exact hf.exists_ae_tendsto_of_bdd hbdd },
  { exact measurable_set.compl (@measurable_set_exists_tendsto _ _ _ _ _ _ (⨆ n, ℱ n) _ _ _ _ _
    (λ n, ((hf.strongly_measurable n).measurable.mono (le_Sup ⟨n, rfl⟩) le_rfl))) }
end

/-- **Almost everywhere martingale convergence theorem**: An L¹-bounded submartingale converges
almost everywhere to a `⨆ n, ℱ n`-measurable function. -/
lemma submartingale.ae_tendsto_limit_process [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (hbdd : ∀ n, snorm (f n) 1 μ ≤ R) :
  ∀ᵐ ω ∂μ, tendsto (λ n, f n ω) at_top (𝓝 (ℱ.limit_process f μ ω)) :=
begin
  classical,
  suffices : ∃ g, strongly_measurable[⨆ n, ℱ n] g ∧ ∀ᵐ ω ∂μ, tendsto (λ n, f n ω) at_top (𝓝 (g ω)),
  { rw [limit_process, dif_pos this],
    exact (classical.some_spec this).2 },
  set g' : Ω → ℝ := λ ω, if h : ∃ c, tendsto (λ n, f n ω) at_top (𝓝 c) then h.some else 0,
  have hle : (⨆ n, ℱ n) ≤ m0 := Sup_le (λ m ⟨n, hn⟩, hn ▸ ℱ.le _),
  have hg' : ∀ᵐ ω ∂(μ.trim hle), tendsto (λ n, f n ω) at_top (𝓝 (g' ω)),
  { filter_upwards [hf.exists_ae_trim_tendsto_of_bdd hbdd] with ω hω,
    simp_rw [g', dif_pos hω],
    exact hω.some_spec },
  have hg'm : @ae_strongly_measurable _ _ _ (⨆ n, ℱ n) g' (μ.trim hle) :=
    (@ae_measurable_of_tendsto_metrizable_ae' _ _ (⨆ n, ℱ n) _ _ _ _ _ _ _
      (λ n, ((hf.strongly_measurable n).measurable.mono
      (le_Sup ⟨n, rfl⟩ : ℱ n ≤ ⨆ n, ℱ n) le_rfl).ae_measurable) hg').ae_strongly_measurable,
  obtain ⟨g, hgm, hae⟩ := hg'm,
  have hg : ∀ᵐ ω ∂μ.trim hle, tendsto (λ n, f n ω) at_top (𝓝 (g ω)),
  { filter_upwards [hae, hg'] with ω hω hg'ω,
    exact hω ▸ hg'ω },
  exact ⟨g, hgm, measure_eq_zero_of_trim_eq_zero hle hg⟩,
end

/-- The limiting process of an Lᵖ-bounded submartingale is Lᵖ. -/
lemma submartingale.mem_ℒp_limit_process {p : ℝ≥0∞}
  (hf : submartingale f ℱ μ) (hbdd : ∀ n, snorm (f n) p μ ≤ R) :
  mem_ℒp (ℱ.limit_process f μ) p μ :=
mem_ℒp_limit_process_of_snorm_bdd
  (λ n, ((hf.strongly_measurable n).mono (ℱ.le n)).ae_strongly_measurable) hbdd

end ae_convergence

section L1_convergence

variables [is_finite_measure μ] {g : Ω → ℝ}

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
and the Vitali convergence theorem as our definition of uniform integrability (in the probability
sense) directly implies L¹-uniform boundedness. We note that our definition of uniform
integrability is slightly non-standard but is equivalent to the usual literary definition. This
equivalence is provided by `measure_theory.uniform_integrable_iff`.

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
L¹, it suffices to show that $h = g$ almost everywhere where $g$ is the almost everywhere and L¹
limit of $(f_n)_n$ from part (b) of the theorem. By noting that, for all $s \in \mathcal{F}_n$,
we have
$$
  \mathbb{E}g\mathbf{1}_s = \mathbb{E}[\mathbb{E}[g \mid \mathcal{F}_n]\mathbf{1}_s] =
    \mathbb{E}[\mathbb{E}[h \mid \mathcal{F}_n]\mathbf{1}_s] = \mathbb{E}h\mathbf{1}_s
$$
where $\mathbb{E}[g \mid \mathcal{F}_n = \mathbb{E}[h \mid \mathcal{F}_n]$ almost everywhere
by part (b); the equality also holds for all $s \in \mathcal{F}_\infty$ by Dynkin's theorem.
Thus, as both $h$ and $g$ are $\mathcal{F}_\infty$-measurable, $h = g$ almost everywhere as
required.

Similar to the a.e. martingale convergence theorem, rather than showing the existence of the
limiting process, we phrased the L¹-martingale convergence theorem by proving that a submartingale
does converge in L¹ to its `limit_process`. However, in contrast to the a.e. martingale convergence
theorem, we do not need to introduce a L¹ version of `filtration.limit_process` as the L¹ limit
and the a.e. limit of a submartingale coincide.

-/

/-- Part a of the **L¹ martingale convergence theorem**: a uniformly integrable submartingale
adapted to the filtration `ℱ` converges a.e. and in L¹ to an integrable function which is
measurable with respect to the σ-algebra `⨆ n, ℱ n`. -/
lemma submartingale.tendsto_snorm_one_limit_process
  (hf : submartingale f ℱ μ) (hunif : uniform_integrable f 1 μ) :
  tendsto (λ n, snorm (f n - ℱ.limit_process f μ) 1 μ) at_top (𝓝 0) :=
begin
  obtain ⟨R, hR⟩ := hunif.2.2,
  have hmeas : ∀ n, ae_strongly_measurable (f n) μ :=
    λ n, ((hf.strongly_measurable n).mono (ℱ.le _)).ae_strongly_measurable,
  exact tendsto_Lp_of_tendsto_in_measure _ le_rfl ennreal.one_ne_top hmeas
    (mem_ℒp_limit_process_of_snorm_bdd hmeas hR) hunif.2.1
    (tendsto_in_measure_of_tendsto_ae hmeas $ hf.ae_tendsto_limit_process hR),
end

lemma submartingale.ae_tendsto_limit_process_of_uniform_integrable
  (hf : submartingale f ℱ μ) (hunif : uniform_integrable f 1 μ) :
  ∀ᵐ ω ∂μ, tendsto (λ n, f n ω) at_top (𝓝 (ℱ.limit_process f μ ω)) :=
let ⟨R, hR⟩ := hunif.2.2 in hf.ae_tendsto_limit_process hR

/-- If a martingale `f` adapted to `ℱ` converges in L¹ to `g`, then for all `n`, `f n` is almost
everywhere equal to `𝔼[g | ℱ n]`. -/
lemma martingale.eq_condexp_of_tendsto_snorm {μ : measure Ω}
  (hf : martingale f ℱ μ) (hg : integrable g μ)
  (hgtends : tendsto (λ n, snorm (f n - g) 1 μ) at_top (𝓝 0)) (n : ℕ) :
  f n =ᵐ[μ] μ[g | ℱ n] :=
begin
  rw [← sub_ae_eq_zero, ← snorm_eq_zero_iff ((((hf.strongly_measurable n).mono (ℱ.le _)).sub
    (strongly_measurable_condexp.mono (ℱ.le _))).ae_strongly_measurable) one_ne_zero],
  have ht : tendsto (λ m, snorm (μ[f m - g | ℱ n]) 1 μ) at_top (𝓝 0),
  { have hint : ∀ m, integrable (f m - g) μ := λ m, (hf.integrable m).sub hg,
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgtends (λ m, zero_le _)
      (λ m, snorm_one_condexp_le_snorm _) },
  have hev : ∀ m ≥ n, snorm (μ[f m - g | ℱ n]) 1 μ = snorm (f n - μ[g | ℱ n]) 1 μ,
  { refine λ m hm, snorm_congr_ae
      ((condexp_sub (hf.integrable m) hg).trans _),
    filter_upwards [hf.2 n m hm] with x hx,
    simp only [hx, pi.sub_apply] },
  exact tendsto_nhds_unique (tendsto_at_top_of_eventually_const hev) ht,
end

/-- Part b of the **L¹ martingale convergence theorem**: if `f` is a uniformly integrable martingale
adapted to the filtration `ℱ`, then for all `n`, `f n` is almost everywhere equal to the conditional
expectation of its limiting process wrt. `ℱ n`. -/
lemma martingale.ae_eq_condexp_limit_process
  (hf : martingale f ℱ μ) (hbdd : uniform_integrable f 1 μ) (n : ℕ) :
  f n =ᵐ[μ] μ[ℱ.limit_process f μ | ℱ n] :=
let ⟨R, hR⟩ := hbdd.2.2 in hf.eq_condexp_of_tendsto_snorm
  ((mem_ℒp_limit_process_of_snorm_bdd hbdd.1 hR).integrable le_rfl)
  (hf.submartingale.tendsto_snorm_one_limit_process hbdd) n

/-- Part c of the **L¹ martingale convergnce theorem**: Given a integrable function `g` which
is measurable with respect to `⨆ n, ℱ n` where `ℱ` is a filtration, the martingale defined by
`𝔼[g | ℱ n]` converges almost everywhere to `g`.

This martingale also converges to `g` in L¹ and this result is provided by
`measure_theory.integrable.tendsto_snorm_condexp` -/
lemma integrable.tendsto_ae_condexp
  (hg : integrable g μ) (hgmeas : strongly_measurable[⨆ n, ℱ n] g) :
  ∀ᵐ x ∂μ, tendsto (λ n, μ[g | ℱ n] x) at_top (𝓝 (g x)) :=
begin
  have hle : (⨆ n, ℱ n) ≤ m0 := Sup_le (λ m ⟨n, hn⟩, hn ▸ ℱ.le _),
  have hunif : uniform_integrable (λ n, μ[g | ℱ n]) 1 μ := hg.uniform_integrable_condexp_filtration,
  obtain ⟨R, hR⟩ := hunif.2.2,
  have hlimint : integrable (ℱ.limit_process (λ n, μ[g | ℱ n]) μ) μ :=
    (mem_ℒp_limit_process_of_snorm_bdd hunif.1 hR).integrable le_rfl,
  suffices : g =ᵐ[μ] ℱ.limit_process (λ n x, μ[g | ℱ n] x) μ,
  { filter_upwards [this, (martingale_condexp g ℱ μ).submartingale.ae_tendsto_limit_process hR]
      with x heq ht,
    rwa heq },
  have : ∀ n s, measurable_set[ℱ n] s → ∫ x in s, g x ∂μ =
    ∫ x in s, ℱ.limit_process (λ n x, μ[g | ℱ n] x) μ x ∂μ,
  { intros n s hs,
    rw [← set_integral_condexp (ℱ.le n) hg hs, ← set_integral_condexp (ℱ.le n) hlimint hs],
    refine set_integral_congr_ae (ℱ.le _ _ hs) _,
    filter_upwards [(martingale_condexp g ℱ μ).ae_eq_condexp_limit_process hunif n] with x hx _,
    rwa hx },
  refine ae_eq_of_forall_set_integral_eq_of_sigma_finite' hle
    (λ s _ _, hg.integrable_on) (λ s _ _, hlimint.integrable_on) (λ s hs, _)
    hgmeas.ae_strongly_measurable' strongly_measurable_limit_process.ae_strongly_measurable',
  refine @measurable_space.induction_on_inter _ _ _ (⨆ n, ℱ n)
    (measurable_space.measurable_space_supr_eq ℱ) _ _ _ _ _ _ hs,
  { rintro s ⟨n, hs⟩ t ⟨m, ht⟩ -,
    by_cases hnm : n ≤ m,
    { exact ⟨m, (ℱ.mono hnm _ hs).inter ht⟩ },
    { exact ⟨n, hs.inter (ℱ.mono (not_le.1 hnm).le _ ht)⟩ } },
  { simp only [measure_empty, with_top.zero_lt_top, measure.restrict_empty,
      integral_zero_measure, forall_true_left] },
  { rintro t ⟨n, ht⟩ -,
    exact this n _ ht },
  { rintro t htmeas ht -,
    have hgeq := @integral_add_compl _ _ (⨆ n, ℱ n) _ _ _ _ _ _ htmeas (hg.trim hle hgmeas),
    have hheq := @integral_add_compl _ _ (⨆ n, ℱ n) _ _ _ _ _ _ htmeas
      (hlimint.trim hle strongly_measurable_limit_process),
    rw [add_comm, ← eq_sub_iff_add_eq] at hgeq hheq,
    rw [set_integral_trim hle hgmeas htmeas.compl,
      set_integral_trim hle strongly_measurable_limit_process htmeas.compl,
      hgeq, hheq, ← set_integral_trim hle hgmeas htmeas,
      ← set_integral_trim hle strongly_measurable_limit_process htmeas,
      ← integral_trim hle hgmeas, ← integral_trim hle strongly_measurable_limit_process,
      ← integral_univ, this 0 _ measurable_set.univ, integral_univ, ht (measure_lt_top _ _)] },
  { rintro f hf hfmeas heq -,
    rw [integral_Union (λ n, hle _ (hfmeas n)) hf hg.integrable_on,
      integral_Union (λ n, hle _ (hfmeas n)) hf hlimint.integrable_on],
    exact tsum_congr (λ n, heq _ (measure_lt_top _ _)) }
end

/-- Part c of the **L¹ martingale convergnce theorem**: Given a integrable function `g` which
is measurable with respect to `⨆ n, ℱ n` where `ℱ` is a filtration, the martingale defined by
`𝔼[g | ℱ n]` converges in L¹ to `g`.

This martingale also converges to `g` almost everywhere and this result is provided by
`measure_theory.integrable.tendsto_ae_condexp` -/
lemma integrable.tendsto_snorm_condexp
  (hg : integrable g μ) (hgmeas : strongly_measurable[⨆ n, ℱ n] g) :
  tendsto (λ n, snorm (μ[g | ℱ n] - g) 1 μ) at_top (𝓝 0) :=
tendsto_Lp_of_tendsto_in_measure _ le_rfl ennreal.one_ne_top
  (λ n, (strongly_measurable_condexp.mono (ℱ.le n)).ae_strongly_measurable)
  (mem_ℒp_one_iff_integrable.2 hg) (hg.uniform_integrable_condexp_filtration).2.1
    (tendsto_in_measure_of_tendsto_ae
    (λ n,(strongly_measurable_condexp.mono (ℱ.le n)).ae_strongly_measurable)
      (hg.tendsto_ae_condexp hgmeas))

/-- **Lévy's upward theorem**, almost everywhere version: given a function `g` and a filtration
`ℱ`, the sequence defined by `𝔼[g | ℱ n]` converges almost everywhere to `𝔼[g | ⨆ n, ℱ n]`. -/
lemma tendsto_ae_condexp (g : Ω → ℝ) :
  ∀ᵐ x ∂μ, tendsto (λ n, μ[g | ℱ n] x) at_top (𝓝 (μ[g | ⨆ n, ℱ n] x)) :=
begin
  have ht : ∀ᵐ x ∂μ, tendsto (λ n, μ[μ[g | ⨆ n, ℱ n] | ℱ n] x) at_top (𝓝 (μ[g | ⨆ n, ℱ n] x)) :=
    integrable_condexp.tendsto_ae_condexp strongly_measurable_condexp,
  have heq : ∀ n, ∀ᵐ x ∂μ, μ[μ[g | ⨆ n, ℱ n] | ℱ n] x = μ[g | ℱ n] x :=
    λ n, condexp_condexp_of_le (le_supr _ n) (supr_le (λ n, ℱ.le n)),
  rw ← ae_all_iff at heq,
  filter_upwards [heq, ht] with x hxeq hxt,
  exact hxt.congr hxeq,
end

/-- **Lévy's upward theorem**, L¹ version: given a function `g` and a filtration `ℱ`, the
sequence defined by `𝔼[g | ℱ n]` converges in L¹ to `𝔼[g | ⨆ n, ℱ n]`. -/
lemma tendsto_snorm_condexp (g : Ω → ℝ) :
  tendsto (λ n, snorm (μ[g | ℱ n] - μ[g | ⨆ n, ℱ n]) 1 μ) at_top (𝓝 0) :=
begin
  have ht : tendsto (λ n, snorm (μ[μ[g | ⨆ n, ℱ n] | ℱ n] - μ[g | ⨆ n, ℱ n]) 1 μ) at_top (𝓝 0) :=
    integrable_condexp.tendsto_snorm_condexp strongly_measurable_condexp,
  have heq : ∀ n, ∀ᵐ x ∂μ, μ[μ[g | ⨆ n, ℱ n] | ℱ n] x = μ[g | ℱ n] x :=
    λ n, condexp_condexp_of_le (le_supr _ n) (supr_le (λ n, ℱ.le n)),
  refine ht.congr (λ n, snorm_congr_ae _),
  filter_upwards [heq n] with x hxeq,
  simp only [hxeq, pi.sub_apply],
end

end L1_convergence

end measure_theory
