/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import probability.martingale.upcrossing

/-!

# Maringale convergence theorems

-/

open topological_space filter
open_locale nnreal ennreal measure_theory probability_theory big_operators topological_space

namespace measure_theory

variables {α ι : Type*} {m0 : measurable_space α} {μ : measure α} {ℱ : filtration ℕ m0}
variables {a b : ℝ} {f : ℕ → α → ℝ} {N : ℕ} {n m : ℕ} {x : α}

/-!

We will now begin to prove the martingale convergence theorem.

Firstly, we want to show a real sequence `x` converges if
(a) `limsup |x| < ∞`,
(b) For all `a < b : ℚ` we have `sup N, upcrossing_before a b x N < ∞`.

With this, for all `x` satisfying `limsup |λ n, f n x| < ∞` and
for all `a < b : ℚ`, `sup N, upcrossing_before a b f N x ≠ ∞`, we have `λ n, f n x` converges.

Assuming `f` is L¹-bounded, using Fatou's lemma,
we have `𝔼[limsup |f|] ≤ limsup 𝔼[|f|] < ∞` implying `limsup |f| < ∞ a.e`. Furthermore, by
the upcrossing_before lemma, `sup N, upcrossing_before a b f N ≠ ∞ a.e.` implying `f` converges
pointwise almost everywhere.

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
  { -- if `(|f n x|)` is not bounded then either `f n x → ±∞` or (`limsup f n x = ∞` or
    -- `liminf f n x = -∞`). The first case contradicts `liminf |f n x| ≠ ∞` while the second
    -- case contradicts finite upcrossings.
    obtain ⟨a, b, hab, h₁, h₂⟩ := exists_upcrossings_of_not_bounded_under hf₁.ne h,
    exact false.elim ((hf₂ a b hab).ne
      (upcrossing_eq_top_of_frequently_lt (rat.cast_lt.2 hab) h₁ h₂)) }
end

/-- An L¹-bounded submartingale has bounded upcrossings almost everywhere. -/
lemma submartingale.upcrossing_ae_lt_top' [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (hbdd : ∃ R : ℝ≥0, ∀ n, snorm (f n) 1 μ ≤ R) (hab : a < b) :
  ∀ᵐ x ∂μ, upcrossing a b f x < ∞ :=
begin
  refine ae_lt_top (hf.adapted.measurable_upcrossing hab) _,
  have := hf.mul_lintegral_upcrossing_le_lintegral_pos_part a b,
  rw [mul_comm, ← ennreal.le_div_iff_mul_le] at this,
  { refine (lt_of_le_of_lt this (ennreal.div_lt_top _ _)).ne,
    { obtain ⟨R, hR⟩ := hbdd,
      have hR' : ∀ n, ∫⁻ (x : α), ∥f n x - a∥₊ ∂μ ≤ R + ∥a∥₊ * μ set.univ,
      { simp_rw snorm_one_eq_lintegral_nnnorm at hR,
        intro n,
        refine (lintegral_mono _ : ∫⁻ x, ∥f n x - a∥₊ ∂μ ≤ ∫⁻ x, ∥f n x∥₊ + ∥a∥₊ ∂μ).trans _,
        { intro x,
          simp_rw [sub_eq_add_neg, ← nnnorm_neg a, ← ennreal.coe_add, ennreal.coe_le_coe],
          exact nnnorm_add_le _ _ },
        { simp_rw [ lintegral_add_right _ measurable_const, lintegral_const],
          exact add_le_add (hR _) le_rfl } },
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

lemma submartingale.upcrossing_ae_lt_top [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (hbdd : ∃ R : ℝ≥0, ∀ n, snorm (f n) 1 μ ≤ R) :
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

lemma liminf_at_top_ae_bdd_of_snorm_bdd
  (hfmeas : ∀ n, measurable (f n)) (hbdd : ∃ R : ℝ≥0, ∀ n, snorm (f n) 1 μ ≤ R) :
  ∀ᵐ x ∂μ, at_top.liminf (λ n, (∥f n x∥₊ : ℝ≥0∞)) < ∞ :=
begin
  obtain ⟨R, hR⟩ := hbdd,
  refine ae_lt_top (measurable_liminf (λ n, (hfmeas n).nnnorm.coe_nnreal_ennreal))
    (lt_of_le_of_lt (lintegral_liminf_le (λ n, (hfmeas n).nnnorm.coe_nnreal_ennreal))
    (lt_of_le_of_lt _ (ennreal.coe_lt_top : ↑R < ∞))).ne,
  simp_rw [← snorm_one_eq_lintegral_nnnorm, liminf_eq, eventually_at_top],
  exact Sup_le (λ b ⟨a, ha⟩, (ha a le_rfl).trans (hR _)),
end

/-- An L¹-bounded submartingale converges almost everywhere. -/
lemma submartingale.exists_ae_tendsto_of_bdd [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (hbdd : ∃ R : ℝ≥0, ∀ n, snorm (f n) 1 μ ≤ R) :
  ∀ᵐ x ∂μ, ∃ c, tendsto (λ n, f n x) at_top (𝓝 c) :=
begin
  filter_upwards [hf.upcrossing_ae_lt_top hbdd, liminf_at_top_ae_bdd_of_snorm_bdd
    (λ n, (hf.strongly_measurable n).measurable.mono (ℱ.le n) le_rfl) hbdd] with x h₁ h₂,
  exact tendsto_of_uncrossing_lt_top h₂ h₁,
end

/-- **Almost everywhere martingale convergence theorem**: An L¹-bounded submartingale converges
almost everywhere to a L¹ random variable. -/
lemma submartingale.exists_mem_ℒ1_ae_tendsto_of_bdd [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (hbdd : ∃ R : ℝ≥0, ∀ n, snorm (f n) 1 μ ≤ R) :
  ∃ g : α → ℝ, mem_ℒp g 1 μ ∧
  ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (𝓝 (g x)) :=
begin
  classical,
  set g : α → ℝ := λ x, if h : ∃ c, tendsto (λ n, f n x) at_top (𝓝 c) then h.some else 0 with hgd,
  have hg : ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (𝓝 (g x)),
  { filter_upwards [hf.exists_ae_tendsto_of_bdd hbdd] with x hx,
    simp_rw [hgd, dif_pos hx],
    exact hx.some_spec },
  have hgmeas : ae_strongly_measurable g μ :=
    ae_measurable.ae_strongly_measurable (ae_measurable_of_tendsto_metrizable_ae'
      (λ n, ((hf.strongly_measurable n).measurable.mono (ℱ.le n) le_rfl).ae_measurable) hg),
  refine ⟨g, ⟨hgmeas, _⟩, hg⟩,
  { obtain ⟨R, hR⟩ := hbdd,
    refine lt_of_le_of_lt (Lp.snorm_lim_le_liminf_snorm
      (λ n, ((hf.strongly_measurable n).measurable.mono (ℱ.le n) le_rfl).ae_strongly_measurable)
      g hg) (lt_of_le_of_lt _ (ennreal.coe_lt_top : ↑R < ∞)),
    simp_rw [liminf_eq, eventually_at_top],
    exact Sup_le (λ b ⟨a, ha⟩, (ha a le_rfl).trans (hR _)) }
end

end measure_theory
