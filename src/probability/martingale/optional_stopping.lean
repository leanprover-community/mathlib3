/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import probability.process.hitting_time
import probability.martingale.basic

/-! # Optional stopping theorem (fair game theorem)

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The optional stopping theorem states that an adapted integrable process `f` is a submartingale if
and only if for all bounded stopping times `τ` and `π` such that `τ ≤ π`, the
stopped value of `f` at `τ` has expectation smaller than its stopped value at `π`.

This file also contains Doob's maximal inequality: given a non-negative submartingale `f`, for all
`ε : ℝ≥0`, we have `ε • μ {ε ≤ f* n} ≤ ∫ ω in {ε ≤ f* n}, f n` where `f* n ω = max_{k ≤ n}, f k ω`.

### Main results

* `measure_theory.submartingale_iff_expected_stopped_value_mono`: the optional stopping theorem.
* `measure_theory.submartingale.stopped_process`: the stopped process of a submartingale with
  respect to a stopping time is a submartingale.
* `measure_theory.maximal_ineq`: Doob's maximal inequality.

 -/

open_locale nnreal ennreal measure_theory probability_theory

namespace measure_theory

variables {Ω : Type*} {m0 : measurable_space Ω} {μ : measure Ω} {𝒢 : filtration ℕ m0}
  {f : ℕ → Ω → ℝ} {τ π : Ω → ℕ}

-- We may generalize the below lemma to functions taking value in a `normed_lattice_add_comm_group`.
-- Similarly, generalize `(super/)submartingale.set_integral_le`.

/-- Given a submartingale `f` and bounded stopping times `τ` and `π` such that `τ ≤ π`, the
expectation of `stopped_value f τ` is less than or equal to the expectation of `stopped_value f π`.
This is the forward direction of the optional stopping theorem. -/
lemma submartingale.expected_stopped_value_mono [sigma_finite_filtration μ 𝒢]
  (hf : submartingale f 𝒢 μ) (hτ : is_stopping_time 𝒢 τ) (hπ : is_stopping_time 𝒢 π) (hle : τ ≤ π)
  {N : ℕ} (hbdd : ∀ ω, π ω ≤ N) :
  μ[stopped_value f τ] ≤ μ[stopped_value f π] :=
begin
  rw [← sub_nonneg, ← integral_sub', stopped_value_sub_eq_sum' hle hbdd],
  { simp only [finset.sum_apply],
    have : ∀ i, measurable_set[𝒢 i] {ω : Ω | τ ω ≤ i ∧ i < π ω},
    { intro i,
      refine (hτ i).inter _,
      convert (hπ i).compl,
      ext x,
      simpa },
    rw integral_finset_sum,
    { refine finset.sum_nonneg (λ i hi, _),
      rw [integral_indicator (𝒢.le _ _ (this _)), integral_sub', sub_nonneg],
      { exact hf.set_integral_le (nat.le_succ i) (this _) },
      { exact (hf.integrable _).integrable_on },
      { exact (hf.integrable _).integrable_on } },
    intros i hi,
    exact integrable.indicator (integrable.sub (hf.integrable _) (hf.integrable _))
      (𝒢.le _ _ (this _)) },
  { exact hf.integrable_stopped_value hπ hbdd },
  { exact hf.integrable_stopped_value hτ (λ ω, le_trans (hle ω) (hbdd ω)) }
end

/-- The converse direction of the optional stopping theorem, i.e. an adapted integrable process `f`
is a submartingale if for all bounded stopping times `τ` and `π` such that `τ ≤ π`, the
stopped value of `f` at `τ` has expectation smaller than its stopped value at `π`. -/
lemma submartingale_of_expected_stopped_value_mono [is_finite_measure μ]
  (hadp : adapted 𝒢 f) (hint : ∀ i, integrable (f i) μ)
  (hf : ∀ τ π : Ω → ℕ, is_stopping_time 𝒢 τ → is_stopping_time 𝒢 π → τ ≤ π → (∃ N, ∀ ω, π ω ≤ N) →
    μ[stopped_value f τ] ≤ μ[stopped_value f π]) :
  submartingale f 𝒢 μ :=
begin
  refine submartingale_of_set_integral_le hadp hint (λ i j hij s hs, _),
  classical,
  specialize hf (s.piecewise (λ _, i) (λ _, j)) _
    (is_stopping_time_piecewise_const hij hs)
    (is_stopping_time_const 𝒢 j) (λ x, (ite_le_sup _ _ _).trans (max_eq_right hij).le)
    ⟨j, λ x, le_rfl⟩,
  rwa [stopped_value_const, stopped_value_piecewise_const,
    integral_piecewise (𝒢.le _ _ hs) (hint _).integrable_on (hint _).integrable_on,
    ← integral_add_compl (𝒢.le _ _ hs) (hint j), add_le_add_iff_right] at hf,
end

/-- **The optional stopping theorem** (fair game theorem): an adapted integrable process `f`
is a submartingale if and only if for all bounded stopping times `τ` and `π` such that `τ ≤ π`, the
stopped value of `f` at `τ` has expectation smaller than its stopped value at `π`. -/
lemma submartingale_iff_expected_stopped_value_mono [is_finite_measure μ]
  (hadp : adapted 𝒢 f) (hint : ∀ i, integrable (f i) μ) :
  submartingale f 𝒢 μ ↔
  ∀ τ π : Ω → ℕ, is_stopping_time 𝒢 τ → is_stopping_time 𝒢 π → τ ≤ π → (∃ N, ∀ x, π x ≤ N) →
    μ[stopped_value f τ] ≤ μ[stopped_value f π] :=
⟨λ hf _ _ hτ hπ hle ⟨N, hN⟩, hf.expected_stopped_value_mono hτ hπ hle hN,
 submartingale_of_expected_stopped_value_mono hadp hint⟩

/-- The stopped process of a submartingale with respect to a stopping time is a submartingale. -/
@[protected]
lemma submartingale.stopped_process [is_finite_measure μ]
  (h : submartingale f 𝒢 μ) (hτ : is_stopping_time 𝒢 τ) :
  submartingale (stopped_process f τ) 𝒢 μ :=
begin
  rw submartingale_iff_expected_stopped_value_mono,
  { intros σ π hσ hπ hσ_le_π hπ_bdd,
    simp_rw stopped_value_stopped_process,
    obtain ⟨n, hπ_le_n⟩ := hπ_bdd,
    exact h.expected_stopped_value_mono (hσ.min hτ) (hπ.min hτ)
      (λ ω, min_le_min (hσ_le_π ω) le_rfl) (λ ω, (min_le_left _ _).trans (hπ_le_n ω)), },
  { exact adapted.stopped_process_of_discrete h.adapted hτ, },
  { exact λ i, h.integrable_stopped_value ((is_stopping_time_const _ i).min hτ)
    (λ ω, min_le_left _ _), },
end

section maximal

open finset

lemma smul_le_stopped_value_hitting [is_finite_measure μ]
  (hsub : submartingale f 𝒢 μ) {ε : ℝ≥0} (n : ℕ) :
  ε • μ {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_succ (λ k, f k ω)} ≤
  ennreal.of_real (∫ ω in {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_succ (λ k, f k ω)},
    stopped_value f (hitting f {y : ℝ | ↑ε ≤ y} 0 n) ω ∂μ) :=
begin
  have hn : set.Icc 0 n = {k | k ≤ n},
  { ext x, simp },
  have : ∀ ω, ((ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_succ (λ k, f k ω)) →
    (ε : ℝ) ≤ stopped_value f (hitting f {y : ℝ | ↑ε ≤ y} 0 n) ω,
  { intros x hx,
    simp_rw [le_sup'_iff, mem_range, nat.lt_succ_iff] at hx,
    refine stopped_value_hitting_mem _,
    simp only [set.mem_set_of_eq, exists_prop, hn],
    exact let ⟨j, hj₁, hj₂⟩ := hx in ⟨j, hj₁, hj₂⟩ },
  have h := set_integral_ge_of_const_le (measurable_set_le measurable_const
    (finset.measurable_range_sup'' (λ n _, (hsub.strongly_measurable n).measurable.le (𝒢.le n))))
    (measure_ne_top _ _) this
    (integrable.integrable_on (hsub.integrable_stopped_value
      (hitting_is_stopping_time hsub.adapted measurable_set_Ici) hitting_le)),
  rw [ennreal.le_of_real_iff_to_real_le, ennreal.to_real_smul],
  { exact h },
  { exact ennreal.mul_ne_top (by simp) (measure_ne_top _ _) },
  { exact le_trans (mul_nonneg ε.coe_nonneg ennreal.to_real_nonneg) h }
end

/-- **Doob's maximal inequality**: Given a non-negative submartingale `f`, for all `ε : ℝ≥0`,
we have `ε • μ {ε ≤ f* n} ≤ ∫ ω in {ε ≤ f* n}, f n` where `f* n ω = max_{k ≤ n}, f k ω`.

In some literature, the Doob's maximal inequality refers to what we call Doob's Lp inequality
(which is a corollary of this lemma and will be proved in an upcomming PR). -/
lemma maximal_ineq [is_finite_measure μ]
  (hsub : submartingale f 𝒢 μ) (hnonneg : 0 ≤ f) {ε : ℝ≥0} (n : ℕ) :
  ε • μ {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_succ (λ k, f k ω)} ≤
  ennreal.of_real (∫ ω in {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_succ (λ k, f k ω)},
    f n ω ∂μ) :=
begin
  suffices : ε • μ {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_succ (λ k, f k ω)} +
    ennreal.of_real (∫ ω in {ω | ((range (n + 1)).sup' nonempty_range_succ (λ k, f k ω)) < ε},
      f n ω ∂μ) ≤ ennreal.of_real (μ[f n]),
  { have hadd : ennreal.of_real (∫ ω, f n ω ∂μ) =
      ennreal.of_real (∫ ω in
        {ω | ↑ε ≤ ((range (n + 1)).sup' nonempty_range_succ (λ k, f k ω))}, f n ω ∂μ) +
      ennreal.of_real (∫ ω in
        {ω | ((range (n + 1)).sup' nonempty_range_succ (λ k, f k ω)) < ↑ε}, f n ω ∂μ),
    { rw [← ennreal.of_real_add, ← integral_union],
      { conv_lhs { rw ← integral_univ },
        convert rfl,
        ext ω,
        change (ε : ℝ) ≤ _ ∨ _ < (ε : ℝ) ↔ _,
        simp only [le_or_lt, true_iff] },
      { rw disjoint_iff_inf_le,
        rintro ω ⟨hω₁ : _ ≤ _, hω₂ : _ < _⟩,
        exact (not_le.2 hω₂) hω₁ },
      { exact (measurable_set_lt (finset.measurable_range_sup''
          (λ n _, (hsub.strongly_measurable n).measurable.le (𝒢.le n))) measurable_const) },
      exacts [(hsub.integrable _).integrable_on, (hsub.integrable _).integrable_on,
        integral_nonneg (hnonneg _), integral_nonneg (hnonneg _)] },
    rwa [hadd, ennreal.add_le_add_iff_right ennreal.of_real_ne_top] at this },
  calc ε • μ {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_succ (λ k, f k ω)}
    + ennreal.of_real (∫ ω in {ω | ((range (n + 1)).sup' nonempty_range_succ (λ k, f k ω)) < ε},
        f n ω ∂μ)
    ≤ ennreal.of_real (∫ ω in {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_succ (λ k, f k ω)},
        stopped_value f (hitting f {y : ℝ | ↑ε ≤ y} 0 n) ω ∂μ)
    + ennreal.of_real (∫ ω in {ω | ((range (n + 1)).sup' nonempty_range_succ (λ k, f k ω)) < ε},
        stopped_value f (hitting f {y : ℝ | ↑ε ≤ y} 0 n) ω ∂μ) :
    begin
      refine add_le_add (smul_le_stopped_value_hitting hsub _)
        (ennreal.of_real_le_of_real (set_integral_mono_on (hsub.integrable n).integrable_on
        (integrable.integrable_on (hsub.integrable_stopped_value
          (hitting_is_stopping_time hsub.adapted measurable_set_Ici) hitting_le))
        (measurable_set_lt (finset.measurable_range_sup''
          (λ n _, (hsub.strongly_measurable n).measurable.le (𝒢.le n))) measurable_const) _)),
      intros ω hω,
      rw set.mem_set_of_eq at hω,
      have : hitting f {y : ℝ | ↑ε ≤ y} 0 n ω = n,
      { simp only [hitting, set.mem_set_of_eq, exists_prop, pi.coe_nat, nat.cast_id,
          ite_eq_right_iff, forall_exists_index, and_imp],
        intros m hm hεm,
        exact false.elim ((not_le.2 hω)
          ((le_sup'_iff _).2 ⟨m, mem_range.2 (nat.lt_succ_of_le hm.2), hεm⟩)) },
      simp_rw [stopped_value, this],
    end
    ... = ennreal.of_real (∫ ω, stopped_value f (hitting f {y : ℝ | ↑ε ≤ y} 0 n) ω ∂μ) :
    begin
      rw [← ennreal.of_real_add, ← integral_union],
      { conv_rhs { rw ← integral_univ },
        convert rfl,
        ext ω,
        change _ ↔ (ε : ℝ) ≤ _ ∨ _ < (ε : ℝ),
        simp only [le_or_lt, iff_true] },
      { rw disjoint_iff_inf_le,
        rintro ω ⟨hω₁ : _ ≤ _, hω₂ : _ < _⟩,
        exact (not_le.2 hω₂) hω₁ },
      { exact (measurable_set_lt (finset.measurable_range_sup''
          (λ n _, (hsub.strongly_measurable n).measurable.le (𝒢.le n))) measurable_const) },
      { exact (integrable.integrable_on (hsub.integrable_stopped_value
          (hitting_is_stopping_time hsub.adapted measurable_set_Ici) hitting_le)) },
      { exact (integrable.integrable_on (hsub.integrable_stopped_value
          (hitting_is_stopping_time hsub.adapted measurable_set_Ici) hitting_le)) },
      exacts [integral_nonneg (λ x, hnonneg _ _), integral_nonneg (λ x, hnonneg _ _)],
    end
    ... ≤ ennreal.of_real (μ[f n]) :
    begin
      refine ennreal.of_real_le_of_real _,
      rw ← stopped_value_const f n,
      exact hsub.expected_stopped_value_mono
        (hitting_is_stopping_time hsub.adapted measurable_set_Ici)
        (is_stopping_time_const _ _) (λ ω, hitting_le ω) (λ ω, le_rfl : ∀ ω, n ≤ n),
    end
end

end maximal

end measure_theory
