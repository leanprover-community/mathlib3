/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import measure_theory.measure.probability_measure

noncomputable theory
open measure_theory
open set
open filter
open bounded_continuous_function
open_locale topological_space ennreal nnreal bounded_continuous_function

namespace measure_theory

section limsup_closed_le_and_le_liminf_open
/-! ### Portmanteau: limsup condition for closed sets iff liminf condition for open sets

In this section we prove that for a sequence of Borel probability measures on a topological space
and its candidate limit measure, the following two conditions are equivalent:
  (C) For any closed set `F` in `Ω` the limsup of the measures of `F` is at most the limit
      measure of `F`.
  (O) For any open set `G` in `Ω` the liminf of the measures of `G` is at least the limit
      measure of `G`.
Either of these will later be shown to be equivalent to the weak convergence of the sequence
of measures.
-/

variables {Ω : Type*} [measurable_space Ω]

lemma le_measure_compl_liminf_of_limsup_measure_le
  {ι : Type*} {L : filter ι} {μ : measure Ω} {μs : ι → measure Ω}
  [is_probability_measure μ] [∀ i, is_probability_measure (μs i)]
  {E : set Ω} (E_mble : measurable_set E) (h : L.limsup (λ i, μs i E) ≤ μ E) :
  μ Eᶜ ≤ L.liminf (λ i, μs i Eᶜ) :=
begin
  by_cases L_bot : L = ⊥,
  { simp only [L_bot, le_top,
      (show liminf (λ i, μs i Eᶜ) ⊥ = ⊤, by simp only [liminf, filter.map_bot, Liminf_bot])], },
  haveI : L.ne_bot, from {ne' := L_bot},
  have meas_Ec : μ Eᶜ = 1 - μ E,
  { simpa only [measure_univ] using measure_compl E_mble (measure_lt_top μ E).ne, },
  have meas_i_Ec : ∀ i, μs i Eᶜ = 1 - μs i E,
  { intro i,
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top (μs i) E).ne, },
  simp_rw [meas_Ec, meas_i_Ec],
  have obs : L.liminf (λ (i : ι), 1 - μs i E) = L.liminf ((λ x, 1 - x) ∘ (λ (i : ι), μs i E)),
    by refl,
  rw obs,
  simp_rw ← antitone_const_tsub.map_limsup_of_continuous_at (λ i, μs i E)
            (ennreal.continuous_sub_left ennreal.one_ne_top).continuous_at,
  exact antitone_const_tsub h,
end

lemma le_measure_liminf_of_limsup_measure_compl_le
  {ι : Type*} {L : filter ι} {μ : measure Ω} {μs : ι → measure Ω}
  [is_probability_measure μ] [∀ i, is_probability_measure (μs i)]
  {E : set Ω} (E_mble : measurable_set E) (h : L.limsup (λ i, μs i Eᶜ) ≤ μ Eᶜ) :
  μ E ≤ L.liminf (λ i, μs i E) :=
compl_compl E ▸ (le_measure_compl_liminf_of_limsup_measure_le (measurable_set.compl E_mble) h)

lemma limsup_measure_compl_le_of_le_liminf_measure
  {ι : Type*} {L : filter ι} {μ : measure Ω} {μs : ι → measure Ω}
  [is_probability_measure μ] [∀ i, is_probability_measure (μs i)]
  {E : set Ω} (E_mble : measurable_set E) (h : μ E ≤ L.liminf (λ i, μs i E)) :
  L.limsup (λ i, μs i Eᶜ) ≤ μ Eᶜ :=
begin
  by_cases L_bot : L = ⊥,
  { simp only [L_bot, bot_le,
      (show limsup (λ i, μs i Eᶜ) ⊥ = ⊥, by simp only [limsup, filter.map_bot, Limsup_bot])], },
  haveI : L.ne_bot, from {ne' := L_bot},
  have meas_Ec : μ Eᶜ = 1 - μ E,
  { simpa only [measure_univ] using measure_compl E_mble (measure_lt_top μ E).ne, },
  have meas_i_Ec : ∀ i, μs i Eᶜ = 1 - μs i E,
  { intro i,
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top (μs i) E).ne, },
  simp_rw [meas_Ec, meas_i_Ec],
  have obs : L.limsup (λ (i : ι), 1 - μs i E) = L.limsup ((λ x, 1 - x) ∘ (λ (i : ι), μs i E)),
    by refl,
  rw obs,
  simp_rw ← antitone_const_tsub.map_liminf_of_continuous_at (λ i, μs i E)
            (ennreal.continuous_sub_left ennreal.one_ne_top).continuous_at,
  exact antitone_const_tsub h,
end

lemma limsup_measure_le_of_le_liminf_measure_compl
  {ι : Type*} {L : filter ι} {μ : measure Ω} {μs : ι → measure Ω}
  [is_probability_measure μ] [∀ i, is_probability_measure (μs i)]
  {E : set Ω} (E_mble : measurable_set E) (h : μ Eᶜ ≤ L.liminf (λ i, μs i Eᶜ)) :
  L.limsup (λ i, μs i E) ≤ μ E :=
compl_compl E ▸ (limsup_measure_compl_le_of_le_liminf_measure (measurable_set.compl E_mble) h)

variables [topological_space Ω] [opens_measurable_space Ω]

/-- One pair of implications of the portmanteau theorem:
For a sequence of Borel probability measures, the following two are equivalent:

(C) The limsup of the measures of any closed set is at most the measure of the closed set
under a candidate limit measure.

(O) The liminf of the measures of any open set is at least the measure of the open set
under a candidate limit measure.
-/
lemma limsup_measure_closed_le_iff_liminf_measure_open_ge
  {ι : Type*} {L : filter ι} {μ : measure Ω} {μs : ι → measure Ω}
  [is_probability_measure μ] [∀ i, is_probability_measure (μs i)] :
  (∀ F, is_closed F → L.limsup (λ i, μs i F) ≤ μ F)
    ↔ (∀ G, is_open G → μ G ≤ L.liminf (λ i, μs i G)) :=
begin
  split,
  { intros h G G_open,
    exact le_measure_liminf_of_limsup_measure_compl_le
          G_open.measurable_set (h Gᶜ (is_closed_compl_iff.mpr G_open)), },
  { intros h F F_closed,
    exact limsup_measure_le_of_le_liminf_measure_compl
          F_closed.measurable_set (h Fᶜ (is_open_compl_iff.mpr F_closed)), },
end

end limsup_closed_le_and_le_liminf_open -- section

section tendsto_of_null_frontier
/-! ### Portmanteau: limit of measures of Borel sets whose boundary carries no mass in the limit

In this section we prove that for a sequence of Borel probability measures on a topological space
and its candidate limit measure, either of the following equivalent conditions:
  (C) For any closed set `F` in `Ω` the limsup of the measures of `F` is at most the limit
      measure of `F`
  (O) For any open set `G` in `Ω` the liminf of the measures of `G` is at least the limit
      measure of `G`
implies that
  (B) For any Borel set `E` in `Ω` whose boundary `∂E` carries no mass under the candidate limit
      measure, we have that the limit of measures of `E` is the measure of `E` under the
      candidate limit measure.
-/

variables {Ω : Type*} [measurable_space Ω]

lemma tendsto_measure_of_le_liminf_measure_of_limsup_measure_le
  {ι : Type*} {L : filter ι} {μ : measure Ω} {μs : ι → measure Ω}
  {E₀ E E₁ : set Ω} (E₀_subset : E₀ ⊆ E) (subset_E₁ : E ⊆ E₁) (nulldiff : μ (E₁ \ E₀) = 0)
  (h_E₀ : μ E₀ ≤ L.liminf (λ i, μs i E₀)) (h_E₁ : L.limsup (λ i, μs i E₁) ≤ μ E₁) :
  L.tendsto (λ i, μs i E) (𝓝 (μ E)) :=
begin
  apply tendsto_of_le_liminf_of_limsup_le,
  { have E₀_ae_eq_E : E₀ =ᵐ[μ] E,
      from eventually_le.antisymm E₀_subset.eventually_le
            (subset_E₁.eventually_le.trans (ae_le_set.mpr nulldiff)),
    calc  μ(E)
        = μ(E₀)                      : measure_congr E₀_ae_eq_E.symm
    ... ≤ L.liminf (λ i, μs i E₀)    : h_E₀
    ... ≤ L.liminf (λ i, μs i E)     : _,
    { refine liminf_le_liminf (eventually_of_forall (λ _, measure_mono E₀_subset)) _,
      apply_auto_param, }, },
  { have E_ae_eq_E₁ : E =ᵐ[μ] E₁,
      from eventually_le.antisymm subset_E₁.eventually_le
            ((ae_le_set.mpr nulldiff).trans E₀_subset.eventually_le),
    calc  L.limsup (λ i, μs i E)
        ≤ L.limsup (λ i, μs i E₁)    : _
    ... ≤ μ E₁                       : h_E₁
    ... = μ E                        : measure_congr E_ae_eq_E₁.symm,
    { refine limsup_le_limsup (eventually_of_forall (λ _, measure_mono subset_E₁)) _,
      apply_auto_param, }, },
end

variables [topological_space Ω] [opens_measurable_space Ω]

/-- One implication of the portmanteau theorem:
For a sequence of Borel probability measures, if the liminf of the measures of any open set is at
least the measure of the open set under a candidate limit measure, then for any set whose
boundary carries no probability mass under the candidate limit measure, then its measures under the
sequence converge to its measure under the candidate limit measure.
-/
lemma tendsto_measure_of_null_frontier
  {ι : Type*} {L : filter ι} {μ : measure Ω} {μs : ι → measure Ω}
  [is_probability_measure μ] [∀ i, is_probability_measure (μs i)]
  (h_opens : ∀ G, is_open G → μ G ≤ L.liminf (λ i, μs i G))
  {E : set Ω} (E_nullbdry : μ (frontier E) = 0) :
  L.tendsto (λ i, μs i E) (𝓝 (μ E)) :=
begin
  have h_closeds : ∀ F, is_closed F → L.limsup (λ i, μs i F) ≤ μ F,
    from limsup_measure_closed_le_iff_liminf_measure_open_ge.mpr h_opens,
  exact tendsto_measure_of_le_liminf_measure_of_limsup_measure_le
        interior_subset subset_closure E_nullbdry
        (h_opens _ is_open_interior) (h_closeds _ is_closed_closure),
end

end tendsto_of_null_frontier --section

section convergence_implies_limsup_closed_le
/-! ### Portmanteau implication: weak convergence implies a limsup condition for closed sets

In this section we prove, under the assumption that the underlying topological space `Ω` is
pseudo-emetrizable, that the weak convergence of measures on `measure_theory.finite_measure Ω`
implies that for any closed set `F` in `Ω` the limsup of the measures of `F` is at most the
limit measure of `F`. This is one implication of the portmanteau theorem characterizing weak
convergence of measures.

Combining with an earlier implication we also get that weak convergence implies that for any Borel
set `E` in `Ω` whose boundary `∂E` carries no mass under the limit measure, the limit of measures
of `E` is the measure of `E` under the limit measure.
-/

variables {Ω : Type*} [measurable_space Ω]

/-- If bounded continuous functions tend to the indicator of a measurable set and are
uniformly bounded, then their integrals against a finite measure tend to the measure of the set.
This formulation assumes:
 * the functions tend to a limit along a countably generated filter;
 * the limit is in the almost everywhere sense;
 * boundedness holds almost everywhere.
-/
lemma measure_of_cont_bdd_of_tendsto_filter_indicator {ι : Type*} {L : filter ι}
  [L.is_countably_generated] [topological_space Ω] [opens_measurable_space Ω]
  (μ : measure Ω) [is_finite_measure μ] {c : ℝ≥0} {E : set Ω} (E_mble : measurable_set E)
  (fs : ι → (Ω →ᵇ ℝ≥0)) (fs_bdd : ∀ᶠ i in L, ∀ᵐ (ω : Ω) ∂μ, fs i ω ≤ c)
  (fs_lim : ∀ᵐ (ω : Ω) ∂μ,
            tendsto (λ (i : ι), (coe_fn : (Ω →ᵇ ℝ≥0) → (Ω → ℝ≥0)) (fs i) ω) L
                    (𝓝 (indicator E (λ x, (1 : ℝ≥0)) ω))) :
  tendsto (λ n, lintegral μ (λ ω, fs n ω)) L (𝓝 (μ E)) :=
begin
  convert finite_measure.tendsto_lintegral_nn_filter_of_le_const μ fs_bdd fs_lim,
  have aux : ∀ ω, indicator E (λ ω, (1 : ℝ≥0∞)) ω = ↑(indicator E (λ ω, (1 : ℝ≥0)) ω),
  from λ ω, by simp only [ennreal.coe_indicator, ennreal.coe_one],
  simp_rw [←aux, lintegral_indicator _ E_mble],
  simp only [lintegral_one, measure.restrict_apply, measurable_set.univ, univ_inter],
end

/-- If a sequence of bounded continuous functions tends to the indicator of a measurable set and
the functions are uniformly bounded, then their integrals against a finite measure tend to the
measure of the set.

A similar result with more general assumptions is
`measure_theory.measure_of_cont_bdd_of_tendsto_filter_indicator`.
-/
lemma measure_of_cont_bdd_of_tendsto_indicator
  [topological_space Ω] [opens_measurable_space Ω]
  (μ : measure Ω) [is_finite_measure μ] {c : ℝ≥0} {E : set Ω} (E_mble : measurable_set E)
  (fs : ℕ → (Ω →ᵇ ℝ≥0)) (fs_bdd : ∀ n ω, fs n ω ≤ c)
  (fs_lim : tendsto (λ (n : ℕ), (coe_fn : (Ω →ᵇ ℝ≥0) → (Ω → ℝ≥0)) (fs n))
            at_top (𝓝 (indicator E (λ x, (1 : ℝ≥0))))) :
  tendsto (λ n, lintegral μ (λ ω, fs n ω)) at_top (𝓝 (μ E)) :=
begin
  have fs_lim' : ∀ ω, tendsto (λ (n : ℕ), (fs n ω : ℝ≥0))
                 at_top (𝓝 (indicator E (λ x, (1 : ℝ≥0)) ω)),
  by { rw tendsto_pi_nhds at fs_lim, exact λ ω, fs_lim ω, },
  apply measure_of_cont_bdd_of_tendsto_filter_indicator μ E_mble fs
      (eventually_of_forall (λ n, eventually_of_forall (fs_bdd n))) (eventually_of_forall fs_lim'),
end

/-- The integrals of thickened indicators of a closed set against a finite measure tend to the
measure of the closed set if the thickening radii tend to zero.
-/
lemma tendsto_lintegral_thickened_indicator_of_is_closed
  {Ω : Type*} [measurable_space Ω] [pseudo_emetric_space Ω] [opens_measurable_space Ω]
  (μ : measure Ω) [is_finite_measure μ] {F : set Ω} (F_closed : is_closed F) {δs : ℕ → ℝ}
  (δs_pos : ∀ n, 0 < δs n) (δs_lim : tendsto δs at_top (𝓝 0)) :
  tendsto (λ n, lintegral μ (λ ω, (thickened_indicator (δs_pos n) F ω : ℝ≥0∞)))
          at_top (𝓝 (μ F)) :=
begin
  apply measure_of_cont_bdd_of_tendsto_indicator μ F_closed.measurable_set
          (λ n, thickened_indicator (δs_pos n) F)
          (λ n ω, thickened_indicator_le_one (δs_pos n) F ω),
  have key := thickened_indicator_tendsto_indicator_closure δs_pos δs_lim F,
  rwa F_closed.closure_eq at key,
end

/-- One implication of the portmanteau theorem:
Weak convergence of finite measures implies that the limsup of the measures of any closed set is
at most the measure of the closed set under the limit measure.
-/
lemma finite_measure.limsup_measure_closed_le_of_tendsto
  {Ω ι : Type*} {L : filter ι}
  [measurable_space Ω] [pseudo_emetric_space Ω] [opens_measurable_space Ω]
  {μ : finite_measure Ω} {μs : ι → finite_measure Ω}
  (μs_lim : tendsto μs L (𝓝 μ)) {F : set Ω} (F_closed : is_closed F) :
  L.limsup (λ i, (μs i : measure Ω) F) ≤ (μ : measure Ω) F :=
begin
  by_cases L = ⊥,
  { simp only [h, limsup, filter.map_bot, Limsup_bot, ennreal.bot_eq_zero, zero_le], },
  apply ennreal.le_of_forall_pos_le_add,
  intros ε ε_pos μ_F_finite,
  set δs := λ (n : ℕ), (1 : ℝ) / (n+1) with def_δs,
  have δs_pos : ∀ n, 0 < δs n, from λ n, nat.one_div_pos_of_nat,
  have δs_lim : tendsto δs at_top (𝓝 0), from tendsto_one_div_add_at_top_nhds_0_nat,
  have key₁ := tendsto_lintegral_thickened_indicator_of_is_closed
                  (μ : measure Ω) F_closed δs_pos δs_lim,
  have room₁ : (μ : measure Ω) F < (μ : measure Ω) F + ε / 2,
  { apply ennreal.lt_add_right (measure_lt_top (μ : measure Ω) F).ne
          ((ennreal.div_pos_iff.mpr
              ⟨(ennreal.coe_pos.mpr ε_pos).ne.symm, ennreal.two_ne_top⟩).ne.symm), },
  rcases eventually_at_top.mp (eventually_lt_of_tendsto_lt room₁ key₁) with ⟨M, hM⟩,
  have key₂ := finite_measure.tendsto_iff_forall_lintegral_tendsto.mp
                μs_lim (thickened_indicator (δs_pos M) F),
  have room₂ : lintegral (μ : measure Ω) (λ a, thickened_indicator (δs_pos M) F a)
                < lintegral (μ : measure Ω) (λ a, thickened_indicator (δs_pos M) F a) + ε / 2,
  { apply ennreal.lt_add_right
          (lintegral_lt_top_of_bounded_continuous_to_nnreal (μ : measure Ω) _).ne
          ((ennreal.div_pos_iff.mpr
              ⟨(ennreal.coe_pos.mpr ε_pos).ne.symm, ennreal.two_ne_top⟩).ne.symm), },
  have ev_near := eventually.mono (eventually_lt_of_tendsto_lt room₂ key₂) (λ n, le_of_lt),
  have aux := λ n, le_trans (measure_le_lintegral_thickened_indicator
                            (μs n : measure Ω) F_closed.measurable_set (δs_pos M)),
  have ev_near' := eventually.mono ev_near aux,
  apply (filter.limsup_le_limsup ev_near').trans,
  haveI : ne_bot L, from ⟨h⟩,
  rw limsup_const,
  apply le_trans (add_le_add (hM M rfl.le).le (le_refl (ε/2 : ℝ≥0∞))),
  simp only [add_assoc, ennreal.add_halves, le_refl],
end

/-- One implication of the portmanteau theorem:
Weak convergence of probability measures implies that the limsup of the measures of any closed
set is at most the measure of the closed set under the limit probability measure.
-/
lemma probability_measure.limsup_measure_closed_le_of_tendsto
  {Ω ι : Type*} {L : filter ι}
  [measurable_space Ω] [pseudo_emetric_space Ω] [opens_measurable_space Ω]
  {μ : probability_measure Ω} {μs : ι → probability_measure Ω}
  (μs_lim : tendsto μs L (𝓝 μ)) {F : set Ω} (F_closed : is_closed F) :
  L.limsup (λ i, (μs i : measure Ω) F) ≤ (μ : measure Ω) F :=
by apply finite_measure.limsup_measure_closed_le_of_tendsto
         ((probability_measure.tendsto_nhds_iff_to_finite_measures_tendsto_nhds L).mp μs_lim)
         F_closed

/-- One implication of the portmanteau theorem:
Weak convergence of probability measures implies that the liminf of the measures of any open set
is at least the measure of the open set under the limit probability measure.
-/
lemma probability_measure.le_liminf_measure_open_of_tendsto
  {Ω ι : Type*} {L : filter ι}
  [measurable_space Ω] [pseudo_emetric_space Ω] [opens_measurable_space Ω]
  {μ : probability_measure Ω} {μs : ι → probability_measure Ω}
  (μs_lim : tendsto μs L (𝓝 μ)) {G : set Ω} (G_open : is_open G) :
  (μ : measure Ω) G ≤ L.liminf (λ i, (μs i : measure Ω) G) :=
begin
  have h_closeds : ∀ F, is_closed F → L.limsup (λ i, (μs i : measure Ω) F) ≤ (μ : measure Ω) F,
    from λ F F_closed, probability_measure.limsup_measure_closed_le_of_tendsto μs_lim F_closed,
  exact le_measure_liminf_of_limsup_measure_compl_le
        G_open.measurable_set (h_closeds _ (is_closed_compl_iff.mpr G_open)),
end

lemma probability_measure.tendsto_measure_of_null_frontier_of_tendsto'
  {Ω ι : Type*} {L : filter ι}
  [measurable_space Ω] [pseudo_emetric_space Ω] [opens_measurable_space Ω]
  {μ : probability_measure Ω} {μs : ι → probability_measure Ω}
  (μs_lim : tendsto μs L (𝓝 μ)) {E : set Ω} (E_nullbdry : (μ : measure Ω) (frontier E) = 0) :
  tendsto (λ i, (μs i : measure Ω) E) L (𝓝 ((μ : measure Ω) E)) :=
begin
  have h_opens : ∀ G, is_open G → (μ : measure Ω) G ≤ L.liminf (λ i, (μs i : measure Ω) G),
    from λ G G_open, probability_measure.le_liminf_measure_open_of_tendsto μs_lim G_open,
  exact tendsto_measure_of_null_frontier h_opens E_nullbdry,
end

/-- One implication of the portmanteau theorem:
Weak convergence of probability measures implies that if the boundary of a Borel set
carries no probability mass under the limit measure, then the limit of the measures of the set
equals the measure of the set under the limit probability measure.

A version with coercions to ordinary `ℝ≥0∞`-valued measures is
`measure_theory.probability_measure.tendsto_measure_of_null_frontier_of_tendsto'`.
-/
lemma probability_measure.tendsto_measure_of_null_frontier_of_tendsto
  {Ω ι : Type*} {L : filter ι}
  [measurable_space Ω] [pseudo_emetric_space Ω] [opens_measurable_space Ω]
  {μ : probability_measure Ω} {μs : ι → probability_measure Ω}
  (μs_lim : tendsto μs L (𝓝 μ)) {E : set Ω} (E_nullbdry : μ (frontier E) = 0) :
  tendsto (λ i, μs i E) L (𝓝 (μ E)) :=
begin
  have E_nullbdry' : (μ : measure Ω) (frontier E) = 0,
    by rw [← probability_measure.ennreal_coe_fn_eq_coe_fn_to_measure, E_nullbdry, ennreal.coe_zero],
  have key := probability_measure.tendsto_measure_of_null_frontier_of_tendsto' μs_lim E_nullbdry',
  exact (ennreal.tendsto_to_nnreal (measure_ne_top ↑μ E)).comp key,
end

end convergence_implies_limsup_closed_le --section

end measure_theory --namespace
