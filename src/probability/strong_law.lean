import probability.martingale
import probability.independence

open measure_theory filter set

localized "notation `Var[` X `]` := ∫ a, (X a) ^ 2 - (∫ a, (X a))^2" in probability_theory
localized "notation `ℙ` := volume" in probability_theory


open_locale topological_space big_operators measure_theory probability_theory


namespace probability_theory

variables {Ω : Type*} [measure_space Ω] [is_probability_measure (ℙ : measure Ω)]


theorem add_Var (X Y : Ω → ℝ) (hX : mem_ℒp X 2)

theorem
  strong_law1
  (X : ℕ → Ω → ℝ) (hint : ∀ i, integrable (X i))
  (hindep : pairwise (λ i j, indep_fun (X i) (X j)))
  (h'i : ∀ i j, measure.map (X i) ℙ = measure.map (X j) ℙ)
  (h''i : ∀ i ω, 0 ≤ X i ω) :
  ∀ᵐ ω, tendsto (λ n, (∑ i in finset.range n, X i ω) / (n : ℝ)) at_top (𝓝 (𝔼[X 0])) :=
begin
  have A : ∀ i, strongly_measurable (indicator (Icc (0 : ℝ) i) id) :=
    λ i, strongly_measurable_id.indicator measurable_set_Icc,
  let Y := λ (n : ℕ), (indicator (Icc (0 : ℝ) n) id) ∘ (X n),
  have : ∀ n, ae_strongly_measurable (Y n) ℙ :=
    λ n, (A n).ae_strongly_measurable.comp_ae_measurable (hint n).ae_measurable,
  have : pairwise (λ i j, indep_fun (Y i) (Y j) ℙ),
  { assume i j hij,
    exact (hindep i j hij).comp (A i).measurable (A j).measurable },

end

end probability_theory
