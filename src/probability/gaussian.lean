import probability.density
import probability.notation
import analysis.convex.topology

/-
Given a topological vector space `α`, a Borel measure `μ` on `α` is a Gaussian if for
all continuous linear functional `l : α → ℝ`, the push-forward measure `μ.map l` is a Gaussian on
`ℝ`.

So we first need a Gaussian on `ℝ`.
-/

open_locale nnreal ennreal probability_theory measure_theory

namespace measure_theory

noncomputable def gaussian_density (m : ℝ) : ℝ → ℝ≥0∞ :=
λ x, ennreal.of_real $ (2 * real.pi)⁻¹ * real.exp (-(x - m)^2 / 2)

def real_gaussian (μ : measure ℝ) (m : ℝ) (s : ℝ≥0∞) : Prop :=
∂μ/∂(volume : measure ℝ) = s • gaussian_density m

variables {E : Type*} [add_comm_group E] [module ℝ E] [topological_space E]
  [topological_add_group E] [has_continuous_const_smul ℝ E]

def gaussian {m0 : measurable_space E} (μ : measure E) : Prop :=
∀ l : E →L[ℝ] ℝ, ∃ m s, real_gaussian (μ.map l) m s

lemma gaussian.real_gaussian {μ : measure ℝ} (hμ : gaussian μ) : ∃ m s, real_gaussian μ m s :=
begin
  sorry
end

lemma absolutely_continuous_gaussian {μ : measure ℝ} (hμ : gaussian μ) : μ ≪ volume :=
begin
  sorry
end

end measure_theory
