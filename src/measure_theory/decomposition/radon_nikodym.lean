import measure_theory.decomposition.lebesgue

noncomputable theory
open_locale classical measure_theory nnreal ennreal

variables {α β : Type*} [measurable_space α]

namespace measure_theory

namespace measure

open vector_measure signed_measure

/-- **The Radon-Nikodym theorem**: Given two finite measures `μ` and `ν`, if `ν` is absolutely
continuous with respect to `μ`, then there exists a measurable function `f` such that
`f` is the derivative of `ν` with respect to `μ`. -/
theorem exists_with_density_of_absolute_continuous
  (μ ν : measure α) [finite_measure μ] [finite_measure ν] (h : ν ≪ μ) :
  ∃ (f : α → ℝ≥0∞) (hf : measurable f), ν = μ.with_density f :=
begin
  obtain ⟨ν₁, ν₂, _, _, hν, ⟨E, hE₁, hE₂, hE₃⟩, f, hf₁, hf₂⟩ :=
    exists_singular_with_density μ ν,
  have : ν₁ = 0,
  { apply le_antisymm,
    { intros A hA,
      suffices : ν₁ set.univ = 0,
      { rw [measure.coe_zero, pi.zero_apply, ← this],
        exact measure_mono (set.subset_univ _) },
      rw [← set.union_compl_self E, measure_union (@disjoint_compl_right _ E _) hE₁ hE₁.compl,
          hE₂, zero_add],
      have : (ν₁ + ν₂) Eᶜ = ν Eᶜ, { rw hν },
      rw [measure.coe_add, pi.add_apply, h hE₃] at this,
      exact (add_eq_zero_iff.1 this).1 },
    { exact measure.zero_le _} },
  rw [this, zero_add] at hν,
  exact ⟨f, hf₁, hν.symm ▸ hf₂⟩,
end

end measure

end measure_theory
