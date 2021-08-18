import measure_theory.decomposition.lebesgue

noncomputable theory
open_locale classical measure_theory nnreal ennreal

variables {α β : Type*} [measurable_space α]

namespace measure_theory

namespace measure

/-- **The Radon-Nikodym theorem**: Given two measures `μ` and `ν`, if
`have_lebesgue_decomposition μ ν`, then there exists a measurable function `f` such that
`f` is the derivative of `ν` with respect to `μ`. -/
theorem with_density_radon_nikodym_deriv_eq_of_finite
  (μ ν : measure α) (hl : have_lebesgue_decomposition μ ν) (h : μ ≪ ν) :
  ν.with_density (radon_nikodym_deriv μ ν) = μ :=
begin
  obtain ⟨hf₁, ⟨E, hE₁, hE₂, hE₃⟩, hadd⟩:= have_lebesgue_decomposition_spec hl,
  have : singular_part μ ν = 0,
  { apply le_antisymm,
    { intros A hA,
      suffices : singular_part μ ν set.univ = 0,
      { rw [measure.coe_zero, pi.zero_apply, ← this],
        exact measure_mono (set.subset_univ _) },
      rw [← set.union_compl_self E, measure_union (@disjoint_compl_right _ E _) hE₁ hE₁.compl,
          hE₂, zero_add],
      have : (singular_part μ ν + ν.with_density (radon_nikodym_deriv μ ν)) Eᶜ = μ Eᶜ,
      { rw ← hadd },
      rw [measure.coe_add, pi.add_apply, h hE₃] at this,
      exact (add_eq_zero_iff.1 this).1 },
    { exact measure.zero_le _} },
  rw [this, zero_add] at hadd,
  exact hadd.symm
end

end measure

end measure_theory
