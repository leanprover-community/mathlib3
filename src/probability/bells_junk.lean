import measure_theory.measure.measure_space

noncomputable theory

open measure_theory measurable_space

universe u
variables {Ω : Type u} [measurable_space Ω]

lemma meas_pm (Z : Ω → ℤˣ) :
{ω : Ω | (Z ω : ℝ) = 1} = (Z ⁻¹' {1}) :=
begin
  ext x,
  simp only [coe_coe, set.mem_set_of_eq, set.mem_preimage, set.mem_singleton_iff],
  norm_cast,
  sorry
end
