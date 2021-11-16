import measure_theory.measure.haar_lebesgue

/-!
-/

open measure_theory
noncomputable theory

namespace complex

instance measure_space : measure_space ℂ :=
⟨measure.map basis_one_I.equiv_fun.symm volume⟩

def measurable_equiv_pi : ℂ ≃ᵐ (fin 2 → ℝ) :=
basis_one_I.equiv_fun.to_continuous_linear_equiv.to_homeomorph.to_measurable_equiv

def measurable_equiv_real_prod : ℂ ≃ᵐ (ℝ × ℝ) :=
equiv_real_prodₗ.to_homeomorph.to_measurable_equiv

lemma volume_preserving_equiv_pi :
  measure_preserving measurable_equiv_pi :=
(measurable_equiv_pi.symm.measurable.measure_preserving _).symm

lemma volume_preserving_equiv_real_prod : measure_preserving measurable_equiv_real_prod :=
(volume_preserving_fin_two_arrow ℝ).comp volume_preserving_equiv_pi

end complex
